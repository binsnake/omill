#include <QApplication>
#include <QCheckBox>
#include <QCloseEvent>
#include <QComboBox>
#include <QDateTime>
#include <QDir>
#include <QFile>
#include <QFileDialog>
#include <QFileInfo>
#include <QFormLayout>
#include <QGridLayout>
#include <QGroupBox>
#include <QHBoxLayout>
#include <QLabel>
#include <QLineEdit>
#include <QListWidget>
#include <QMainWindow>
#include <QMessageBox>
#include <QPlainTextEdit>
#include <QProcess>
#include <QPushButton>
#include <QRegularExpression>
#include <QSplitter>
#include <QStatusBar>
#include <QSyntaxHighlighter>
#include <QTabWidget>
#include <QTextCharFormat>
#include <QTimer>
#include <QVBoxLayout>

#include <llvm/Support/JSON.h>
#include <llvm/Support/raw_ostream.h>

#include "omill/Tools/LiftRunContract.h"

#include <algorithm>
#include <limits>
#include <memory>
#include <optional>
#include <string>
#include <vector>

namespace {

using omill::tools::EventDetailLevel;
using omill::tools::LiftRunEvent;
using omill::tools::LiftRunRequest;
using omill::tools::LiftRunResult;

QString readTextFile(const QString &path) {
  QFile file(path);
  if (!file.open(QIODevice::ReadOnly | QIODevice::Text))
    return {};
  return QString::fromUtf8(file.readAll());
}

bool writeTextFile(const QString &path, const QString &text) {
  QFile file(path);
  if (!file.open(QIODevice::WriteOnly | QIODevice::Text))
    return false;
  file.write(text.toUtf8());
  return true;
}

QString commandPreview(const QString &program, const QStringList &args) {
  QString preview = program;
  for (const auto &arg : args) {
    if (arg.contains(' '))
      preview += " \"" + arg + "\"";
    else
      preview += " " + arg;
  }
  return preview;
}

class LlvmIrHighlighter final : public QSyntaxHighlighter {
 public:
  explicit LlvmIrHighlighter(QTextDocument *doc) : QSyntaxHighlighter(doc) {
    keyword_format_.setForeground(QColor("#1565C0"));
    keyword_format_.setFontWeight(QFont::Bold);
    type_format_.setForeground(QColor("#2E7D32"));
    symbol_format_.setForeground(QColor("#6A1B9A"));
    comment_format_.setForeground(QColor("#616161"));
    comment_format_.setFontItalic(true);
    number_format_.setForeground(QColor("#B71C1C"));

    keywords_ = {
        "define",  "declare", "target", "datalayout", "triple", "ret",
        "br",      "switch",  "call",   "invoke",     "phi",    "alloca",
        "load",    "store",   "icmp",   "fcmp",       "select", "getelementptr",
        "bitcast", "trunc",   "zext",   "sext",       "fptrunc", "fpext",
        "sitofp",  "uitofp",  "fptosi", "fptoui",     "ptrtoint", "inttoptr",
        "global",  "private", "internal", "constant", "attributes"};
  }

 protected:
  void highlightBlock(const QString &text) override {
    for (const auto &kw : keywords_) {
      const QRegularExpression rx("\\b" + QRegularExpression::escape(kw) + "\\b");
      auto it = rx.globalMatch(text);
      while (it.hasNext()) {
        const auto m = it.next();
        setFormat(m.capturedStart(), m.capturedLength(), keyword_format_);
      }
    }

    {
      const QRegularExpression rx("\\b(i[0-9]+|float|double|void|ptr)\\b");
      auto it = rx.globalMatch(text);
      while (it.hasNext()) {
        const auto m = it.next();
        setFormat(m.capturedStart(), m.capturedLength(), type_format_);
      }
    }

    {
      const QRegularExpression rx("[%@][A-Za-z0-9_.$\\\"-]+");
      auto it = rx.globalMatch(text);
      while (it.hasNext()) {
        const auto m = it.next();
        setFormat(m.capturedStart(), m.capturedLength(), symbol_format_);
      }
    }

    {
      const QRegularExpression rx("[-+]?(0x[0-9A-Fa-f]+|[0-9]+)");
      auto it = rx.globalMatch(text);
      while (it.hasNext()) {
        const auto m = it.next();
        setFormat(m.capturedStart(), m.capturedLength(), number_format_);
      }
    }

    const int comment_index = text.indexOf(';');
    if (comment_index >= 0)
      setFormat(comment_index, text.size() - comment_index, comment_format_);
  }

 private:
  QTextCharFormat keyword_format_;
  QTextCharFormat type_format_;
  QTextCharFormat symbol_format_;
  QTextCharFormat comment_format_;
  QTextCharFormat number_format_;
  QStringList keywords_;
};

class CSyntaxHighlighter final : public QSyntaxHighlighter {
 public:
  explicit CSyntaxHighlighter(QTextDocument *doc) : QSyntaxHighlighter(doc) {
    keyword_format_.setForeground(QColor("#1565C0"));
    keyword_format_.setFontWeight(QFont::Bold);
    string_format_.setForeground(QColor("#2E7D32"));
    comment_format_.setForeground(QColor("#616161"));
    comment_format_.setFontItalic(true);
    preproc_format_.setForeground(QColor("#6A1B9A"));

    keywords_ = {"int",      "char",     "short",   "long",      "float", "double",
                 "void",     "unsigned", "signed",  "struct",    "enum",  "typedef",
                 "if",       "else",     "while",   "for",       "switch", "case",
                 "default",  "break",    "continue", "return",   "static", "const",
                 "volatile", "extern",   "sizeof",  "class",     "public", "private",
                 "protected", "namespace", "template", "typename", "using", "new",
                 "delete",   "try",      "catch",   "throw",     "nullptr"};
  }

 protected:
  void highlightBlock(const QString &text) override {
    for (const auto &kw : keywords_) {
      const QRegularExpression rx("\\b" + QRegularExpression::escape(kw) + "\\b");
      auto it = rx.globalMatch(text);
      while (it.hasNext()) {
        const auto m = it.next();
        setFormat(m.capturedStart(), m.capturedLength(), keyword_format_);
      }
    }

    {
      const QRegularExpression rx("\"[^\"]*\"");
      auto it = rx.globalMatch(text);
      while (it.hasNext()) {
        const auto m = it.next();
        setFormat(m.capturedStart(), m.capturedLength(), string_format_);
      }
    }

    if (text.trimmed().startsWith("#"))
      setFormat(0, text.size(), preproc_format_);

    const int line_comment_index = text.indexOf("//");
    if (line_comment_index >= 0)
      setFormat(line_comment_index, text.size() - line_comment_index, comment_format_);
  }

 private:
  QTextCharFormat keyword_format_;
  QTextCharFormat string_format_;
  QTextCharFormat comment_format_;
  QTextCharFormat preproc_format_;
  QStringList keywords_;
};

class DiffHighlighter final : public QSyntaxHighlighter {
 public:
  explicit DiffHighlighter(QTextDocument *doc) : QSyntaxHighlighter(doc) {
    added_.setForeground(QColor("#1B5E20"));
    added_.setBackground(QColor("#E8F5E9"));
    removed_.setForeground(QColor("#B71C1C"));
    removed_.setBackground(QColor("#FFEBEE"));
    context_.setForeground(QColor("#455A64"));
  }

 protected:
  void highlightBlock(const QString &text) override {
    if (text.startsWith("+ ")) {
      setFormat(0, text.size(), added_);
    } else if (text.startsWith("- ")) {
      setFormat(0, text.size(), removed_);
    } else {
      setFormat(0, text.size(), context_);
    }
  }

 private:
  QTextCharFormat added_;
  QTextCharFormat removed_;
  QTextCharFormat context_;
};

struct QueuedRun {
  LiftRunRequest request;
  bool enabled = true;
  QString state = "queued";
  int last_exit_code = 0;
};

struct SessionRecord {
  QString id;
  LiftRunRequest request;
  LiftRunResult result;
  std::vector<LiftRunEvent> events;
  QStringList stderr_lines;
  QString status = "queued";
  QString event_path;
};

class MainWindow final : public QMainWindow {
 public:
  MainWindow() {
    setWindowTitle("omill-lift-ui");
    resize(1850, 1020);
    buildUi();
    setOptionTooltips();
    wireSignals();
    refreshQueue();
    refreshSessions();
  }
  ~MainWindow() override { shutdown(); }

 protected:
  void closeEvent(QCloseEvent *event) override {
    shutdown();
    QMainWindow::closeEvent(event);
  }

 private:
  void shutdown() {
    if (shutting_down_)
      return;
    shutting_down_ = true;

    event_poll_timer_.stop();
    event_file_.close();

    if (process_) {
      process_->disconnect(this);
      process_->blockSignals(true);
      if (process_->state() != QProcess::NotRunning) {
        process_->kill();
        process_->waitForFinished(1000);
      }
      process_.reset();
    }
  }

  QWidget *buildBrowseRow(QLineEdit *&edit, QPushButton *&button, QWidget *parent,
                          const QString &initial_text = QString()) {
    auto *container = new QWidget(parent);
    auto *layout = new QHBoxLayout(container);
    layout->setContentsMargins(0, 0, 0, 0);
    edit = new QLineEdit(container);
    edit->setText(initial_text);
    button = new QPushButton("Browse", container);
    button->setMaximumWidth(92);
    layout->addWidget(edit, 1);
    layout->addWidget(button);
    return container;
  }

  void buildUi() {
    auto *root = new QWidget(this);
    auto *root_layout = new QHBoxLayout(root);
    auto *splitter = new QSplitter(Qt::Horizontal, root);
    root_layout->addWidget(splitter);
    setCentralWidget(root);

    auto *left = new QWidget(splitter);
    auto *left_layout = new QVBoxLayout(left);

    auto *config_group = new QGroupBox("Run Configuration", left);
    auto *config_layout = new QFormLayout(config_group);

    config_layout->addRow("Binary", buildBrowseRow(binary_edit_, browse_binary_btn_, config_group,
                                                    "omill-lift"));
    config_layout->addRow("Input file", buildBrowseRow(input_edit_, browse_input_btn_, config_group));
    va_edit_ = new QLineEdit(config_group);
    base_edit_ = new QLineEdit("0", config_group);
    config_layout->addRow("--va", va_edit_);
    config_layout->addRow("--base", base_edit_);
    config_layout->addRow("-o", buildBrowseRow(output_edit_, browse_output_btn_, config_group, "-"));

    vm_entry_edit_ = new QLineEdit(config_group);
    vm_exit_edit_ = new QLineEdit(config_group);
    trace_func_edit_ = new QLineEdit(config_group);
    scan_section_edit_ = new QLineEdit(config_group);
    scan_output_edit_ = new QLineEdit("-", config_group);
    config_layout->addRow("--vm-entry", vm_entry_edit_);
    config_layout->addRow("--vm-exit", vm_exit_edit_);
    config_layout->addRow("--trace-func", trace_func_edit_);
    config_layout->addRow("--scan-section", scan_section_edit_);
    config_layout->addRow("--scan-output", scan_output_edit_);
    config_layout->addRow("--deobf-targets",
                          buildBrowseRow(deobf_targets_edit_, browse_deobf_targets_btn_, config_group));

    deobf_section_edit_ = new QLineEdit(config_group);
    min_func_size_edit_ = new QLineEdit("64", config_group);
    max_iterations_edit_ = new QLineEdit("10", config_group);
    config_layout->addRow("--deobf-section", deobf_section_edit_);
    config_layout->addRow("--min-func-size", min_func_size_edit_);
    config_layout->addRow("--max-iterations", max_iterations_edit_);

    config_layout->addRow("--event-jsonl",
                          buildBrowseRow(event_jsonl_edit_, browse_event_jsonl_btn_, config_group));
    event_detail_combo_ = new QComboBox(config_group);
    event_detail_combo_->addItem("basic");
    event_detail_combo_->addItem("detailed");
    config_layout->addRow("--event-detail", event_detail_combo_);

    auto *flag_group = new QGroupBox("Flags (CLI parity)", left);
    auto *flag_layout = new QGridLayout(flag_group);
    raw_cb_ = new QCheckBox("--raw", flag_group);
    no_abi_cb_ = new QCheckBox("--no-abi", flag_group);
    deobf_cb_ = new QCheckBox("--deobfuscate", flag_group);
    resolve_targets_cb_ = new QCheckBox("--resolve-targets", flag_group);
    ipcp_cb_ = new QCheckBox("--ipcp", flag_group);
    resolve_exceptions_cb_ = new QCheckBox("--resolve-exceptions", flag_group);
    block_lift_cb_ = new QCheckBox("--block-lift", flag_group);
    dump_ir_cb_ = new QCheckBox("--dump-ir", flag_group);
    omill_time_cb_ = new QCheckBox("--omill-time-passes", flag_group);
    verify_each_cb_ = new QCheckBox("--verify-each", flag_group);
    dump_func_phases_cb_ = new QCheckBox("--dump-func-phases", flag_group);
    scan_all_cb_ = new QCheckBox("--scan-all", flag_group);

    flag_layout->addWidget(raw_cb_, 0, 0);
    flag_layout->addWidget(no_abi_cb_, 0, 1);
    flag_layout->addWidget(deobf_cb_, 1, 0);
    flag_layout->addWidget(resolve_targets_cb_, 1, 1);
    flag_layout->addWidget(ipcp_cb_, 2, 1);
    flag_layout->addWidget(resolve_exceptions_cb_, 3, 0);
    flag_layout->addWidget(block_lift_cb_, 3, 1);
    flag_layout->addWidget(dump_ir_cb_, 4, 0);
    flag_layout->addWidget(omill_time_cb_, 4, 1);
    flag_layout->addWidget(verify_each_cb_, 5, 0);
    flag_layout->addWidget(dump_func_phases_cb_, 5, 1);
    flag_layout->addWidget(scan_all_cb_, 6, 0);

    auto *queue_group = new QGroupBox("Run Queue", left);
    auto *queue_layout = new QVBoxLayout(queue_group);
    queue_list_ = new QListWidget(queue_group);
    queue_layout->addWidget(queue_list_);

    auto *queue_btn_row1 = new QHBoxLayout();
    add_queue_btn_ = new QPushButton("Add Current", queue_group);
    start_btn_ = new QPushButton("Start", queue_group);
    cancel_btn_ = new QPushButton("Cancel", queue_group);
    queue_btn_row1->addWidget(add_queue_btn_);
    queue_btn_row1->addWidget(start_btn_);
    queue_btn_row1->addWidget(cancel_btn_);
    queue_layout->addLayout(queue_btn_row1);

    auto *queue_btn_row2 = new QHBoxLayout();
    retry_btn_ = new QPushButton("Retry", queue_group);
    duplicate_btn_ = new QPushButton("Duplicate", queue_group);
    toggle_btn_ = new QPushButton("Enable/Disable", queue_group);
    up_btn_ = new QPushButton("Move Up", queue_group);
    down_btn_ = new QPushButton("Move Down", queue_group);
    queue_btn_row2->addWidget(retry_btn_);
    queue_btn_row2->addWidget(duplicate_btn_);
    queue_btn_row2->addWidget(toggle_btn_);
    queue_btn_row2->addWidget(up_btn_);
    queue_btn_row2->addWidget(down_btn_);
    queue_layout->addLayout(queue_btn_row2);

    left_layout->addWidget(config_group);
    left_layout->addWidget(flag_group);
    left_layout->addWidget(queue_group, 1);

    auto *right = new QWidget(splitter);
    auto *right_layout = new QVBoxLayout(right);
    right_tabs_ = new QTabWidget(right);

    auto *overview_tab = new QWidget(right_tabs_);
    auto *overview_layout = new QVBoxLayout(overview_tab);

    auto *sessions_group = new QGroupBox("Session History", overview_tab);
    auto *sessions_layout = new QVBoxLayout(sessions_group);
    session_list_ = new QListWidget(sessions_group);
    sessions_layout->addWidget(session_list_);
    export_btn_ = new QPushButton("Export Selected Session JSON", sessions_group);
    sessions_layout->addWidget(export_btn_);

    auto *timeline_group = new QGroupBox("Phase Timeline / Events", overview_tab);
    auto *timeline_layout = new QVBoxLayout(timeline_group);
    event_list_ = new QListWidget(timeline_group);
    timeline_layout->addWidget(event_list_);

    auto *logs_group = new QGroupBox("Logs + Artifacts", overview_tab);
    auto *logs_layout = new QHBoxLayout(logs_group);
    stderr_list_ = new QListWidget(logs_group);

    auto *artifact_panel = new QWidget(logs_group);
    auto *artifact_layout = new QVBoxLayout(artifact_panel);
    artifacts_list_ = new QListWidget(artifact_panel);
    open_artifact_btn_ = new QPushButton("Load .ll Artifact", artifact_panel);
    artifact_layout->addWidget(artifacts_list_, 1);
    artifact_layout->addWidget(open_artifact_btn_);

    logs_layout->addWidget(stderr_list_, 2);
    logs_layout->addWidget(artifact_panel, 1);

    overview_layout->addWidget(sessions_group, 1);
    overview_layout->addWidget(timeline_group, 2);
    overview_layout->addWidget(logs_group, 2);

    auto *analysis_tab = new QWidget(right_tabs_);
    auto *analysis_layout = new QVBoxLayout(analysis_tab);

    auto *analysis_controls = new QGroupBox("Lifted IR Analysis", analysis_tab);
    auto *analysis_controls_layout = new QGridLayout(analysis_controls);

    current_ir_path_edit_ = new QLineEdit(analysis_controls);
    current_ir_path_edit_->setReadOnly(true);
    load_ir_btn_ = new QPushButton("Load IR File", analysis_controls);

    function_combo_ = new QComboBox(analysis_controls);
    function_combo_->addItem("<module>");

    pass_combo_ = new QComboBox(analysis_controls);
    pass_combo_->addItem("Simplify CFG", "simplifycfg");
    pass_combo_->addItem("InstCombine + CFG", "instcombine,simplifycfg");
    pass_combo_->addItem("SROA + Mem2Reg + InstCombine", "sroa,mem2reg,instcombine,simplifycfg");
    pass_combo_->addItem("Reassociate + GVN + DCE", "reassociate,gvn,dce");
    pass_combo_->addItem("ADCE", "adce");

    opt_binary_edit_ = new QLineEdit("opt", analysis_controls);
    apply_pass_btn_ = new QPushButton("Apply Passes", analysis_controls);
    reset_ir_btn_ = new QPushButton("Reset To Original", analysis_controls);

    analysis_controls_layout->addWidget(new QLabel("IR path", analysis_controls), 0, 0);
    analysis_controls_layout->addWidget(current_ir_path_edit_, 0, 1, 1, 3);
    analysis_controls_layout->addWidget(load_ir_btn_, 0, 4);

    analysis_controls_layout->addWidget(new QLabel("Function", analysis_controls), 1, 0);
    analysis_controls_layout->addWidget(function_combo_, 1, 1);
    analysis_controls_layout->addWidget(new QLabel("Pipeline", analysis_controls), 1, 2);
    analysis_controls_layout->addWidget(pass_combo_, 1, 3);

    analysis_controls_layout->addWidget(new QLabel("opt binary", analysis_controls), 2, 0);
    analysis_controls_layout->addWidget(opt_binary_edit_, 2, 1);
    analysis_controls_layout->addWidget(apply_pass_btn_, 2, 3);
    analysis_controls_layout->addWidget(reset_ir_btn_, 2, 4);

    auto *analysis_splitter = new QSplitter(Qt::Horizontal, analysis_tab);

    auto *before_group = new QGroupBox("Original", analysis_splitter);
    auto *before_layout = new QVBoxLayout(before_group);
    ir_before_view_ = new QPlainTextEdit(before_group);
    ir_before_view_->setReadOnly(true);
    before_layout->addWidget(ir_before_view_);

    auto *after_group = new QGroupBox("After Passes", analysis_splitter);
    auto *after_layout = new QVBoxLayout(after_group);
    ir_after_view_ = new QPlainTextEdit(after_group);
    ir_after_view_->setReadOnly(true);
    after_layout->addWidget(ir_after_view_);

    auto *diff_group = new QGroupBox("Diff", analysis_splitter);
    auto *diff_layout = new QVBoxLayout(diff_group);
    ir_diff_view_ = new QPlainTextEdit(diff_group);
    ir_diff_view_->setReadOnly(true);
    diff_layout->addWidget(ir_diff_view_);

    analysis_splitter->setStretchFactor(0, 1);
    analysis_splitter->setStretchFactor(1, 1);
    analysis_splitter->setStretchFactor(2, 1);

    analysis_layout->addWidget(analysis_controls);
    analysis_layout->addWidget(analysis_splitter, 1);

    auto *plan_tab = new QWidget(right_tabs_);
    auto *plan_layout = new QVBoxLayout(plan_tab);

    auto *tooling_group = new QGroupBox("Compile + IDA CLI Decompile Plan", plan_tab);
    auto *tooling_layout = new QGridLayout(tooling_group);

    clang_binary_edit_ = new QLineEdit("clang", tooling_group);
    compile_output_edit_ = new QLineEdit(QDir::tempPath() + "/omill-lift-ui-out.exe", tooling_group);
    ida_binary_edit_ = new QLineEdit("idat64", tooling_group);
    ida_script_edit_ = new QLineEdit(tooling_group);
    decompile_output_edit_ = new QLineEdit(QDir::tempPath() + "/omill-lift-ui-out.c", tooling_group);

    browse_compile_output_btn_ = new QPushButton("Browse", tooling_group);
    browse_ida_script_btn_ = new QPushButton("Browse", tooling_group);
    browse_decompile_output_btn_ = new QPushButton("Browse", tooling_group);

    tooling_layout->addWidget(new QLabel("clang", tooling_group), 0, 0);
    tooling_layout->addWidget(clang_binary_edit_, 0, 1, 1, 3);
    tooling_layout->addWidget(new QLabel("Compile output", tooling_group), 1, 0);
    tooling_layout->addWidget(compile_output_edit_, 1, 1, 1, 2);
    tooling_layout->addWidget(browse_compile_output_btn_, 1, 3);
    tooling_layout->addWidget(new QLabel("IDA CLI", tooling_group), 2, 0);
    tooling_layout->addWidget(ida_binary_edit_, 2, 1, 1, 3);
    tooling_layout->addWidget(new QLabel("IDA script", tooling_group), 3, 0);
    tooling_layout->addWidget(ida_script_edit_, 3, 1, 1, 2);
    tooling_layout->addWidget(browse_ida_script_btn_, 3, 3);
    tooling_layout->addWidget(new QLabel("Decompile output", tooling_group), 4, 0);
    tooling_layout->addWidget(decompile_output_edit_, 4, 1, 1, 2);
    tooling_layout->addWidget(browse_decompile_output_btn_, 4, 3);

    auto *plan_btn_row = new QHBoxLayout();
    plan_btn_ = new QPushButton("Plan Steps", tooling_group);
    compile_btn_ = new QPushButton("Run Compile", tooling_group);
    decompile_btn_ = new QPushButton("Run IDA Decompile", tooling_group);
    plan_btn_row->addWidget(plan_btn_);
    plan_btn_row->addWidget(compile_btn_);
    plan_btn_row->addWidget(decompile_btn_);
    tooling_layout->addLayout(plan_btn_row, 5, 0, 1, 4);

    plan_list_ = new QListWidget(plan_tab);

    auto *plan_splitter = new QSplitter(Qt::Horizontal, plan_tab);
    auto *log_group = new QGroupBox("Tool Log", plan_splitter);
    auto *log_layout = new QVBoxLayout(log_group);
    compile_log_view_ = new QPlainTextEdit(log_group);
    compile_log_view_->setReadOnly(true);
    log_layout->addWidget(compile_log_view_);

    auto *decomp_group = new QGroupBox("Decompiled View", plan_splitter);
    auto *decomp_layout = new QVBoxLayout(decomp_group);
    decompile_view_ = new QPlainTextEdit(decomp_group);
    decompile_view_->setReadOnly(true);
    decomp_layout->addWidget(decompile_view_);

    plan_splitter->setStretchFactor(0, 1);
    plan_splitter->setStretchFactor(1, 1);

    plan_layout->addWidget(tooling_group);
    plan_layout->addWidget(new QLabel("Planned Steps", plan_tab));
    plan_layout->addWidget(plan_list_);
    plan_layout->addWidget(plan_splitter, 1);

    right_tabs_->addTab(overview_tab, "Overview");
    right_tabs_->addTab(analysis_tab, "Artifacts & Analysis");
    right_tabs_->addTab(plan_tab, "Compile/Decompile Plan");

    right_layout->addWidget(right_tabs_);

    splitter->addWidget(left);
    splitter->addWidget(right);
    splitter->setStretchFactor(0, 2);
    splitter->setStretchFactor(1, 4);

    new LlvmIrHighlighter(ir_before_view_->document());
    new LlvmIrHighlighter(ir_after_view_->document());
    new DiffHighlighter(ir_diff_view_->document());
    new CSyntaxHighlighter(decompile_view_->document());

    statusBar()->showMessage("Idle");
    cancel_btn_->setEnabled(false);
  }

  void setOptionTooltips() {
    binary_edit_->setToolTip("Path to the omill-lift CLI binary that will be launched for runs.");
    browse_binary_btn_->setToolTip("Select the omill-lift executable using the native file picker.");
    input_edit_->setToolTip("Input binary/raw file to lift.");
    browse_input_btn_->setToolTip("Pick an input file with native Windows Explorer dialog.");
    va_edit_->setToolTip("Entry virtual address to lift (hex, e.g. 0x140001000).");
    base_edit_->setToolTip("Image base for raw inputs (hex or decimal).");
    output_edit_->setToolTip("Lifted LLVM IR output path (use - for stdout).");
    browse_output_btn_->setToolTip("Choose output .ll path.");
    vm_entry_edit_->setToolTip("VM entry address for VM mode.");
    vm_exit_edit_->setToolTip("Optional VM exit address.");
    trace_func_edit_->setToolTip("Restrict tracing/phase dumps to one function symbol or VA.");
    scan_section_edit_->setToolTip("Section name to scan for candidates.");
    scan_output_edit_->setToolTip("Output for scan results.");
    deobf_targets_edit_->setToolTip("Path to target list JSON used by deobfuscation batch mode.");
    browse_deobf_targets_btn_->setToolTip("Choose deobf targets JSON.");
    deobf_section_edit_->setToolTip("Section to prioritize for deobfuscation target collection.");
    min_func_size_edit_->setToolTip("Minimum function size threshold for discovery.");
    max_iterations_edit_->setToolTip("Max fixed-point iterations for iterative passes.");
    event_jsonl_edit_->setToolTip("JSONL event stream path (leave empty for auto temp file).");
    browse_event_jsonl_btn_->setToolTip("Choose event stream output path.");
    event_detail_combo_->setToolTip("basic: coarse milestones, detailed: finer-grain progress events.");

    raw_cb_->setToolTip("Treat input as raw bytes (no PE/ELF loader parsing).");
    no_abi_cb_->setToolTip("Disable ABI recovery stage.");
    deobf_cb_->setToolTip("Enable deobfuscation pipeline passes.");
    resolve_targets_cb_->setToolTip("Enable iterative target resolution.");
    ipcp_cb_->setToolTip("Enable interprocedural constant propagation.");
    resolve_exceptions_cb_->setToolTip("Resolve forced exception dispatch constructs.");
    block_lift_cb_->setToolTip("Prefer block-level lifting mode.");
    dump_ir_cb_->setToolTip("Emit intermediate IR snapshots.");
    omill_time_cb_->setToolTip("Enable per-pass timing output.");
    verify_each_cb_->setToolTip("Run verifier after each major stage.");
    dump_func_phases_cb_->setToolTip("Dump per-function phase outputs.");
    scan_all_cb_->setToolTip("Scan all sections for candidate functions.");

    load_ir_btn_->setToolTip("Load LLVM IR file for function-level review and pass experimentation.");
    function_combo_->setToolTip("Select function scope for focused before/after view.");
    pass_combo_->setToolTip("New-PM pass pipeline to apply via opt.");
    opt_binary_edit_->setToolTip("Path or name of opt executable used for pass application.");
    apply_pass_btn_->setToolTip("Apply selected pass pipeline to currently loaded IR and show diff.");
    reset_ir_btn_->setToolTip("Discard transformed text and return to original loaded IR.");

    clang_binary_edit_->setToolTip("clang executable used to compile IR into a binary.");
    compile_output_edit_->setToolTip("Binary output path for compile stage.");
    ida_binary_edit_->setToolTip("IDA CLI executable (e.g. idat64.exe).");
    ida_script_edit_->setToolTip("IDA Python script invoked in batch mode for decompile export.");
    decompile_output_edit_->setToolTip("Path where decompile script should emit C/pseudocode.");
    plan_btn_->setToolTip("Preview compile + decompile commands before execution.");
    compile_btn_->setToolTip("Compile currently loaded IR using clang.");
    decompile_btn_->setToolTip("Run IDA in batch mode and load exported decompilation output.");
  }

  void wireSignals() {
    connect(add_queue_btn_, &QPushButton::clicked, this, [this] { addCurrentToQueue(); });
    connect(start_btn_, &QPushButton::clicked, this, [this] { startSelectedOrNext(); });
    connect(cancel_btn_, &QPushButton::clicked, this, [this] { cancelActive(); });
    connect(retry_btn_, &QPushButton::clicked, this, [this] { retrySelected(); });
    connect(duplicate_btn_, &QPushButton::clicked, this, [this] { duplicateSelected(); });
    connect(toggle_btn_, &QPushButton::clicked, this, [this] { toggleSelectedQueue(); });
    connect(up_btn_, &QPushButton::clicked, this, [this] { moveQueue(-1); });
    connect(down_btn_, &QPushButton::clicked, this, [this] { moveQueue(1); });
    connect(export_btn_, &QPushButton::clicked, this, [this] { exportSelectedSession(); });
    connect(session_list_, &QListWidget::currentRowChanged, this,
            [this](int row) { showSession(row); });

    connect(browse_binary_btn_, &QPushButton::clicked, this, [this] {
      chooseOpenFileFor(binary_edit_, "Select omill-lift Binary", "Executables (*.exe);;All files (*.*)");
    });
    connect(browse_input_btn_, &QPushButton::clicked, this, [this] {
      chooseOpenFileFor(input_edit_, "Select Input File", "All files (*.*)");
    });
    connect(browse_output_btn_, &QPushButton::clicked, this, [this] {
      chooseSaveFileFor(output_edit_, "Select Lift Output", "LLVM IR (*.ll);;All files (*.*)");
    });
    connect(browse_deobf_targets_btn_, &QPushButton::clicked, this, [this] {
      chooseOpenFileFor(deobf_targets_edit_, "Select Deobf Targets", "JSON (*.json);;All files (*.*)");
    });
    connect(browse_event_jsonl_btn_, &QPushButton::clicked, this, [this] {
      chooseSaveFileFor(event_jsonl_edit_, "Select Event JSONL", "JSONL (*.jsonl);;All files (*.*)");
    });

    connect(load_ir_btn_, &QPushButton::clicked, this, [this] {
      QString path;
      chooseOpenFile(path, "Load LLVM IR", "LLVM IR (*.ll *.bc);;All files (*.*)");
      if (!path.isEmpty())
        loadIrFromPath(path);
    });
    connect(open_artifact_btn_, &QPushButton::clicked, this, [this] { loadSelectedArtifactIfLl(); });
    connect(artifacts_list_, &QListWidget::itemDoubleClicked, this,
            [this](QListWidgetItem *) { loadSelectedArtifactIfLl(); });
    connect(function_combo_, &QComboBox::currentTextChanged, this,
            [this](const QString &) { refreshFunctionViews(); });
    connect(apply_pass_btn_, &QPushButton::clicked, this, [this] { applySelectedPassPipeline(); });
    connect(reset_ir_btn_, &QPushButton::clicked, this, [this] { resetTransformedIr(); });

    connect(plan_btn_, &QPushButton::clicked, this, [this] { planCompileAndDecompile(); });
    connect(compile_btn_, &QPushButton::clicked, this, [this] { runCompileStep(); });
    connect(decompile_btn_, &QPushButton::clicked, this, [this] { runIdaDecompileStep(); });

    connect(browse_compile_output_btn_, &QPushButton::clicked, this, [this] {
      chooseSaveFileFor(compile_output_edit_, "Compile Output", "Executables (*.exe);;All files (*.*)");
    });
    connect(browse_ida_script_btn_, &QPushButton::clicked, this, [this] {
      chooseOpenFileFor(ida_script_edit_, "IDA Script", "Python (*.py);;All files (*.*)");
    });
    connect(browse_decompile_output_btn_, &QPushButton::clicked, this, [this] {
      chooseSaveFileFor(decompile_output_edit_, "Decompile Output", "C/C++ (*.c *.cpp *.h);;All files (*.*)");
    });

    event_poll_timer_.setInterval(150);
    connect(&event_poll_timer_, &QTimer::timeout, this, [this] { pollEventFile(); });
  }

  void chooseOpenFile(QString &dst, const QString &title, const QString &filter) {
    const QString path = QFileDialog::getOpenFileName(this, title, dst, filter);
    if (!path.isEmpty())
      dst = path;
  }

  void chooseOpenFileFor(QLineEdit *edit, const QString &title, const QString &filter) {
    QString value = edit->text();
    chooseOpenFile(value, title, filter);
    if (!value.isEmpty())
      edit->setText(value);
  }

  void chooseSaveFileFor(QLineEdit *edit, const QString &title, const QString &filter) {
    const QString path = QFileDialog::getSaveFileName(this, title, edit->text(), filter);
    if (!path.isEmpty())
      edit->setText(path);
  }

  static std::optional<unsigned> parseUInt(const QString &text) {
    bool ok = false;
    const auto trimmed = text.trimmed();
    if (trimmed.isEmpty())
      return std::nullopt;
    quint64 value = trimmed.toULongLong(&ok, 0);
    if (!ok || value > static_cast<quint64>(std::numeric_limits<unsigned>::max()))
      return std::nullopt;
    return static_cast<unsigned>(value);
  }

  static std::optional<uint64_t> parseU64(const QString &text) {
    bool ok = false;
    const auto trimmed = text.trimmed();
    if (trimmed.isEmpty())
      return std::nullopt;
    quint64 value = trimmed.toULongLong(&ok, 0);
    if (!ok)
      return std::nullopt;
    return static_cast<uint64_t>(value);
  }

  LiftRunRequest buildRequestFromUi() const {
    LiftRunRequest request;
    request.input_filename = input_edit_->text().toStdString();
    request.va = va_edit_->text().toStdString();
    request.raw = raw_cb_->isChecked();
    if (auto base = parseU64(base_edit_->text()); base)
      request.base = *base;
    request.output_filename = output_edit_->text().toStdString();
    request.no_abi = no_abi_cb_->isChecked();
    request.deobfuscate = deobf_cb_->isChecked();
    request.resolve_targets = resolve_targets_cb_->isChecked();
    if (auto mi = parseUInt(max_iterations_edit_->text()); mi)
      request.max_iterations = *mi;
    request.ipcp = ipcp_cb_->isChecked();
    request.resolve_exceptions = resolve_exceptions_cb_->isChecked();
    request.block_lift = block_lift_cb_->isChecked();
    request.dump_ir = dump_ir_cb_->isChecked();
    request.vm_entry = vm_entry_edit_->text().toStdString();
    request.vm_exit = vm_exit_edit_->text().toStdString();
    request.omill_time_passes = omill_time_cb_->isChecked();
    request.verify_each = verify_each_cb_->isChecked();
    request.trace_func = trace_func_edit_->text().toStdString();
    request.dump_func_phases = dump_func_phases_cb_->isChecked();
    request.scan_section = scan_section_edit_->text().toStdString();
    request.scan_output = scan_output_edit_->text().toStdString();
    request.scan_all = scan_all_cb_->isChecked();
    request.deobf_targets = deobf_targets_edit_->text().toStdString();
    request.deobf_section = deobf_section_edit_->text().toStdString();
    if (auto mfs = parseUInt(min_func_size_edit_->text()); mfs)
      request.min_func_size = *mfs;
    request.event_jsonl = event_jsonl_edit_->text().toStdString();
    request.event_detail = (event_detail_combo_->currentText() == "detailed")
                               ? EventDetailLevel::kDetailed
                               : EventDetailLevel::kBasic;
    return request;
  }

  QString runLabel(const QueuedRun &run) const {
    const QString in = QString::fromStdString(run.request.input_filename);
    const QString va = QString::fromStdString(run.request.va);
    const QString mode = run.enabled ? "EN" : "DIS";
    return QString("[%1] %2 (%3) %4")
        .arg(mode, in.isEmpty() ? "<no-input>" : in,
             va.isEmpty() ? "no-va" : va, run.state);
  }

  QString sessionLabel(const SessionRecord &session) const {
    const QString in = QString::fromStdString(session.request.input_filename);
    return QString("%1 | %2 | %3")
        .arg(session.id, session.status, in.isEmpty() ? "<no-input>" : in);
  }

  static void pushUniqueString(std::vector<std::string> &items, const std::string &value) {
    if (value.empty())
      return;
    if (std::find(items.begin(), items.end(), value) == items.end())
      items.push_back(value);
  }

  void refreshQueue() {
    queue_list_->clear();
    for (const auto &run : queue_)
      queue_list_->addItem(runLabel(run));
  }

  void refreshSessions() {
    session_list_->clear();
    for (const auto &session : sessions_)
      session_list_->addItem(sessionLabel(session));
  }

  void addCurrentToQueue() {
    QueuedRun run;
    run.request = buildRequestFromUi();
    queue_.push_back(run);
    refreshQueue();
    queue_list_->setCurrentRow(static_cast<int>(queue_.size()) - 1);
  }

  int selectedQueueIndex() const {
    const int row = queue_list_->currentRow();
    if (row >= 0 && row < static_cast<int>(queue_.size()))
      return row;
    return -1;
  }

  int selectedSessionIndex() const {
    const int row = session_list_->currentRow();
    if (row >= 0 && row < static_cast<int>(sessions_.size()))
      return row;
    return -1;
  }

  void startSelectedOrNext() {
    if (process_)
      return;
    int idx = selectedQueueIndex();
    if (idx < 0 || !queue_[idx].enabled || queue_[idx].state != "queued") {
      idx = -1;
      for (int i = 0; i < static_cast<int>(queue_.size()); ++i) {
        if (queue_[i].enabled && queue_[i].state == "queued") {
          idx = i;
          break;
        }
      }
    }
    if (idx < 0) {
      statusBar()->showMessage("No queued run available");
      return;
    }
    startQueueIndex(idx);
  }

  void startQueueIndex(int idx) {
    if (idx < 0 || idx >= static_cast<int>(queue_.size()))
      return;

    auto request = queue_[idx].request;
    if (request.input_filename.empty()) {
      QMessageBox::warning(this, "Invalid Run", "Input file is required.");
      return;
    }

    if (request.event_jsonl.empty() || request.event_jsonl == "-") {
      const QString auto_event_path =
          QDir::tempPath() + "/omill-lift-" +
          QDateTime::currentDateTimeUtc().toString("yyyyMMddhhmmsszzz") +
          "-" + QString::number(sessions_.size()) + ".jsonl";
      request.event_jsonl = auto_event_path.toStdString();
    }

    SessionRecord session;
    session.id = QDateTime::currentDateTimeUtc().toString(Qt::ISODateWithMs);
    session.request = request;
    session.status = "running";
    session.event_path = QString::fromStdString(request.event_jsonl);
    sessions_.push_back(session);
    active_session_index_ = static_cast<int>(sessions_.size()) - 1;
    active_queue_index_ = idx;
    queue_[idx].state = "running";
    refreshQueue();
    refreshSessions();
    session_list_->setCurrentRow(active_session_index_);

    event_file_.close();
    event_file_.setFileName(session.event_path);
    event_file_offset_ = 0;

    const QString selected_binary = binary_edit_->text().trimmed().isEmpty()
                                        ? "omill-lift"
                                        : binary_edit_->text().trimmed();
    omill::tools::SubprocessExecutor executor(selected_binary.toStdString());
    const auto invocation = executor.buildInvocation(request);
    if (invocation.empty()) {
      QMessageBox::warning(this, "Invalid Invocation",
                           "Could not build omill-lift invocation.");
      return;
    }

    process_ = std::make_unique<QProcess>(this);
    process_->setProcessChannelMode(QProcess::SeparateChannels);
    connect(process_.get(), &QProcess::readyReadStandardError, this, [this] {
      if (active_session_index_ < 0 || active_session_index_ >= static_cast<int>(sessions_.size()))
        return;
      const QByteArray data = process_->readAllStandardError();
      const QString text = QString::fromUtf8(data);
      for (const auto &line : text.split('\n', Qt::SkipEmptyParts))
        sessions_[active_session_index_].stderr_lines.push_back(line);
      if (session_list_->currentRow() == active_session_index_)
        showSession(active_session_index_);
    });
    connect(process_.get(),
            QOverload<int, QProcess::ExitStatus>::of(&QProcess::finished),
            this, [this](int code, QProcess::ExitStatus status) {
              finalizeRun(code, status == QProcess::NormalExit);
            });
    connect(process_.get(), &QProcess::errorOccurred, this,
            [this](QProcess::ProcessError err) {
              if (err == QProcess::FailedToStart) {
                if (active_session_index_ >= 0 &&
                    active_session_index_ < static_cast<int>(sessions_.size())) {
                  sessions_[active_session_index_].stderr_lines.push_back(
                      "Failed to start omill-lift subprocess");
                }
                finalizeRun(127, false);
              }
            });

    QStringList qargs;
    for (size_t i = 1; i < invocation.size(); ++i)
      qargs.push_back(QString::fromStdString(invocation[i]));

    const QString program = QString::fromStdString(invocation.front());
    process_->start(program, qargs);
    statusBar()->showMessage("Running: " + program + " " + qargs.join(' '));
    cancel_btn_->setEnabled(true);
    event_poll_timer_.start();
  }

  void finalizeRun(int exit_code, bool normal_exit) {
    if (!process_)
      return;
    pollEventFile();
    if (active_session_index_ >= 0 && active_session_index_ < static_cast<int>(sessions_.size())) {
      auto &session = sessions_[active_session_index_];
      session.result.exit_code = exit_code;
      session.status = (normal_exit && exit_code == 0) ? "success" : "failed";
      if (exit_code != 0)
        session.result.errors.push_back("Process exited with code " + std::to_string(exit_code));

      if (!session.request.output_filename.empty() &&
          session.request.output_filename != "-") {
        pushUniqueString(session.result.artifacts, session.request.output_filename);
      }

      loadFirstLlArtifactFromSession(session);
    }

    if (active_queue_index_ >= 0 && active_queue_index_ < static_cast<int>(queue_.size())) {
      auto &run = queue_[active_queue_index_];
      run.state = (exit_code == 0) ? "success" : "failed";
      run.last_exit_code = exit_code;
    }

    process_.reset();
    event_poll_timer_.stop();
    event_file_.close();
    cancel_btn_->setEnabled(false);
    refreshQueue();
    refreshSessions();
    if (active_session_index_ >= 0)
      showSession(active_session_index_);
    statusBar()->showMessage("Run finished");

    if (shutting_down_)
      return;

    for (int i = 0; i < static_cast<int>(queue_.size()); ++i) {
      if (queue_[i].enabled && queue_[i].state == "queued") {
        startQueueIndex(i);
        return;
      }
    }
  }

  void cancelActive() {
    if (!process_)
      return;
    process_->kill();
    statusBar()->showMessage("Cancelling active run...");
  }

  void toggleSelectedQueue() {
    const int idx = selectedQueueIndex();
    if (idx < 0)
      return;
    queue_[idx].enabled = !queue_[idx].enabled;
    refreshQueue();
    queue_list_->setCurrentRow(idx);
  }

  void moveQueue(int delta) {
    const int idx = selectedQueueIndex();
    if (idx < 0)
      return;
    const int target = idx + delta;
    if (target < 0 || target >= static_cast<int>(queue_.size()))
      return;
    std::swap(queue_[idx], queue_[target]);
    refreshQueue();
    queue_list_->setCurrentRow(target);
  }

  void duplicateSelected() {
    int idx = selectedQueueIndex();
    if (idx >= 0) {
      queue_.push_back(queue_[idx]);
      queue_.back().state = "queued";
      refreshQueue();
      queue_list_->setCurrentRow(static_cast<int>(queue_.size()) - 1);
      return;
    }

    idx = selectedSessionIndex();
    if (idx >= 0) {
      QueuedRun run;
      run.request = sessions_[idx].request;
      queue_.push_back(run);
      refreshQueue();
      queue_list_->setCurrentRow(static_cast<int>(queue_.size()) - 1);
    }
  }

  void retrySelected() {
    int idx = selectedQueueIndex();
    if (idx >= 0) {
      queue_[idx].state = "queued";
      queue_[idx].last_exit_code = 0;
      refreshQueue();
      queue_list_->setCurrentRow(idx);
      return;
    }

    idx = selectedSessionIndex();
    if (idx >= 0) {
      QueuedRun run;
      run.request = sessions_[idx].request;
      run.state = "queued";
      queue_.push_back(run);
      refreshQueue();
      queue_list_->setCurrentRow(static_cast<int>(queue_.size()) - 1);
    }
  }

  void pollEventFile() {
    if (active_session_index_ < 0 || active_session_index_ >= static_cast<int>(sessions_.size()))
      return;
    auto &session = sessions_[active_session_index_];
    if (session.event_path.isEmpty())
      return;
    if (!event_file_.isOpen()) {
      if (!event_file_.exists())
        return;
      if (!event_file_.open(QIODevice::ReadOnly | QIODevice::Text))
        return;
      event_file_offset_ = 0;
    }

    event_file_.seek(event_file_offset_);
    while (event_file_.canReadLine()) {
      const QByteArray line = event_file_.readLine();
      event_file_offset_ = event_file_.pos();
      auto parsed = llvm::json::parse(line.toStdString());
      if (!parsed)
        continue;
      auto event = omill::tools::parseLiftRunEvent(*parsed);
      if (!event)
        continue;
      session.events.push_back(*event);
      if (event->severity == "warning")
        session.result.warnings.push_back(event->message);
      if (event->severity == "error")
        session.result.errors.push_back(event->message);

      if (event->kind == "output_write_completed" || event->kind == "run_done") {
        if (const auto it = event->payload.find("path"); it != event->payload.end()) {
          if (auto s = it->second.getAsString())
            pushUniqueString(session.result.artifacts, std::string(*s));
        }
        if (const auto it = event->payload.find("output_file"); it != event->payload.end()) {
          if (auto s = it->second.getAsString())
            pushUniqueString(session.result.artifacts, std::string(*s));
        }
      }
    }

    if (session_list_->currentRow() == active_session_index_)
      showSession(active_session_index_);
  }

  void showSession(int index) {
    event_list_->clear();
    stderr_list_->clear();
    artifacts_list_->clear();
    if (index < 0 || index >= static_cast<int>(sessions_.size()))
      return;

    const auto &session = sessions_[index];
    for (const auto &event : session.events) {
      event_list_->addItem(
          QString("[%1] %2 %3 | %4")
              .arg(QString::number(event.seq),
                   QString::fromStdString(event.severity),
                   QString::fromStdString(event.kind),
                   QString::fromStdString(event.message)));
    }
    for (const auto &line : session.stderr_lines)
      stderr_list_->addItem(line);
    for (const auto &path : session.result.artifacts)
      artifacts_list_->addItem(QString::fromStdString(path));

    loadFirstLlArtifactFromSession(session);
  }

  void exportSelectedSession() {
    const int idx = selectedSessionIndex();
    if (idx < 0)
      return;
    const auto &session = sessions_[idx];

    const QString path = QFileDialog::getSaveFileName(
        this, "Export Session JSON", "omill-lift-session.json",
        "JSON Files (*.json)");
    if (path.isEmpty())
      return;

    llvm::json::Object root;
    root["id"] = session.id.toStdString();
    root["status"] = session.status.toStdString();
    root["request"] = omill::tools::toJSON(session.request);
    root["result"] = omill::tools::toJSON(session.result);

    llvm::json::Array events;
    for (const auto &event : session.events)
      events.push_back(omill::tools::toJSON(event));
    root["events"] = std::move(events);

    llvm::json::Array stderr_arr;
    for (const auto &line : session.stderr_lines)
      stderr_arr.push_back(line.toStdString());
    root["stderr"] = std::move(stderr_arr);

    std::string payload;
    llvm::raw_string_ostream os(payload);
    os << llvm::json::Value(std::move(root));
    os.flush();

    QFile out(path);
    if (!out.open(QIODevice::WriteOnly | QIODevice::Text)) {
      QMessageBox::warning(this, "Export Failed", "Could not open target path.");
      return;
    }
    out.write(payload.c_str(), static_cast<qint64>(payload.size()));
    out.close();
    statusBar()->showMessage("Session exported: " + path, 4000);
  }

  QString selectedFunctionForView() const {
    return function_combo_->currentText().trimmed();
  }

  QString extractFunctionSnippet(const QString &module, const QString &function_name) const {
    if (module.isEmpty())
      return {};
    if (function_name.isEmpty() || function_name == "<module>")
      return module;

    const QString marker = "@" + function_name + "(";
    const QStringList lines = module.split('\n');

    bool capture = false;
    int brace_depth = 0;
    QString snippet;

    for (const auto &line : lines) {
      if (!capture) {
        if (line.contains("define") && line.contains(marker)) {
          capture = true;
        } else {
          continue;
        }
      }

      snippet += line;
      snippet += "\n";
      brace_depth += line.count('{');
      brace_depth -= line.count('}');

      if (capture && brace_depth <= 0 && line.contains('}'))
        break;
    }

    if (snippet.isEmpty())
      return QString("; Function '%1' not found in current module view.\n").arg(function_name);
    return snippet;
  }

  QString buildSimpleDiff(const QString &before, const QString &after) const {
    const QStringList a = before.split('\n');
    const QStringList b = after.split('\n');

    int i = 0;
    int j = 0;
    QString diff;
    while (i < a.size() || j < b.size()) {
      if (i < a.size() && j < b.size() && a[i] == b[j]) {
        diff += "  " + a[i] + "\n";
        ++i;
        ++j;
        continue;
      }
      if (i < a.size()) {
        diff += "- " + a[i] + "\n";
        ++i;
      }
      if (j < b.size()) {
        diff += "+ " + b[j] + "\n";
        ++j;
      }
    }
    return diff;
  }

  void rebuildFunctionListFromCurrentIr() {
    const QString previous = function_combo_->currentText();
    function_combo_->clear();
    function_combo_->addItem("<module>");

    const QRegularExpression rx("^\\s*define\\b[^@]*@([^\\(\\s]+)\\(",
                                QRegularExpression::MultilineOption);
    auto it = rx.globalMatch(current_ir_text_);
    QStringList names;
    while (it.hasNext()) {
      const auto m = it.next();
      const QString name = m.captured(1);
      if (!name.isEmpty() && !names.contains(name))
        names.push_back(name);
    }
    names.sort();
    for (const auto &name : names)
      function_combo_->addItem(name);

    const int previous_idx = function_combo_->findText(previous);
    if (previous_idx >= 0)
      function_combo_->setCurrentIndex(previous_idx);
  }

  void refreshFunctionViews() {
    const QString function_name = selectedFunctionForView();
    const QString before_module = current_ir_text_;
    const QString after_module = transformed_ir_text_.isEmpty() ? current_ir_text_ : transformed_ir_text_;

    const QString before = extractFunctionSnippet(before_module, function_name);
    const QString after = extractFunctionSnippet(after_module, function_name);

    ir_before_view_->setPlainText(before);
    ir_after_view_->setPlainText(after);
    ir_diff_view_->setPlainText(buildSimpleDiff(before, after));
  }

  void loadIrFromPath(const QString &path) {
    if (path.isEmpty())
      return;
    const QString text = readTextFile(path);
    if (text.isEmpty()) {
      QMessageBox::warning(this, "Load IR Failed", "Could not read IR file: " + path);
      return;
    }

    current_ir_path_ = path;
    current_ir_text_ = text;
    transformed_ir_text_.clear();
    current_ir_path_edit_->setText(path);
    rebuildFunctionListFromCurrentIr();
    refreshFunctionViews();
    right_tabs_->setCurrentIndex(1);
    statusBar()->showMessage("Loaded IR: " + path, 3000);
  }

  void loadFirstLlArtifactFromSession(const SessionRecord &session) {
    QString candidate;

    if (!session.request.output_filename.empty()) {
      const QString from_request = QString::fromStdString(session.request.output_filename);
      if (from_request.endsWith(".ll", Qt::CaseInsensitive) && QFileInfo::exists(from_request))
        candidate = from_request;
    }

    if (candidate.isEmpty()) {
      for (const auto &artifact : session.result.artifacts) {
        const QString p = QString::fromStdString(artifact);
        if (p.endsWith(".ll", Qt::CaseInsensitive) && QFileInfo::exists(p)) {
          candidate = p;
          break;
        }
      }
    }

    if (candidate.isEmpty())
      return;
    if (candidate == current_ir_path_ && !current_ir_text_.isEmpty())
      return;

    loadIrFromPath(candidate);
  }

  void loadSelectedArtifactIfLl() {
    auto *item = artifacts_list_->currentItem();
    if (!item)
      return;
    const QString path = item->text();
    if (!path.endsWith(".ll", Qt::CaseInsensitive)) {
      QMessageBox::information(this, "Artifact", "Selected artifact is not an .ll file.");
      return;
    }
    loadIrFromPath(path);
  }

  void resetTransformedIr() {
    transformed_ir_text_.clear();
    refreshFunctionViews();
    statusBar()->showMessage("Cleared transformed IR and returned to original module", 3000);
  }

  bool runExternalProcess(const QString &program, const QStringList &args,
                          QString &std_out, QString &std_err,
                          int &exit_code, int timeout_ms = 120000) {
    QProcess proc;
    proc.setProcessChannelMode(QProcess::SeparateChannels);
    proc.start(program, args);
    if (!proc.waitForStarted(8000)) {
      std_err = "Failed to start process: " + program;
      exit_code = 127;
      return false;
    }
    if (!proc.waitForFinished(timeout_ms)) {
      proc.kill();
      proc.waitForFinished(2000);
      std_err = "Process timed out: " + program;
      exit_code = 124;
      return false;
    }

    std_out = QString::fromUtf8(proc.readAllStandardOutput());
    std_err = QString::fromUtf8(proc.readAllStandardError());
    exit_code = proc.exitCode();
    return proc.exitStatus() == QProcess::NormalExit;
  }

  QString materializeCurrentIrForTools() {
    if (current_ir_text_.isEmpty())
      return {};

    if (transformed_ir_text_.isEmpty() && !current_ir_path_.isEmpty() && QFileInfo::exists(current_ir_path_))
      return current_ir_path_;

    const QString temp_path =
        QDir::tempPath() + "/omill-lift-ui-work-" +
        QDateTime::currentDateTimeUtc().toString("yyyyMMddhhmmsszzz") + ".ll";
    const QString payload = transformed_ir_text_.isEmpty() ? current_ir_text_ : transformed_ir_text_;
    if (!writeTextFile(temp_path, payload))
      return {};
    return temp_path;
  }

  void appendToolLog(const QString &line) {
    compile_log_view_->appendPlainText(line);
  }

  void applySelectedPassPipeline() {
    if (current_ir_text_.isEmpty()) {
      QMessageBox::information(this, "No IR Loaded", "Load a lifted .ll file first.");
      return;
    }

    const QString opt_program = opt_binary_edit_->text().trimmed().isEmpty()
                                    ? "opt"
                                    : opt_binary_edit_->text().trimmed();
    const QString pipeline = pass_combo_->currentData().toString();
    if (pipeline.isEmpty()) {
      QMessageBox::warning(this, "Pass Pipeline", "Selected pass pipeline is empty.");
      return;
    }

    const QString input_path = materializeCurrentIrForTools();
    if (input_path.isEmpty()) {
      QMessageBox::warning(this, "IR Materialization", "Failed to materialize IR for pass run.");
      return;
    }

    const QString output_path =
        QDir::tempPath() + "/omill-lift-ui-pass-out-" +
        QDateTime::currentDateTimeUtc().toString("yyyyMMddhhmmsszzz") + ".ll";

    QStringList args;
    args << "-S";
    args << "-passes=" + pipeline;
    args << input_path;
    args << "-o";
    args << output_path;

    appendToolLog("[pass] " + commandPreview(opt_program, args));

    QString out;
    QString err;
    int exit_code = 0;
    const bool normal = runExternalProcess(opt_program, args, out, err, exit_code);
    if (!out.isEmpty())
      appendToolLog(out);
    if (!err.isEmpty())
      appendToolLog(err);

    if (!normal || exit_code != 0 || !QFileInfo::exists(output_path)) {
      QMessageBox::warning(this, "Pass Failure",
                           QString("opt failed (exit %1). Check Tool Log.").arg(exit_code));
      return;
    }

    const QString transformed = readTextFile(output_path);
    if (transformed.isEmpty()) {
      QMessageBox::warning(this, "Pass Failure", "Pass output was empty or unreadable.");
      return;
    }

    transformed_ir_text_ = transformed;
    refreshFunctionViews();
    right_tabs_->setCurrentIndex(1);
    statusBar()->showMessage("Applied pipeline: " + pass_combo_->currentText(), 4000);
  }

  void planCompileAndDecompile() {
    plan_list_->clear();

    if (current_ir_text_.isEmpty()) {
      plan_list_->addItem("No IR loaded. Load a .ll file before planning compile/decompile.");
      right_tabs_->setCurrentIndex(2);
      return;
    }

    const QString ir_path = transformed_ir_text_.isEmpty() && !current_ir_path_.isEmpty()
                                ? current_ir_path_
                                : "<materialized temp .ll from current editor state>";

    const QString clang_program = clang_binary_edit_->text().trimmed().isEmpty()
                                      ? "clang"
                                      : clang_binary_edit_->text().trimmed();
    const QString compile_output = compile_output_edit_->text().trimmed();

    QStringList compile_args;
    compile_args << ir_path;
    compile_args << "-o";
    compile_args << compile_output;

    plan_list_->addItem("1. Compile lifted IR -> binary");
    plan_list_->addItem("   " + commandPreview(clang_program, compile_args));

    const QString ida_program = ida_binary_edit_->text().trimmed().isEmpty()
                                    ? "idat64"
                                    : ida_binary_edit_->text().trimmed();
    const QString ida_script = ida_script_edit_->text().trimmed();
    const QString decomp_output = decompile_output_edit_->text().trimmed();

    QStringList decomp_args;
    decomp_args << "-A";
    if (!ida_script.isEmpty()) {
      const QString script_arg = QString("-S%1 \"%2\" \"%3\"")
                                     .arg(ida_script, compile_output, decomp_output);
      decomp_args << script_arg;
    }
    decomp_args << compile_output;

    plan_list_->addItem("2. Run IDA CLI decompile export");
    plan_list_->addItem("   " + commandPreview(ida_program, decomp_args));
    plan_list_->addItem("3. Load exported text with syntax highlight");

    right_tabs_->setCurrentIndex(2);
  }

  void runCompileStep() {
    if (current_ir_text_.isEmpty()) {
      QMessageBox::information(this, "No IR Loaded", "Load lifted IR before running compile.");
      return;
    }

    const QString materialized_ir = materializeCurrentIrForTools();
    if (materialized_ir.isEmpty()) {
      QMessageBox::warning(this, "Compile", "Failed to materialize IR for compilation.");
      return;
    }

    QString compile_output = compile_output_edit_->text().trimmed();
    if (compile_output.isEmpty()) {
      compile_output = QDir::tempPath() + "/omill-lift-ui-out.exe";
      compile_output_edit_->setText(compile_output);
    }

    const QString clang_program = clang_binary_edit_->text().trimmed().isEmpty()
                                      ? "clang"
                                      : clang_binary_edit_->text().trimmed();

    QStringList args;
    args << materialized_ir;
    args << "-o";
    args << compile_output;

    appendToolLog("[compile] " + commandPreview(clang_program, args));

    QString out;
    QString err;
    int exit_code = 0;
    const bool normal = runExternalProcess(clang_program, args, out, err, exit_code, 180000);
    if (!out.isEmpty())
      appendToolLog(out);
    if (!err.isEmpty())
      appendToolLog(err);

    if (!normal || exit_code != 0 || !QFileInfo::exists(compile_output)) {
      QMessageBox::warning(this, "Compile Failed",
                           QString("Compile failed (exit %1). See Tool Log.").arg(exit_code));
      return;
    }

    last_compiled_binary_path_ = compile_output;
    if (decompile_output_edit_->text().trimmed().isEmpty())
      decompile_output_edit_->setText(compile_output + ".c");

    appendToolLog("[compile] output: " + compile_output);
    statusBar()->showMessage("Compile succeeded: " + compile_output, 5000);
    right_tabs_->setCurrentIndex(2);
  }

  void runIdaDecompileStep() {
    QString binary_path = compile_output_edit_->text().trimmed();
    if (binary_path.isEmpty())
      binary_path = last_compiled_binary_path_;
    if (binary_path.isEmpty() || !QFileInfo::exists(binary_path)) {
      QMessageBox::warning(this, "Decompile", "Compiled binary not found. Run compile first.");
      return;
    }

    const QString ida_script = ida_script_edit_->text().trimmed();
    if (ida_script.isEmpty() || !QFileInfo::exists(ida_script)) {
      QMessageBox::warning(
          this, "Decompile",
          "IDA script path is required. Provide a script that exports pseudocode to a file.");
      return;
    }

    QString output_path = decompile_output_edit_->text().trimmed();
    if (output_path.isEmpty()) {
      output_path = binary_path + ".c";
      decompile_output_edit_->setText(output_path);
    }

    const QString ida_program = ida_binary_edit_->text().trimmed().isEmpty()
                                    ? "idat64"
                                    : ida_binary_edit_->text().trimmed();

    QStringList args;
    args << "-A";
    args << QString("-S%1 \"%2\" \"%3\"").arg(ida_script, binary_path, output_path);
    args << binary_path;

    appendToolLog("[ida] " + commandPreview(ida_program, args));

    QString out;
    QString err;
    int exit_code = 0;
    const bool normal = runExternalProcess(ida_program, args, out, err, exit_code, 600000);
    if (!out.isEmpty())
      appendToolLog(out);
    if (!err.isEmpty())
      appendToolLog(err);

    if (!normal || exit_code != 0) {
      QMessageBox::warning(this, "IDA Failed",
                           QString("IDA CLI returned exit %1. Check Tool Log.").arg(exit_code));
    }

    if (QFileInfo::exists(output_path)) {
      const QString decompiled = readTextFile(output_path);
      decompile_view_->setPlainText(decompiled);
      appendToolLog("[ida] exported decompile: " + output_path);
      statusBar()->showMessage("Loaded decompile output: " + output_path, 5000);
    } else {
      appendToolLog("[ida] expected output file not found: " + output_path);
    }

    right_tabs_->setCurrentIndex(2);
  }

  QLineEdit *binary_edit_ = nullptr;
  QPushButton *browse_binary_btn_ = nullptr;
  QLineEdit *input_edit_ = nullptr;
  QPushButton *browse_input_btn_ = nullptr;
  QLineEdit *va_edit_ = nullptr;
  QLineEdit *base_edit_ = nullptr;
  QLineEdit *output_edit_ = nullptr;
  QPushButton *browse_output_btn_ = nullptr;
  QLineEdit *vm_entry_edit_ = nullptr;
  QLineEdit *vm_exit_edit_ = nullptr;
  QLineEdit *trace_func_edit_ = nullptr;
  QLineEdit *scan_section_edit_ = nullptr;
  QLineEdit *scan_output_edit_ = nullptr;
  QLineEdit *deobf_targets_edit_ = nullptr;
  QPushButton *browse_deobf_targets_btn_ = nullptr;
  QLineEdit *deobf_section_edit_ = nullptr;
  QLineEdit *min_func_size_edit_ = nullptr;
  QLineEdit *max_iterations_edit_ = nullptr;
  QLineEdit *event_jsonl_edit_ = nullptr;
  QPushButton *browse_event_jsonl_btn_ = nullptr;
  QComboBox *event_detail_combo_ = nullptr;

  QCheckBox *raw_cb_ = nullptr;
  QCheckBox *no_abi_cb_ = nullptr;
  QCheckBox *deobf_cb_ = nullptr;
  QCheckBox *resolve_targets_cb_ = nullptr;
  QCheckBox *ipcp_cb_ = nullptr;
  QCheckBox *resolve_exceptions_cb_ = nullptr;
  QCheckBox *block_lift_cb_ = nullptr;
  QCheckBox *dump_ir_cb_ = nullptr;
  QCheckBox *omill_time_cb_ = nullptr;
  QCheckBox *verify_each_cb_ = nullptr;
  QCheckBox *dump_func_phases_cb_ = nullptr;
  QCheckBox *scan_all_cb_ = nullptr;

  QListWidget *queue_list_ = nullptr;
  QListWidget *session_list_ = nullptr;
  QListWidget *event_list_ = nullptr;
  QListWidget *stderr_list_ = nullptr;
  QListWidget *artifacts_list_ = nullptr;

  QPushButton *add_queue_btn_ = nullptr;
  QPushButton *start_btn_ = nullptr;
  QPushButton *cancel_btn_ = nullptr;
  QPushButton *retry_btn_ = nullptr;
  QPushButton *duplicate_btn_ = nullptr;
  QPushButton *toggle_btn_ = nullptr;
  QPushButton *up_btn_ = nullptr;
  QPushButton *down_btn_ = nullptr;
  QPushButton *export_btn_ = nullptr;
  QPushButton *open_artifact_btn_ = nullptr;

  QTabWidget *right_tabs_ = nullptr;

  QLineEdit *current_ir_path_edit_ = nullptr;
  QPushButton *load_ir_btn_ = nullptr;
  QComboBox *function_combo_ = nullptr;
  QComboBox *pass_combo_ = nullptr;
  QLineEdit *opt_binary_edit_ = nullptr;
  QPushButton *apply_pass_btn_ = nullptr;
  QPushButton *reset_ir_btn_ = nullptr;
  QPlainTextEdit *ir_before_view_ = nullptr;
  QPlainTextEdit *ir_after_view_ = nullptr;
  QPlainTextEdit *ir_diff_view_ = nullptr;

  QLineEdit *clang_binary_edit_ = nullptr;
  QLineEdit *compile_output_edit_ = nullptr;
  QLineEdit *ida_binary_edit_ = nullptr;
  QLineEdit *ida_script_edit_ = nullptr;
  QLineEdit *decompile_output_edit_ = nullptr;
  QPushButton *browse_compile_output_btn_ = nullptr;
  QPushButton *browse_ida_script_btn_ = nullptr;
  QPushButton *browse_decompile_output_btn_ = nullptr;
  QPushButton *plan_btn_ = nullptr;
  QPushButton *compile_btn_ = nullptr;
  QPushButton *decompile_btn_ = nullptr;
  QListWidget *plan_list_ = nullptr;
  QPlainTextEdit *compile_log_view_ = nullptr;
  QPlainTextEdit *decompile_view_ = nullptr;

  QString current_ir_path_;
  QString current_ir_text_;
  QString transformed_ir_text_;
  QString last_compiled_binary_path_;

  std::vector<QueuedRun> queue_;
  std::vector<SessionRecord> sessions_;
  int active_queue_index_ = -1;
  int active_session_index_ = -1;

  std::unique_ptr<QProcess> process_;
  QFile event_file_;
  qint64 event_file_offset_ = 0;
  QTimer event_poll_timer_;
  bool shutting_down_ = false;
};

}  // namespace

int main(int argc, char **argv) {
  QApplication app(argc, argv);
  MainWindow window;
  window.show();
  return app.exec();
}
