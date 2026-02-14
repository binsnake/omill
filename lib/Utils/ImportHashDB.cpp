#include "omill/Utils/ImportHashDB.h"

#include <llvm/Support/MemoryBuffer.h>
#include <llvm/Support/raw_ostream.h>

#include <fstream>

namespace omill {

namespace {

/// Algorithm/seed combinations to precompute.
struct AlgoSeed {
  HashAlgorithm algo;
  uint32_t seed;
};

static constexpr AlgoSeed kPrecomputedCombinations[] = {
    {HashAlgorithm::FNV1a32, 0x811c9dc5u},
    {HashAlgorithm::FNV1a32, 0u},
    {HashAlgorithm::FNV1a32_Lowercase, 0x811c9dc5u},
    {HashAlgorithm::FNV1a32_Lowercase, 0u},
    {HashAlgorithm::DJB2, 5381u},
    {HashAlgorithm::DJB2, 0u},
};

}  // namespace

uint32_t ImportHashDB::computeHash(llvm::StringRef name, HashAlgorithm algo,
                                   uint32_t seed) {
  uint32_t value = seed;
  switch (algo) {
    case HashAlgorithm::FNV1a32:
      for (unsigned char c : name)
        value = (value ^ c) * 0x01000193u;
      break;
    case HashAlgorithm::FNV1a32_Lowercase:
      for (unsigned char c : name) {
        if (c >= 'A' && c <= 'Z')
          c |= 0x20;
        value = (value ^ c) * 0x01000193u;
      }
      break;
    case HashAlgorithm::DJB2:
      for (unsigned char c : name)
        value = value * 33 + c;
      break;
  }
  return value;
}

uint32_t ImportHashDB::computeHash(llvm::StringRef name, uint32_t offset) {
  return computeHash(name, HashAlgorithm::FNV1a32, offset);
}

void ImportHashDB::addExport(llvm::StringRef module, llvm::StringRef function) {
  exports_.push_back({module.str(), function.str()});
}

bool ImportHashDB::loadFromFile(llvm::StringRef path) {
  auto buf = llvm::MemoryBuffer::getFile(path);
  if (!buf)
    return false;

  llvm::StringRef content = (*buf)->getBuffer();
  while (!content.empty()) {
    auto [line, rest] = content.split('\n');
    content = rest;
    line = line.trim();
    if (line.empty())
      continue;
    auto [mod, func] = line.split('\t');
    if (!func.empty())
      addExport(mod, func);
  }
  return true;
}

void ImportHashDB::buildLookupTables() {
  lookup_tables_.clear();
  for (const auto &combo : kPrecomputedCombinations) {
    LookupTable lt;
    lt.algo = combo.algo;
    lt.seed = combo.seed;
    for (size_t i = 0; i < exports_.size(); ++i) {
      uint32_t h = computeHash(exports_[i].function, combo.algo, combo.seed);
      lt.table.try_emplace(h, i);
    }
    lookup_tables_.push_back(std::move(lt));
  }
}

std::optional<ImportHashDB::ResolvedImport> ImportHashDB::tryResolve(
    uint32_t hash_value) const {
  for (const auto &lt : lookup_tables_) {
    auto it = lt.table.find(hash_value);
    if (it != lt.table.end()) {
      return ResolvedImport{exports_[it->second], lt.algo, lt.seed};
    }
  }
  return std::nullopt;
}

std::optional<ImportHashDB::ExportEntry> ImportHashDB::resolve(
    uint32_t offset, uint32_t target_hash) const {
  for (const auto &entry : exports_) {
    if (computeHash(entry.function, offset) == target_hash)
      return entry;
  }
  return std::nullopt;
}

// Built-in table of common Windows API exports.
// Covers kernel32, ntdll, user32, advapi32, ws2_32, ole32, shell32,
// crypt32, winhttp, bcrypt, shlwapi, gdi32, comctl32, msvcrt, ucrtbase.
void ImportHashDB::loadBuiltins() {
  // Helper macro: M(module, function)
#define M(mod, fn) addExport(mod, fn)

  // --- kernel32.dll ---
  M("kernel32.dll", "AddVectoredExceptionHandler");
  M("kernel32.dll", "AllocConsole");
  M("kernel32.dll", "CloseHandle");
  M("kernel32.dll", "CopyFileA");
  M("kernel32.dll", "CopyFileW");
  M("kernel32.dll", "CreateDirectoryA");
  M("kernel32.dll", "CreateDirectoryW");
  M("kernel32.dll", "CreateEventA");
  M("kernel32.dll", "CreateEventW");
  M("kernel32.dll", "CreateFileA");
  M("kernel32.dll", "CreateFileW");
  M("kernel32.dll", "CreateFileMappingA");
  M("kernel32.dll", "CreateFileMappingW");
  M("kernel32.dll", "CreateMutexA");
  M("kernel32.dll", "CreateMutexW");
  M("kernel32.dll", "CreatePipe");
  M("kernel32.dll", "CreateProcessA");
  M("kernel32.dll", "CreateProcessW");
  M("kernel32.dll", "CreateRemoteThread");
  M("kernel32.dll", "CreateRemoteThreadEx");
  M("kernel32.dll", "CreateSemaphoreA");
  M("kernel32.dll", "CreateSemaphoreW");
  M("kernel32.dll", "CreateThread");
  M("kernel32.dll", "CreateToolhelp32Snapshot");
  M("kernel32.dll", "DebugBreak");
  M("kernel32.dll", "DecodePointer");
  M("kernel32.dll", "DeleteCriticalSection");
  M("kernel32.dll", "DeleteFileA");
  M("kernel32.dll", "DeleteFileW");
  M("kernel32.dll", "DeviceIoControl");
  M("kernel32.dll", "DisableThreadLibraryCalls");
  M("kernel32.dll", "DuplicateHandle");
  M("kernel32.dll", "EncodePointer");
  M("kernel32.dll", "EnterCriticalSection");
  M("kernel32.dll", "EnumProcessModules");
  M("kernel32.dll", "ExitProcess");
  M("kernel32.dll", "ExitThread");
  M("kernel32.dll", "ExpandEnvironmentStringsA");
  M("kernel32.dll", "ExpandEnvironmentStringsW");
  M("kernel32.dll", "FindClose");
  M("kernel32.dll", "FindFirstFileA");
  M("kernel32.dll", "FindFirstFileW");
  M("kernel32.dll", "FindNextFileA");
  M("kernel32.dll", "FindNextFileW");
  M("kernel32.dll", "FindResourceA");
  M("kernel32.dll", "FindResourceW");
  M("kernel32.dll", "FlushFileBuffers");
  M("kernel32.dll", "FlushInstructionCache");
  M("kernel32.dll", "FlushViewOfFile");
  M("kernel32.dll", "FreeLibrary");
  M("kernel32.dll", "GetCommandLineA");
  M("kernel32.dll", "GetCommandLineW");
  M("kernel32.dll", "GetComputerNameA");
  M("kernel32.dll", "GetComputerNameW");
  M("kernel32.dll", "GetConsoleWindow");
  M("kernel32.dll", "GetCurrentDirectory");
  M("kernel32.dll", "GetCurrentDirectoryA");
  M("kernel32.dll", "GetCurrentDirectoryW");
  M("kernel32.dll", "GetCurrentProcess");
  M("kernel32.dll", "GetCurrentProcessId");
  M("kernel32.dll", "GetCurrentThread");
  M("kernel32.dll", "GetCurrentThreadId");
  M("kernel32.dll", "GetEnvironmentVariableA");
  M("kernel32.dll", "GetEnvironmentVariableW");
  M("kernel32.dll", "GetExitCodeProcess");
  M("kernel32.dll", "GetExitCodeThread");
  M("kernel32.dll", "GetFileAttributesA");
  M("kernel32.dll", "GetFileAttributesW");
  M("kernel32.dll", "GetFileSize");
  M("kernel32.dll", "GetFileSizeEx");
  M("kernel32.dll", "GetFileType");
  M("kernel32.dll", "GetFullPathNameA");
  M("kernel32.dll", "GetFullPathNameW");
  M("kernel32.dll", "GetLastError");
  M("kernel32.dll", "GetLocalTime");
  M("kernel32.dll", "GetModuleFileNameA");
  M("kernel32.dll", "GetModuleFileNameW");
  M("kernel32.dll", "GetModuleHandleA");
  M("kernel32.dll", "GetModuleHandleW");
  M("kernel32.dll", "GetModuleHandleExA");
  M("kernel32.dll", "GetModuleHandleExW");
  M("kernel32.dll", "GetNativeSystemInfo");
  M("kernel32.dll", "GetOverlappedResult");
  M("kernel32.dll", "GetProcAddress");
  M("kernel32.dll", "GetProcessHeap");
  M("kernel32.dll", "GetProcessId");
  M("kernel32.dll", "GetStartupInfoA");
  M("kernel32.dll", "GetStartupInfoW");
  M("kernel32.dll", "GetStdHandle");
  M("kernel32.dll", "GetSystemDirectoryA");
  M("kernel32.dll", "GetSystemDirectoryW");
  M("kernel32.dll", "GetSystemInfo");
  M("kernel32.dll", "GetSystemTime");
  M("kernel32.dll", "GetSystemTimeAsFileTime");
  M("kernel32.dll", "GetTempFileNameA");
  M("kernel32.dll", "GetTempFileNameW");
  M("kernel32.dll", "GetTempPathA");
  M("kernel32.dll", "GetTempPathW");
  M("kernel32.dll", "GetThreadContext");
  M("kernel32.dll", "GetTickCount");
  M("kernel32.dll", "GetTickCount64");
  M("kernel32.dll", "GetVersionExA");
  M("kernel32.dll", "GetVersionExW");
  M("kernel32.dll", "GetVolumeInformationA");
  M("kernel32.dll", "GetVolumeInformationW");
  M("kernel32.dll", "GetWindowsDirectoryA");
  M("kernel32.dll", "GetWindowsDirectoryW");
  M("kernel32.dll", "GlobalAlloc");
  M("kernel32.dll", "GlobalFree");
  M("kernel32.dll", "GlobalLock");
  M("kernel32.dll", "GlobalUnlock");
  M("kernel32.dll", "HeapAlloc");
  M("kernel32.dll", "HeapCreate");
  M("kernel32.dll", "HeapDestroy");
  M("kernel32.dll", "HeapFree");
  M("kernel32.dll", "HeapReAlloc");
  M("kernel32.dll", "HeapSize");
  M("kernel32.dll", "InitializeCriticalSection");
  M("kernel32.dll", "InitializeCriticalSectionAndSpinCount");
  M("kernel32.dll", "InterlockedCompareExchange");
  M("kernel32.dll", "InterlockedDecrement");
  M("kernel32.dll", "InterlockedExchange");
  M("kernel32.dll", "InterlockedIncrement");
  M("kernel32.dll", "IsBadReadPtr");
  M("kernel32.dll", "IsDebuggerPresent");
  M("kernel32.dll", "IsProcessorFeaturePresent");
  M("kernel32.dll", "IsWow64Process");
  M("kernel32.dll", "K32EnumProcessModules");
  M("kernel32.dll", "K32GetModuleBaseNameA");
  M("kernel32.dll", "K32GetModuleBaseNameW");
  M("kernel32.dll", "K32GetModuleFileNameExA");
  M("kernel32.dll", "K32GetModuleFileNameExW");
  M("kernel32.dll", "LeaveCriticalSection");
  M("kernel32.dll", "LoadLibraryA");
  M("kernel32.dll", "LoadLibraryExA");
  M("kernel32.dll", "LoadLibraryExW");
  M("kernel32.dll", "LoadLibraryW");
  M("kernel32.dll", "LoadResource");
  M("kernel32.dll", "LocalAlloc");
  M("kernel32.dll", "LocalFree");
  M("kernel32.dll", "LockResource");
  M("kernel32.dll", "MapViewOfFile");
  M("kernel32.dll", "Module32First");
  M("kernel32.dll", "Module32FirstW");
  M("kernel32.dll", "Module32Next");
  M("kernel32.dll", "Module32NextW");
  M("kernel32.dll", "MoveFileA");
  M("kernel32.dll", "MoveFileExA");
  M("kernel32.dll", "MoveFileExW");
  M("kernel32.dll", "MoveFileW");
  M("kernel32.dll", "MultiByteToWideChar");
  M("kernel32.dll", "OpenEventA");
  M("kernel32.dll", "OpenEventW");
  M("kernel32.dll", "OpenFileMappingA");
  M("kernel32.dll", "OpenFileMappingW");
  M("kernel32.dll", "OpenMutexA");
  M("kernel32.dll", "OpenMutexW");
  M("kernel32.dll", "OpenProcess");
  M("kernel32.dll", "OpenThread");
  M("kernel32.dll", "OutputDebugStringA");
  M("kernel32.dll", "OutputDebugStringW");
  M("kernel32.dll", "PeekNamedPipe");
  M("kernel32.dll", "Process32First");
  M("kernel32.dll", "Process32FirstW");
  M("kernel32.dll", "Process32Next");
  M("kernel32.dll", "Process32NextW");
  M("kernel32.dll", "QueryPerformanceCounter");
  M("kernel32.dll", "QueryPerformanceFrequency");
  M("kernel32.dll", "RaiseException");
  M("kernel32.dll", "ReadFile");
  M("kernel32.dll", "ReadProcessMemory");
  M("kernel32.dll", "ReleaseMutex");
  M("kernel32.dll", "ReleaseSemaphore");
  M("kernel32.dll", "RemoveDirectoryA");
  M("kernel32.dll", "RemoveDirectoryW");
  M("kernel32.dll", "ResetEvent");
  M("kernel32.dll", "ResumeThread");
  M("kernel32.dll", "RtlCaptureContext");
  M("kernel32.dll", "SetConsoleCtrlHandler");
  M("kernel32.dll", "SetCurrentDirectoryA");
  M("kernel32.dll", "SetCurrentDirectoryW");
  M("kernel32.dll", "SetEndOfFile");
  M("kernel32.dll", "SetEnvironmentVariableA");
  M("kernel32.dll", "SetEnvironmentVariableW");
  M("kernel32.dll", "SetEvent");
  M("kernel32.dll", "SetFileAttributesA");
  M("kernel32.dll", "SetFileAttributesW");
  M("kernel32.dll", "SetFilePointer");
  M("kernel32.dll", "SetFilePointerEx");
  M("kernel32.dll", "SetLastError");
  M("kernel32.dll", "SetThreadContext");
  M("kernel32.dll", "SetUnhandledExceptionFilter");
  M("kernel32.dll", "SignalObjectAndWait");
  M("kernel32.dll", "SizeofResource");
  M("kernel32.dll", "Sleep");
  M("kernel32.dll", "SleepEx");
  M("kernel32.dll", "SuspendThread");
  M("kernel32.dll", "SwitchToThread");
  M("kernel32.dll", "TerminateProcess");
  M("kernel32.dll", "TerminateThread");
  M("kernel32.dll", "Thread32First");
  M("kernel32.dll", "Thread32Next");
  M("kernel32.dll", "TlsAlloc");
  M("kernel32.dll", "TlsFree");
  M("kernel32.dll", "TlsGetValue");
  M("kernel32.dll", "TlsSetValue");
  M("kernel32.dll", "TryEnterCriticalSection");
  M("kernel32.dll", "UnhandledExceptionFilter");
  M("kernel32.dll", "UnmapViewOfFile");
  M("kernel32.dll", "VirtualAlloc");
  M("kernel32.dll", "VirtualAllocEx");
  M("kernel32.dll", "VirtualFree");
  M("kernel32.dll", "VirtualFreeEx");
  M("kernel32.dll", "VirtualProtect");
  M("kernel32.dll", "VirtualProtectEx");
  M("kernel32.dll", "VirtualQuery");
  M("kernel32.dll", "VirtualQueryEx");
  M("kernel32.dll", "WaitForMultipleObjects");
  M("kernel32.dll", "WaitForMultipleObjectsEx");
  M("kernel32.dll", "WaitForSingleObject");
  M("kernel32.dll", "WaitForSingleObjectEx");
  M("kernel32.dll", "WideCharToMultiByte");
  M("kernel32.dll", "WriteConsoleA");
  M("kernel32.dll", "WriteConsoleW");
  M("kernel32.dll", "WriteFile");
  M("kernel32.dll", "WriteProcessMemory");
  M("kernel32.dll", "lstrlenA");
  M("kernel32.dll", "lstrlenW");
  M("kernel32.dll", "lstrcmpA");
  M("kernel32.dll", "lstrcmpW");
  M("kernel32.dll", "lstrcmpiA");
  M("kernel32.dll", "lstrcmpiW");
  M("kernel32.dll", "lstrcpyA");
  M("kernel32.dll", "lstrcpyW");
  M("kernel32.dll", "lstrcatA");
  M("kernel32.dll", "lstrcatW");

  // --- ntdll.dll ---
  M("ntdll.dll", "NtAllocateVirtualMemory");
  M("ntdll.dll", "NtClose");
  M("ntdll.dll", "NtCreateFile");
  M("ntdll.dll", "NtCreateSection");
  M("ntdll.dll", "NtCreateThreadEx");
  M("ntdll.dll", "NtDelayExecution");
  M("ntdll.dll", "NtDuplicateObject");
  M("ntdll.dll", "NtFreeVirtualMemory");
  M("ntdll.dll", "NtGetContextThread");
  M("ntdll.dll", "NtMapViewOfSection");
  M("ntdll.dll", "NtOpenFile");
  M("ntdll.dll", "NtOpenProcess");
  M("ntdll.dll", "NtOpenThread");
  M("ntdll.dll", "NtProtectVirtualMemory");
  M("ntdll.dll", "NtQueryInformationFile");
  M("ntdll.dll", "NtQueryInformationProcess");
  M("ntdll.dll", "NtQueryInformationThread");
  M("ntdll.dll", "NtQueryObject");
  M("ntdll.dll", "NtQuerySection");
  M("ntdll.dll", "NtQuerySystemInformation");
  M("ntdll.dll", "NtQueryValueKey");
  M("ntdll.dll", "NtQueryVirtualMemory");
  M("ntdll.dll", "NtReadFile");
  M("ntdll.dll", "NtReadVirtualMemory");
  M("ntdll.dll", "NtResumeThread");
  M("ntdll.dll", "NtSetContextThread");
  M("ntdll.dll", "NtSetInformationFile");
  M("ntdll.dll", "NtSetInformationProcess");
  M("ntdll.dll", "NtSetInformationThread");
  M("ntdll.dll", "NtSetValueKey");
  M("ntdll.dll", "NtSuspendThread");
  M("ntdll.dll", "NtTerminateProcess");
  M("ntdll.dll", "NtTerminateThread");
  M("ntdll.dll", "NtUnmapViewOfSection");
  M("ntdll.dll", "NtWaitForMultipleObjects");
  M("ntdll.dll", "NtWaitForSingleObject");
  M("ntdll.dll", "NtWriteFile");
  M("ntdll.dll", "NtWriteVirtualMemory");
  M("ntdll.dll", "RtlAddVectoredExceptionHandler");
  M("ntdll.dll", "RtlAllocateHeap");
  M("ntdll.dll", "RtlAnsiStringToUnicodeString");
  M("ntdll.dll", "RtlCompareMemory");
  M("ntdll.dll", "RtlCopyMemory");
  M("ntdll.dll", "RtlCreateHeap");
  M("ntdll.dll", "RtlDecompressBuffer");
  M("ntdll.dll", "RtlDestroyHeap");
  M("ntdll.dll", "RtlDosPathNameToNtPathName_U");
  M("ntdll.dll", "RtlExitUserThread");
  M("ntdll.dll", "RtlFreeHeap");
  M("ntdll.dll", "RtlFreeUnicodeString");
  M("ntdll.dll", "RtlGetVersion");
  M("ntdll.dll", "RtlInitAnsiString");
  M("ntdll.dll", "RtlInitUnicodeString");
  M("ntdll.dll", "RtlMoveMemory");
  M("ntdll.dll", "RtlNtStatusToDosError");
  M("ntdll.dll", "RtlReAllocateHeap");
  M("ntdll.dll", "RtlSizeHeap");
  M("ntdll.dll", "RtlUnicodeStringToAnsiString");
  M("ntdll.dll", "RtlZeroMemory");
  M("ntdll.dll", "DbgPrint");
  M("ntdll.dll", "DbgPrintEx");
  M("ntdll.dll", "LdrGetDllHandle");
  M("ntdll.dll", "LdrGetProcedureAddress");
  M("ntdll.dll", "LdrLoadDll");
  M("ntdll.dll", "NtCurrentTeb");
  M("ntdll.dll", "NtCurrentPeb");

  // --- user32.dll ---
  M("user32.dll", "AdjustWindowRect");
  M("user32.dll", "AdjustWindowRectEx");
  M("user32.dll", "BeginPaint");
  M("user32.dll", "BringWindowToTop");
  M("user32.dll", "CallWindowProcA");
  M("user32.dll", "CallWindowProcW");
  M("user32.dll", "CharLowerA");
  M("user32.dll", "CharUpperA");
  M("user32.dll", "ClientToScreen");
  M("user32.dll", "ClipCursor");
  M("user32.dll", "CreateWindowExA");
  M("user32.dll", "CreateWindowExW");
  M("user32.dll", "DefWindowProcA");
  M("user32.dll", "DefWindowProcW");
  M("user32.dll", "DestroyWindow");
  M("user32.dll", "DialogBoxParamA");
  M("user32.dll", "DialogBoxParamW");
  M("user32.dll", "DispatchMessageA");
  M("user32.dll", "DispatchMessageW");
  M("user32.dll", "EnableWindow");
  M("user32.dll", "EndDialog");
  M("user32.dll", "EndPaint");
  M("user32.dll", "EnumChildWindows");
  M("user32.dll", "EnumWindows");
  M("user32.dll", "FillRect");
  M("user32.dll", "FindWindowA");
  M("user32.dll", "FindWindowExA");
  M("user32.dll", "FindWindowExW");
  M("user32.dll", "FindWindowW");
  M("user32.dll", "GetAsyncKeyState");
  M("user32.dll", "GetClassNameA");
  M("user32.dll", "GetClassNameW");
  M("user32.dll", "GetClientRect");
  M("user32.dll", "GetClipboardData");
  M("user32.dll", "GetCursorPos");
  M("user32.dll", "GetDC");
  M("user32.dll", "GetDesktopWindow");
  M("user32.dll", "GetDlgItem");
  M("user32.dll", "GetDlgItemTextA");
  M("user32.dll", "GetDlgItemTextW");
  M("user32.dll", "GetForegroundWindow");
  M("user32.dll", "GetKeyState");
  M("user32.dll", "GetKeyboardState");
  M("user32.dll", "GetMessageA");
  M("user32.dll", "GetMessageW");
  M("user32.dll", "GetMonitorInfoA");
  M("user32.dll", "GetMonitorInfoW");
  M("user32.dll", "GetParent");
  M("user32.dll", "GetSystemMetrics");
  M("user32.dll", "GetWindow");
  M("user32.dll", "GetWindowLongA");
  M("user32.dll", "GetWindowLongPtrA");
  M("user32.dll", "GetWindowLongPtrW");
  M("user32.dll", "GetWindowLongW");
  M("user32.dll", "GetWindowRect");
  M("user32.dll", "GetWindowTextA");
  M("user32.dll", "GetWindowTextLengthA");
  M("user32.dll", "GetWindowTextLengthW");
  M("user32.dll", "GetWindowTextW");
  M("user32.dll", "GetWindowThreadProcessId");
  M("user32.dll", "InvalidateRect");
  M("user32.dll", "IsWindow");
  M("user32.dll", "IsWindowVisible");
  M("user32.dll", "KillTimer");
  M("user32.dll", "LoadCursorA");
  M("user32.dll", "LoadCursorW");
  M("user32.dll", "LoadIconA");
  M("user32.dll", "LoadIconW");
  M("user32.dll", "LoadStringA");
  M("user32.dll", "LoadStringW");
  M("user32.dll", "MapVirtualKeyA");
  M("user32.dll", "MapVirtualKeyW");
  M("user32.dll", "MessageBoxA");
  M("user32.dll", "MessageBoxExA");
  M("user32.dll", "MessageBoxExW");
  M("user32.dll", "MessageBoxW");
  M("user32.dll", "MonitorFromWindow");
  M("user32.dll", "MoveWindow");
  M("user32.dll", "PeekMessageA");
  M("user32.dll", "PeekMessageW");
  M("user32.dll", "PostMessageA");
  M("user32.dll", "PostMessageW");
  M("user32.dll", "PostQuitMessage");
  M("user32.dll", "RegisterClassA");
  M("user32.dll", "RegisterClassExA");
  M("user32.dll", "RegisterClassExW");
  M("user32.dll", "RegisterClassW");
  M("user32.dll", "RegisterHotKey");
  M("user32.dll", "RegisterWindowMessageA");
  M("user32.dll", "RegisterWindowMessageW");
  M("user32.dll", "ReleaseDC");
  M("user32.dll", "ScreenToClient");
  M("user32.dll", "SendDlgItemMessageA");
  M("user32.dll", "SendDlgItemMessageW");
  M("user32.dll", "SendInput");
  M("user32.dll", "SendMessageA");
  M("user32.dll", "SendMessageW");
  M("user32.dll", "SetCapture");
  M("user32.dll", "SetCursorPos");
  M("user32.dll", "SetDlgItemTextA");
  M("user32.dll", "SetDlgItemTextW");
  M("user32.dll", "SetFocus");
  M("user32.dll", "SetForegroundWindow");
  M("user32.dll", "SetLayeredWindowAttributes");
  M("user32.dll", "SetTimer");
  M("user32.dll", "SetWindowLongA");
  M("user32.dll", "SetWindowLongPtrA");
  M("user32.dll", "SetWindowLongPtrW");
  M("user32.dll", "SetWindowLongW");
  M("user32.dll", "SetWindowPos");
  M("user32.dll", "SetWindowTextA");
  M("user32.dll", "SetWindowTextW");
  M("user32.dll", "ShowCursor");
  M("user32.dll", "ShowWindow");
  M("user32.dll", "SystemParametersInfoA");
  M("user32.dll", "SystemParametersInfoW");
  M("user32.dll", "ToUnicode");
  M("user32.dll", "TranslateMessage");
  M("user32.dll", "UnregisterClassA");
  M("user32.dll", "UnregisterClassW");
  M("user32.dll", "UpdateWindow");
  M("user32.dll", "wsprintfA");
  M("user32.dll", "wsprintfW");

  // --- advapi32.dll ---
  M("advapi32.dll", "AdjustTokenPrivileges");
  M("advapi32.dll", "AllocateAndInitializeSid");
  M("advapi32.dll", "CheckTokenMembership");
  M("advapi32.dll", "ConvertSidToStringSidA");
  M("advapi32.dll", "ConvertSidToStringSidW");
  M("advapi32.dll", "ConvertStringSidToSidA");
  M("advapi32.dll", "ConvertStringSidToSidW");
  M("advapi32.dll", "CryptAcquireContextA");
  M("advapi32.dll", "CryptAcquireContextW");
  M("advapi32.dll", "CryptCreateHash");
  M("advapi32.dll", "CryptDecrypt");
  M("advapi32.dll", "CryptDeriveKey");
  M("advapi32.dll", "CryptDestroyHash");
  M("advapi32.dll", "CryptDestroyKey");
  M("advapi32.dll", "CryptEncrypt");
  M("advapi32.dll", "CryptGenRandom");
  M("advapi32.dll", "CryptGetHashParam");
  M("advapi32.dll", "CryptHashData");
  M("advapi32.dll", "CryptImportKey");
  M("advapi32.dll", "CryptReleaseContext");
  M("advapi32.dll", "DuplicateToken");
  M("advapi32.dll", "DuplicateTokenEx");
  M("advapi32.dll", "FreeSid");
  M("advapi32.dll", "GetTokenInformation");
  M("advapi32.dll", "GetUserNameA");
  M("advapi32.dll", "GetUserNameW");
  M("advapi32.dll", "ImpersonateLoggedOnUser");
  M("advapi32.dll", "InitializeSecurityDescriptor");
  M("advapi32.dll", "LookupAccountSidA");
  M("advapi32.dll", "LookupAccountSidW");
  M("advapi32.dll", "LookupPrivilegeValueA");
  M("advapi32.dll", "LookupPrivilegeValueW");
  M("advapi32.dll", "OpenProcessToken");
  M("advapi32.dll", "OpenThreadToken");
  M("advapi32.dll", "RegCloseKey");
  M("advapi32.dll", "RegCreateKeyA");
  M("advapi32.dll", "RegCreateKeyExA");
  M("advapi32.dll", "RegCreateKeyExW");
  M("advapi32.dll", "RegCreateKeyW");
  M("advapi32.dll", "RegDeleteKeyA");
  M("advapi32.dll", "RegDeleteKeyW");
  M("advapi32.dll", "RegDeleteValueA");
  M("advapi32.dll", "RegDeleteValueW");
  M("advapi32.dll", "RegEnumKeyExA");
  M("advapi32.dll", "RegEnumKeyExW");
  M("advapi32.dll", "RegEnumValueA");
  M("advapi32.dll", "RegEnumValueW");
  M("advapi32.dll", "RegGetValueA");
  M("advapi32.dll", "RegGetValueW");
  M("advapi32.dll", "RegOpenKeyA");
  M("advapi32.dll", "RegOpenKeyExA");
  M("advapi32.dll", "RegOpenKeyExW");
  M("advapi32.dll", "RegOpenKeyW");
  M("advapi32.dll", "RegQueryInfoKeyA");
  M("advapi32.dll", "RegQueryInfoKeyW");
  M("advapi32.dll", "RegQueryValueExA");
  M("advapi32.dll", "RegQueryValueExW");
  M("advapi32.dll", "RegSetValueExA");
  M("advapi32.dll", "RegSetValueExW");
  M("advapi32.dll", "RevertToSelf");
  M("advapi32.dll", "SetSecurityDescriptorDacl");
  M("advapi32.dll", "SetTokenInformation");
  M("advapi32.dll", "StartServiceA");
  M("advapi32.dll", "StartServiceW");

  // --- ws2_32.dll ---
  M("ws2_32.dll", "WSACleanup");
  M("ws2_32.dll", "WSAGetLastError");
  M("ws2_32.dll", "WSAStartup");
  M("ws2_32.dll", "accept");
  M("ws2_32.dll", "bind");
  M("ws2_32.dll", "closesocket");
  M("ws2_32.dll", "connect");
  M("ws2_32.dll", "getaddrinfo");
  M("ws2_32.dll", "freeaddrinfo");
  M("ws2_32.dll", "gethostbyname");
  M("ws2_32.dll", "gethostname");
  M("ws2_32.dll", "getpeername");
  M("ws2_32.dll", "getsockname");
  M("ws2_32.dll", "getsockopt");
  M("ws2_32.dll", "htonl");
  M("ws2_32.dll", "htons");
  M("ws2_32.dll", "inet_addr");
  M("ws2_32.dll", "inet_ntoa");
  M("ws2_32.dll", "ioctlsocket");
  M("ws2_32.dll", "listen");
  M("ws2_32.dll", "ntohl");
  M("ws2_32.dll", "ntohs");
  M("ws2_32.dll", "recv");
  M("ws2_32.dll", "recvfrom");
  M("ws2_32.dll", "select");
  M("ws2_32.dll", "send");
  M("ws2_32.dll", "sendto");
  M("ws2_32.dll", "setsockopt");
  M("ws2_32.dll", "shutdown");
  M("ws2_32.dll", "socket");

  // --- ole32.dll ---
  M("ole32.dll", "CoCreateInstance");
  M("ole32.dll", "CoInitialize");
  M("ole32.dll", "CoInitializeEx");
  M("ole32.dll", "CoInitializeSecurity");
  M("ole32.dll", "CoTaskMemAlloc");
  M("ole32.dll", "CoTaskMemFree");
  M("ole32.dll", "CoUninitialize");

  // --- shell32.dll ---
  M("shell32.dll", "CommandLineToArgvW");
  M("shell32.dll", "SHGetFolderPathA");
  M("shell32.dll", "SHGetFolderPathW");
  M("shell32.dll", "SHGetKnownFolderPath");
  M("shell32.dll", "SHGetSpecialFolderPathA");
  M("shell32.dll", "SHGetSpecialFolderPathW");
  M("shell32.dll", "ShellExecuteA");
  M("shell32.dll", "ShellExecuteExA");
  M("shell32.dll", "ShellExecuteExW");
  M("shell32.dll", "ShellExecuteW");

  // --- crypt32.dll ---
  M("crypt32.dll", "CertCloseStore");
  M("crypt32.dll", "CertFindCertificateInStore");
  M("crypt32.dll", "CertFreeCertificateContext");
  M("crypt32.dll", "CertGetCertificateChain");
  M("crypt32.dll", "CertOpenStore");
  M("crypt32.dll", "CertOpenSystemStoreA");
  M("crypt32.dll", "CertOpenSystemStoreW");
  M("crypt32.dll", "CryptBinaryToStringA");
  M("crypt32.dll", "CryptBinaryToStringW");
  M("crypt32.dll", "CryptDecodeObjectEx");
  M("crypt32.dll", "CryptProtectData");
  M("crypt32.dll", "CryptStringToBinaryA");
  M("crypt32.dll", "CryptStringToBinaryW");
  M("crypt32.dll", "CryptUnprotectData");

  // --- winhttp.dll ---
  M("winhttp.dll", "WinHttpCloseHandle");
  M("winhttp.dll", "WinHttpConnect");
  M("winhttp.dll", "WinHttpCrackUrl");
  M("winhttp.dll", "WinHttpOpen");
  M("winhttp.dll", "WinHttpOpenRequest");
  M("winhttp.dll", "WinHttpQueryDataAvailable");
  M("winhttp.dll", "WinHttpQueryHeaders");
  M("winhttp.dll", "WinHttpReadData");
  M("winhttp.dll", "WinHttpReceiveResponse");
  M("winhttp.dll", "WinHttpSendRequest");
  M("winhttp.dll", "WinHttpSetOption");
  M("winhttp.dll", "WinHttpSetTimeouts");
  M("winhttp.dll", "WinHttpWriteData");

  // --- wininet.dll ---
  M("wininet.dll", "HttpOpenRequestA");
  M("wininet.dll", "HttpOpenRequestW");
  M("wininet.dll", "HttpQueryInfoA");
  M("wininet.dll", "HttpQueryInfoW");
  M("wininet.dll", "HttpSendRequestA");
  M("wininet.dll", "HttpSendRequestW");
  M("wininet.dll", "InternetCloseHandle");
  M("wininet.dll", "InternetConnectA");
  M("wininet.dll", "InternetConnectW");
  M("wininet.dll", "InternetOpenA");
  M("wininet.dll", "InternetOpenUrlA");
  M("wininet.dll", "InternetOpenUrlW");
  M("wininet.dll", "InternetOpenW");
  M("wininet.dll", "InternetReadFile");
  M("wininet.dll", "InternetSetOptionA");
  M("wininet.dll", "InternetSetOptionW");
  M("wininet.dll", "InternetWriteFile");

  // --- bcrypt.dll ---
  M("bcrypt.dll", "BCryptCloseAlgorithmProvider");
  M("bcrypt.dll", "BCryptCreateHash");
  M("bcrypt.dll", "BCryptDecrypt");
  M("bcrypt.dll", "BCryptDestroyHash");
  M("bcrypt.dll", "BCryptDestroyKey");
  M("bcrypt.dll", "BCryptEncrypt");
  M("bcrypt.dll", "BCryptFinishHash");
  M("bcrypt.dll", "BCryptGenRandom");
  M("bcrypt.dll", "BCryptGenerateSymmetricKey");
  M("bcrypt.dll", "BCryptGetProperty");
  M("bcrypt.dll", "BCryptHashData");
  M("bcrypt.dll", "BCryptImportKey");
  M("bcrypt.dll", "BCryptOpenAlgorithmProvider");
  M("bcrypt.dll", "BCryptSetProperty");

  // --- gdi32.dll ---
  M("gdi32.dll", "BitBlt");
  M("gdi32.dll", "CreateCompatibleBitmap");
  M("gdi32.dll", "CreateCompatibleDC");
  M("gdi32.dll", "CreateDCA");
  M("gdi32.dll", "CreateDCW");
  M("gdi32.dll", "CreateFontA");
  M("gdi32.dll", "CreateFontW");
  M("gdi32.dll", "CreatePen");
  M("gdi32.dll", "CreateSolidBrush");
  M("gdi32.dll", "DeleteDC");
  M("gdi32.dll", "DeleteObject");
  M("gdi32.dll", "GetDIBits");
  M("gdi32.dll", "GetDeviceCaps");
  M("gdi32.dll", "GetObjectA");
  M("gdi32.dll", "GetObjectW");
  M("gdi32.dll", "GetStockObject");
  M("gdi32.dll", "SelectObject");
  M("gdi32.dll", "SetBkColor");
  M("gdi32.dll", "SetBkMode");
  M("gdi32.dll", "SetTextColor");
  M("gdi32.dll", "StretchBlt");
  M("gdi32.dll", "TextOutA");
  M("gdi32.dll", "TextOutW");

  // --- shlwapi.dll ---
  M("shlwapi.dll", "PathAppendA");
  M("shlwapi.dll", "PathAppendW");
  M("shlwapi.dll", "PathCombineA");
  M("shlwapi.dll", "PathCombineW");
  M("shlwapi.dll", "PathFileExistsA");
  M("shlwapi.dll", "PathFileExistsW");
  M("shlwapi.dll", "PathFindExtensionA");
  M("shlwapi.dll", "PathFindExtensionW");
  M("shlwapi.dll", "PathFindFileNameA");
  M("shlwapi.dll", "PathFindFileNameW");
  M("shlwapi.dll", "PathRemoveFileSpecA");
  M("shlwapi.dll", "PathRemoveFileSpecW");
  M("shlwapi.dll", "StrCmpIA");
  M("shlwapi.dll", "StrCmpIW");
  M("shlwapi.dll", "StrStrIA");
  M("shlwapi.dll", "StrStrIW");

  // --- msvcrt.dll ---
  M("msvcrt.dll", "malloc");
  M("msvcrt.dll", "calloc");
  M("msvcrt.dll", "realloc");
  M("msvcrt.dll", "free");
  M("msvcrt.dll", "memcpy");
  M("msvcrt.dll", "memset");
  M("msvcrt.dll", "memmove");
  M("msvcrt.dll", "memcmp");
  M("msvcrt.dll", "strlen");
  M("msvcrt.dll", "strcmp");
  M("msvcrt.dll", "strncmp");
  M("msvcrt.dll", "strcpy");
  M("msvcrt.dll", "strncpy");
  M("msvcrt.dll", "strcat");
  M("msvcrt.dll", "strncat");
  M("msvcrt.dll", "strstr");
  M("msvcrt.dll", "strchr");
  M("msvcrt.dll", "strrchr");
  M("msvcrt.dll", "sprintf");
  M("msvcrt.dll", "snprintf");
  M("msvcrt.dll", "sscanf");
  M("msvcrt.dll", "printf");
  M("msvcrt.dll", "fprintf");
  M("msvcrt.dll", "fopen");
  M("msvcrt.dll", "fclose");
  M("msvcrt.dll", "fread");
  M("msvcrt.dll", "fwrite");
  M("msvcrt.dll", "fseek");
  M("msvcrt.dll", "ftell");
  M("msvcrt.dll", "fflush");
  M("msvcrt.dll", "atoi");
  M("msvcrt.dll", "atol");
  M("msvcrt.dll", "strtol");
  M("msvcrt.dll", "strtoul");
  M("msvcrt.dll", "wcslen");
  M("msvcrt.dll", "wcscpy");
  M("msvcrt.dll", "wcscat");
  M("msvcrt.dll", "wcscmp");
  M("msvcrt.dll", "_wfopen");
  M("msvcrt.dll", "_stricmp");
  M("msvcrt.dll", "_wcsicmp");
  M("msvcrt.dll", "_snprintf");
  M("msvcrt.dll", "_vsnprintf");
  M("msvcrt.dll", "_vsnwprintf");

  // --- ucrtbase.dll ---
  M("ucrtbase.dll", "malloc");
  M("ucrtbase.dll", "calloc");
  M("ucrtbase.dll", "realloc");
  M("ucrtbase.dll", "free");
  M("ucrtbase.dll", "memcpy");
  M("ucrtbase.dll", "memset");
  M("ucrtbase.dll", "memmove");
  M("ucrtbase.dll", "memcmp");
  M("ucrtbase.dll", "strlen");
  M("ucrtbase.dll", "strcmp");
  M("ucrtbase.dll", "strcpy");
  M("ucrtbase.dll", "strcat");

  // --- iphlpapi.dll ---
  M("iphlpapi.dll", "GetAdaptersAddresses");
  M("iphlpapi.dll", "GetAdaptersInfo");
  M("iphlpapi.dll", "GetBestInterface");
  M("iphlpapi.dll", "GetIpAddrTable");
  M("iphlpapi.dll", "GetNetworkParams");

  // --- psapi.dll ---
  M("psapi.dll", "EnumProcessModules");
  M("psapi.dll", "EnumProcessModulesEx");
  M("psapi.dll", "EnumProcesses");
  M("psapi.dll", "GetModuleBaseNameA");
  M("psapi.dll", "GetModuleBaseNameW");
  M("psapi.dll", "GetModuleFileNameExA");
  M("psapi.dll", "GetModuleFileNameExW");
  M("psapi.dll", "GetModuleInformation");
  M("psapi.dll", "GetProcessMemoryInfo");

  // --- dbghelp.dll ---
  M("dbghelp.dll", "MiniDumpWriteDump");
  M("dbghelp.dll", "StackWalk64");
  M("dbghelp.dll", "SymCleanup");
  M("dbghelp.dll", "SymFromAddr");
  M("dbghelp.dll", "SymGetLineFromAddr64");
  M("dbghelp.dll", "SymInitialize");
  M("dbghelp.dll", "SymSetOptions");
  M("dbghelp.dll", "UnDecorateSymbolName");

#undef M
}

}  // namespace omill
