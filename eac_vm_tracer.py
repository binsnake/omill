#!/usr/bin/env python3
"""
EasyAntiCheat VM Tracer
========================
Traces the hash/overflow-based virtual machine dispatcher in
EasyAntiCheat_EOS.sys.

Dispatch resolution formula
----------------------------
    base_delta = imagebase + 0x2F09 = 0x140002F09
    target     = constant + base_delta

8266 dispatch stubs extracted and resolved statically (7393 hash-only, 873 with extras).

VM architecture
---------------
    VM Context: 0x1A0-byte struct on stack, R12 = base pointer.
    Hash/IP:    [R12+0x190] -- each stub writes a unique 64-bit hash.
    Extra:      [R12+0x198] -- per-stub auxiliary value (873 stubs set this).
    base_delta: [R12+0xE0]  -- imagebase + 0x2F09 (constant after VM setup).
    VM Exit:    sub_1402A112B restores all registers and returns.

    Handler flow:
        HANDLER_BODY -> jmp rax/rdx -> DISPATCH_STUB
        DISPATCH_STUB:
            mov rax, <hash64>            ; unique 64-bit hash per stub
            mov [r12+190h], rax
           [mov rax, <extra64>           ; optional extra field (873 stubs)
            mov [r12+198h], rax]
            mov eax, <const32>           ; handler selector constant
            add rax, [r12+0E0h]          ; + base_delta = target VA
            jmp rax                      ; -> thunk -> next handler

    Dispatch targets:
        All targets land in a thunk section (0x1402A1000-0x14033D000) that
        jmp-redirects to the actual handler body in seg006 (0x1402A1000-0x14266F000).

    Stats: 8266 stubs, 4178 unique targets, 8266 unique hashes.
    Handler exit stubs are NOT spatially adjacent to their handler body --
    the opaque predicate can dispatch to stubs anywhere in seg006.

    Emulation limitation: handler payloads dereference pointers computed from
    register context values. Without correct initial register state, these
    produce invalid addresses. The dispatch resolution is fully static, but
    tracing the live hash chain requires emulation with valid context data.
"""

import struct
import json
import sys
import time
import re
from pathlib import Path
from collections import defaultdict

import pefile
from unicorn import *
from unicorn.x86_const import *
from capstone import Cs, CS_ARCH_X86, CS_MODE_64

# -- Constants ----------------------------------------------------------------
BINARY_PATH  = Path(r"D:\binsnake\omill\build-remill\tools\omill-lift\EasyAntiCheat_EOS.sys")
STUBS_JSON   = Path(r"D:\binsnake\tracer\dispatch_stubs.json")

IMAGEBASE    = 0x140000000
VM_ENTRY     = 0x14030FDD0
DRIVER_ENTRY = 0x14019DA10
VM_SETUP     = 0x1402A1000
VM_EXIT      = 0x1402A112B
BASE_DELTA   = 0x140002F09
INITIAL_HASH = 0xA26346B5C9C0B6DB
ENTRY_CONST  = 0x2C6386

DISPATCH_SIG = b'\x49\x03\x84\x24\xE0\x00\x00\x00'  # add rax,[r12+0E0h]
# Middle of native call stub: lea rsp,[rsp+1C0h]; call [rsp+8]; lea rsp,[rsp-1C0h]
NATIVE_CALL_MID = b'\x48\x8D\xA4\x24\xC0\x01\x00\x00\xFF\x54\x24\x08\x48\x8D\xA4\x24\x40\xFE\xFF\xFF'
NATIVE_STUB_SIZE = 35  # call vmexit(5) + lea(8) + call[rsp+8](4) + lea(8) + call vmenter(5) + jmp(5)

STACK_BASE   = 0x00007FFE_00000000
STACK_SIZE   = 0x800000
DRIVER_OBJ   = 0x00000001_00000000
REG_PATH     = 0x00000002_00000000
STUB_BASE    = 0xFFFF0000

# KUSER_SHARED_DATA -- kernel VA 0xFFFFF78000000000.
# Unicorn truncates the 64-bit canonical address; the handler's obfuscated
# pointer computation produces 0xFF78000000000 as the effective base.
KUSER_SHARED_DATA = 0xFF78000000000
KUSD_PAGE_SIZE    = 0x1000

CTX_OFF = {
    'xmm7':0x00,  'xmm11':0x10, 'xmm9':0x20,  'rbp':0x30,
    'rdx':0x38,   'rbx':0x40,   'xmm1':0x48,   'xmm0':0x58,
    'xmm12':0x68, 'r8':0x78,    'r9':0x80,     'r13':0x88,
    'rcx':0x90,   'r12':0x98,   'xmm14':0xA0,  'rflags':0xB0,
    'rsp':0xB8,   'xmm3':0xC0,  'xmm15':0xD0,  'base':0xE0,
    'xmm5':0xE8,  'xmm2':0xF8,  'rax':0x108,   'r14':0x110,
    'xmm8':0x118, 'rsi':0x128,  'xmm10':0x130, 'r15':0x140,
    'xmm6':0x148, 'r10':0x158,  'xmm4':0x160,  'rdi':0x170,
    'xmm13':0x178,'r11':0x188,  'hash':0x190,  'extra':0x198,
}

GPR_NAMES = ['rax','rbx','rcx','rdx','rsp','rbp','rsi','rdi',
             'r8','r9','r10','r11','r12','r13','r14','r15']
WATCHED_GLOBALS = {
    0x140225720: 'slot_140225720',
    0x1402264D0: 'slot_1402264D0',
    0x1402264F0: 'slot_1402264F0',
    0x140226500: 'slot_140226500',
    0x140270CE0: 'qword_140270CE0',
    0x140277BC8: 'qword_140277BC8',
}
WATCHED_PAGES = {
    0x140225000,
    0x140226000,
    0x140270000,
    0x140277000,
}
PRIVILEGED_MNEMONICS = {
    'cli', 'sti', 'hlt', 'swapgs',
    'rdmsr', 'wrmsr', 'rdpmc', 'rdtsc', 'rdtscp',
    'xgetbv', 'xsetbv',
    'sgdt', 'sidt', 'sldt', 'str', 'smsw', 'lmsw',
    'in', 'insb', 'insd', 'insw', 'out', 'outsb', 'outsd', 'outsw',
}
SPECIAL_REG_TOKEN_RE = re.compile(r'\b(?:cr\d+|dr\d+|tr\d+|msr)\b')
NATIVE_PROBE_EXTRA_PAGES = {
    0x1401660E0: [
        0x140270CE0 & ~0xFFF,
        0x140277BC8 & ~0xFFF,
    ],
}

UC_REG_BY_NAME = {
    'rax': UC_X86_REG_RAX,
    'rbx': UC_X86_REG_RBX,
    'rcx': UC_X86_REG_RCX,
    'rdx': UC_X86_REG_RDX,
    'rsp': UC_X86_REG_RSP,
    'rbp': UC_X86_REG_RBP,
    'rsi': UC_X86_REG_RSI,
    'rdi': UC_X86_REG_RDI,
    'r8': UC_X86_REG_R8,
    'r9': UC_X86_REG_R9,
    'r10': UC_X86_REG_R10,
    'r11': UC_X86_REG_R11,
    'r12': UC_X86_REG_R12,
    'r13': UC_X86_REG_R13,
    'r14': UC_X86_REG_R14,
    'r15': UC_X86_REG_R15,
}

VM_DISPATCH_LOOP = 0x1402A1318
VM_DISPATCH_JMP  = 0x1402A1366

# Known giant loop heads that are safe to summarize with the isolated resolver
# and then skip back into the live Unicorn VM at their resolved continuation.
JIT_OUTLINE_LOOP_HEADS = {
    0x14170D5A2,
}

OUTLINE_LIVE_MAX_INSNS = 250_000
OUTLINE_SYNTH_MAX_INSNS = 250_000


# =============================================================================
#  Static Dispatch Database
# =============================================================================

class DispatchDB:
    """
    Static database of all VM dispatch stubs extracted from the binary.

    Two stub forms:
        Hash-only (7393):  mov rax,H; mov [r12+190h],rax; mov eax,C; <dispatch>
        Hash+extra (873):  mov rax,H; mov [r12+190h],rax;
                           mov rax,E; mov [r12+198h],rax; mov eax,C; <dispatch>

    Every hash is globally unique across all 8266 stubs.
    """

    def __init__(self, stubs_path=None, pe_path=None):
        self.stubs = []
        self.by_hash = {}
        self.by_target = defaultdict(list)
        self.by_thunk = defaultdict(list)

        if stubs_path and stubs_path.exists():
            self._load_json(stubs_path)
        elif pe_path and pe_path.exists():
            self._extract_from_pe(pe_path)
        else:
            print("[!] No stub database found.")
            return
        self._index()

    def _load_json(self, path):
        with open(path) as f:
            raw = json.load(f)
        for r in raw:
            self.stubs.append({
                'stub_addr': int(r['stub_addr'], 16),
                'hash':  int(r['hash'], 16) if r.get('hash') else None,
                'extra': int(r['extra'], 16) if r.get('extra') else None,
                'const': int(r['const'], 16),
                'target': int(r['target'], 16),
                'thunk_target': int(r['thunk_target'], 16) if r.get('thunk_target') else None,
            })

    def _extract_from_pe(self, pe_path):
        pe = pefile.PE(str(pe_path))
        hash_store = b'\x49\x89\x84\x24\x90\x01\x00\x00'
        extra_store = b'\x49\x89\x84\x24\x98\x01\x00\x00'
        dispatch    = b'\x49\x03\x84\x24\xe0\x00\x00\x00\xff\xe0'

        for sec in pe.sections:
            va = IMAGEBASE + sec.VirtualAddress
            data = sec.get_data()
            pos = 0
            while pos < len(data) - 30:
                idx = data.find(hash_store, pos)
                if idx == -1:
                    break

                after = idx + 8
                if after + 15 > len(data):
                    pos = idx + 1
                    continue

                hash_val = extra_val = None
                const_val = None
                stub_start = None

                if data[after] == 0xB8:
                    # Hash-only
                    const_val = struct.unpack_from('<I', data, after + 1)[0]
                    if data[after+5:after+15] != dispatch:
                        pos = idx + 1
                        continue
                    if idx >= 10 and data[idx-10] == 0x48 and data[idx-9] == 0xB8:
                        hash_val = struct.unpack_from('<Q', data, idx-8)[0]
                        stub_start = va + idx - 10
                    else:
                        stub_start = va + idx
                elif (after + 1 < len(data) and
                      data[after] == 0x48 and data[after+1] == 0xB8):
                    # Hash+extra
                    if after + 26 > len(data):
                        pos = idx + 1
                        continue
                    extra_val = struct.unpack_from('<Q', data, after + 2)[0]
                    es_pos = after + 10
                    if data[es_pos:es_pos+8] != extra_store:
                        pos = idx + 1
                        continue
                    c_pos = es_pos + 8
                    if data[c_pos] != 0xB8:
                        pos = idx + 1
                        continue
                    const_val = struct.unpack_from('<I', data, c_pos + 1)[0]
                    if data[c_pos+5:c_pos+15] != dispatch:
                        pos = idx + 1
                        continue
                    if idx >= 10 and data[idx-10] == 0x48 and data[idx-9] == 0xB8:
                        hash_val = struct.unpack_from('<Q', data, idx-8)[0]
                        stub_start = va + idx - 10
                    else:
                        stub_start = va + idx
                else:
                    pos = idx + 1
                    continue

                target = const_val + BASE_DELTA
                thunk_target = None
                t_off = target - va
                if 0 <= t_off < len(data) and data[t_off] == 0xE9:
                    rel32 = struct.unpack_from('<i', data, t_off + 1)[0]
                    thunk_target = target + 5 + rel32

                self.stubs.append({
                    'stub_addr': stub_start,
                    'hash': hash_val,
                    'extra': extra_val,
                    'const': const_val,
                    'target': target,
                    'thunk_target': thunk_target,
                })
                pos = idx + 1
        print(f"  Extracted {len(self.stubs)} stubs from PE")

    def _index(self):
        self.by_stub_addr = {}
        for s in self.stubs:
            if s['hash'] is not None:
                self.by_hash[s['hash']] = s
            self.by_target[s['target']].append(s)
            self.by_stub_addr[s['stub_addr']] = s
            if s.get('thunk_target'):
                self.by_thunk[s['thunk_target']].append(s)

    def resolve(self, constant):
        return constant + BASE_DELTA

    def lookup_hash(self, hash_val):
        return self.by_hash.get(hash_val)

    def stubs_for_handler(self, handler_va):
        """Find all stubs that dispatch TO a given handler VA."""
        return self.by_thunk.get(handler_va, [])

    def print_summary(self):
        n_extra = sum(1 for s in self.stubs if s.get('extra') is not None)
        n_targets = len(self.by_target)
        n_handlers = len(self.by_thunk)
        print(f"\n{'='*70}")
        print(f" Dispatch Stub Database")
        print(f"{'='*70}")
        print(f" Total stubs:      {len(self.stubs):>6d}")
        print(f"   hash-only:      {len(self.stubs) - n_extra:>6d}")
        print(f"   hash+extra:     {n_extra:>6d}")
        print(f" Unique hashes:    {len(self.by_hash):>6d}")
        print(f" Unique targets:   {n_targets:>6d}")
        print(f" Handler VAs:      {n_handlers:>6d}")
        print(f" Base delta:       0x{BASE_DELTA:X}")
        print(f" Formula:          target = const + 0x{BASE_DELTA:X}")
        print(f"{'='*70}")


# =============================================================================
#  Unicorn-based VM Emulator/Tracer
# =============================================================================

class VMTracer:
    def __init__(self, pe_path, db, verbose=2, resolver=None, outline_loop_heads=None):
        self.verbose = verbose
        self.db = db
        self.resolver = resolver
        self.pe = pefile.PE(pe_path)
        self.mu = Uc(UC_ARCH_X86, UC_MODE_64)
        self.cs = Cs(CS_ARCH_X86, CS_MODE_64)

        self.step = 0
        self.max_steps = 500
        self.trace = []
        self.insn_count = 0
        self.auto_mapped = set()
        self.skip_count = 0
        self.pe_mapped_ranges = []  # [(start, end), ...] for legit PE sections

        # Native call stub tracking
        self.in_native_stub = False       # currently inside a native call stub
        self.native_stub_addr = 0         # start address of current native stub
        self.native_call_addr = 0         # address of call [rsp+8] inside stub
        self.pending_native_target = 0    # resolved native function VA
        self.native_calls = []            # list of {step, native_target_va, stub_addr}

        # VM nesting depth: incremented at VM_SETUP entry, decremented at
        # non-transient vmexit.  Only depth==1 is the final (outer VM) exit.
        self.vm_depth = 0
        self.final_vmexit_seen = False
        self.post_dispatch_targets = []
        self.outline_loop_heads = set(outline_loop_heads or JIT_OUTLINE_LOOP_HEADS)
        self.outline_attempted = set()
        self.outline_hits = 0
        self.outline_failures = 0
        self.watched_mem_events = []
        self._watched_mem_seen = set()
        self.privileged_insn_events = []
        self._privileged_insn_seen = set()

        self._map_pe()
        self._setup()

    def _record_watched_mem(self, access, address, size, value, rip):
        page = address & ~0xFFF
        if address not in WATCHED_GLOBALS and page not in WATCHED_PAGES:
            return
        key = (access, address, size, value, rip)
        if key in self._watched_mem_seen:
            return
        self._watched_mem_seen.add(key)
        event = {
            'access': access,
            'address': address,
            'size': size,
            'value': value,
            'rip': rip,
            'label': WATCHED_GLOBALS.get(address, ''),
        }
        self.watched_mem_events.append(event)
        if self.verbose >= 1:
            atype = {
                UC_MEM_READ: 'READ',
                UC_MEM_WRITE: 'WRITE',
            }.get(access, f'ACC{access}')
            label = f" {event['label']}" if event['label'] else ''
            print(f'  [watch] {atype}{label} addr=0x{address:X} size={size} value=0x{value:X} rip=0x{rip:X}')

    def _hook_mem_access(self, uc, access, address, size, value, _):
        rip = uc.reg_read(UC_X86_REG_RIP)
        self._record_watched_mem(access, address, size, value, rip)
        return True

    def _maybe_log_special_insn(self, uc, insn):
        ops = insn.op_str or ''
        mn = insn.mnemonic.lower()
        if mn not in PRIVILEGED_MNEMONICS and not SPECIAL_REG_TOKEN_RE.search(ops.lower()):
            return
        key = (insn.address, mn, ops)
        if key in self._privileged_insn_seen:
            return
        self._privileged_insn_seen.add(key)
        event = {
            'rip': insn.address,
            'mnemonic': insn.mnemonic,
            'op_str': insn.op_str,
        }
        self.privileged_insn_events.append(event)
        if self.verbose >= 1:
            print(f"  [cpu] 0x{insn.address:X}: {insn.mnemonic} {insn.op_str}")

    def _clone_runtime_regions(self, uc):
        regions = []

        def _append_region(base, size):
            try:
                regions.append({
                    'base': base,
                    'size': size,
                    'data': bytes(uc.mem_read(base, size)),
                })
            except:
                pass

        seen = set()
        for base, size in (
            (DRIVER_OBJ, 0x10000),
            (REG_PATH, 0x10000),
            (STUB_BASE, 0x10000),
            (KUSER_SHARED_DATA, KUSD_PAGE_SIZE),
        ):
            key = (base, size)
            if key in seen:
                continue
            seen.add(key)
            _append_region(base, size)

        for page in sorted(self.auto_mapped):
            key = (page, 0x1000)
            if key in seen:
                continue
            seen.add(key)
            _append_region(page, 0x1000)

        return regions

    def _capture_native_call_snapshot(self, uc, native_target, stub_addr=0,
                                      call_addr=0, source='live_stub',
                                      handler_after=0):
        try:
            regs = {name: uc.reg_read(reg) for name, reg in UC_REG_BY_NAME.items()}
            eflags = uc.reg_read(UC_X86_REG_EFLAGS)
            rsp_pre_call = regs['rsp']
            stack_base = max(rsp_pre_call - 0x40, STACK_BASE)
            stack_size = min(0x200, STACK_BASE + STACK_SIZE - stack_base)
            stack_bytes = bytes(uc.mem_read(stack_base, stack_size))
            snapshot = {
                'source': source,
                'native_target_va': native_target,
                'stub_addr': stub_addr,
                'call_addr': call_addr,
                'handler_after_va': handler_after,
                'regs': regs,
                'eflags': eflags,
                'rsp_pre_call': rsp_pre_call,
                'entry_rsp': (rsp_pre_call - 8) & 0xFFFFFFFFFFFFFFFF,
                'stack_base': stack_base,
                'stack_bytes': stack_bytes.hex(),
                'runtime_regions': self._clone_runtime_regions(uc),
            }
            return snapshot
        except:
            return None

    def _clone_native_probe_pages(self, uc, native_target):
        regions = []
        seen = set()
        for page in NATIVE_PROBE_EXTRA_PAGES.get(native_target, []):
            if page in seen:
                continue
            seen.add(page)
            try:
                regions.append({
                    'base': page,
                    'size': 0x1000,
                    'data': bytes(uc.mem_read(page, 0x1000)),
                })
            except:
                pass
        return regions

    def _synthesize_native_call_snapshot(self, ctx_bytes, native_target,
                                         stub_addr=0, handler_after=0,
                                         source='outlined_ctx',
                                         runtime_regions=None):
        if ctx_bytes is None:
            return None
        try:
            regs = {}
            for name in GPR_NAMES:
                regs[name] = struct.unpack(
                    '<Q',
                    ctx_bytes[CTX_OFF[name]:CTX_OFF[name] + 8])[0]
            original_rsp = regs['rsp']
            entry_rsp = (original_rsp - 8) & 0xFFFFFFFFFFFFFFFF
            stack_base = max(entry_rsp - 0x40, STACK_BASE)
            stack_span = min(0x200, STACK_BASE + STACK_SIZE - stack_base)
            stack = bytearray(stack_span)
            ret_sentinel = 0xDEADDEADDEADDEAD
            if stack_base <= entry_rsp < stack_base + stack_span:
                off = entry_rsp - stack_base
                struct.pack_into('<Q', stack, off, ret_sentinel)
            snapshot = {
                'source': source,
                'native_target_va': native_target,
                'stub_addr': stub_addr,
                'call_addr': 0,
                'handler_after_va': handler_after,
                'regs': regs,
                'eflags': struct.unpack(
                    '<Q',
                    ctx_bytes[CTX_OFF['rflags']:CTX_OFF['rflags'] + 8])[0],
                'rsp_pre_call': original_rsp,
                'entry_rsp': entry_rsp,
                'stack_base': stack_base,
                'stack_bytes': bytes(stack).hex(),
                'runtime_regions': list(runtime_regions or []),
            }
            return snapshot
        except:
            return None

    def _capture_vm_snapshot(self, uc):
        """Capture the live VM context at handler entry for targeted re-resolution."""
        try:
            r12 = uc.reg_read(UC_X86_REG_R12)
            rsp = uc.reg_read(UC_X86_REG_RSP)
            ctx_size = getattr(self.resolver, 'CTX_SIZE', 0x1A0) if self.resolver else 0x1A0
            ctx_bytes = bytes(uc.mem_read(r12, ctx_size))
            stack_bytes = bytes(uc.mem_read(rsp, min(0x200, 0x1000)))
            return {
                'r12': r12,
                'rsp': rsp,
                'ctx': ctx_bytes,
                'stack': stack_bytes,
            }
        except:
            return None

    def _map_pe(self):
        for sec in self.pe.sections:
            va = IMAGEBASE + sec.VirtualAddress
            data = sec.get_data()
            vsize = max(sec.Misc_VirtualSize, len(data))
            size = (vsize + 0xFFF) & ~0xFFF
            if size == 0:
                size = 0x1000
            self.mu.mem_map(va, size)
            self.mu.mem_write(va, data[:vsize])
            self.pe_mapped_ranges.append((va, va + size))

        self.mu.mem_map(STACK_BASE, STACK_SIZE)
        self.mu.mem_map(DRIVER_OBJ, 0x10000)
        self.mu.mem_map(REG_PATH, 0x10000)
        self.mu.mem_map(STUB_BASE, 0x10000)

        # KUSER_SHARED_DATA -- pre-map at the canonical kernel VA.
        # Handlers read SystemTime (offset 0x14) etc. via obfuscated pointers.
        self.mu.mem_map(KUSER_SHARED_DATA, KUSD_PAGE_SIZE)
        kusd = bytearray(KUSD_PAGE_SIZE)
        # SystemTime at offset 0x14 (KSYSTEM_TIME: LowPart u32, High1Time i32, High2Time i32)
        # Use a plausible FILETIME: ~2024-01-01 00:00 UTC = 0x01DA5E9847800000
        filetime = 0x01DA5E9847800000
        struct.pack_into('<I', kusd, 0x14, filetime & 0xFFFFFFFF)        # LowPart
        struct.pack_into('<i', kusd, 0x18, (filetime >> 32) & 0xFFFFFFFF)  # High1Time
        struct.pack_into('<i', kusd, 0x1C, (filetime >> 32) & 0xFFFFFFFF)  # High2Time
        # InterruptTime at offset 0x08 (same format)
        struct.pack_into('<I', kusd, 0x08, filetime & 0xFFFFFFFF)
        struct.pack_into('<i', kusd, 0x0C, (filetime >> 32) & 0xFFFFFFFF)
        struct.pack_into('<i', kusd, 0x10, (filetime >> 32) & 0xFFFFFFFF)
        # NtMajorVersion (0x26C) = 10, NtMinorVersion (0x270) = 0
        struct.pack_into('<I', kusd, 0x26C, 10)
        struct.pack_into('<I', kusd, 0x270, 0)
        self.mu.mem_write(KUSER_SHARED_DATA, bytes(kusd))

        for off in range(0, 0x2000, 8):
            self.mu.mem_write(DRIVER_OBJ + off,
                              struct.pack('<Q', 0xDEAD000000000000 | off))

        # Import stubs: FltRegisterFilter returns 0 (ret), __chkstk is nop (ret)
        self.mu.mem_write(STUB_BASE, b'\xC3')
        self.mu.mem_write(STUB_BASE + 0x10, b'\x31\xC0\xC3')
        self.mu.mem_write(0x14019E000, struct.pack('<Q', STUB_BASE + 0x10))
        self.mu.mem_write(0x14019E010, struct.pack('<Q', STUB_BASE))

        # Security cookie
        cookie = 0xDEADBEEFCAFEBABE
        self.mu.mem_write(0x140221028, struct.pack('<Q', cookie))
        self.mu.mem_write(0x140221030, struct.pack('<Q', (~cookie) & 0xFFFFFFFFFFFFFFFF))

    def _setup(self):
        rsp = STACK_BASE + STACK_SIZE - 0x8000
        rsp -= 8
        self.mu.mem_write(rsp, struct.pack('<Q', 0xDEADDEADDEADDEAD))

        self.mu.reg_write(UC_X86_REG_RSP, rsp)
        self.mu.reg_write(UC_X86_REG_RCX, DRIVER_OBJ)
        self.mu.reg_write(UC_X86_REG_RDX, REG_PATH)
        for reg in [UC_X86_REG_RAX, UC_X86_REG_RBX, UC_X86_REG_RSI,
                    UC_X86_REG_RDI, UC_X86_REG_R8, UC_X86_REG_R9,
                    UC_X86_REG_R10, UC_X86_REG_R11, UC_X86_REG_R12,
                    UC_X86_REG_R13, UC_X86_REG_R14, UC_X86_REG_R15]:
            self.mu.reg_write(reg, 0)
        self.mu.reg_write(UC_X86_REG_RBP, rsp + 0x200)
        self.mu.reg_write(UC_X86_REG_EFLAGS, 0x202)

    def _hook_code(self, uc, address, size, _):
        self.insn_count += 1
        # Safety: stop if too many insns without dispatch (infinite loop)
        if self.insn_count > 5_000_000:
            print(f'\n[!] Instruction limit (5M) reached @ RIP=0x{address:X}')
            uc.emu_stop()
            return
        if address in self.outline_loop_heads and self._try_outline_loop(uc, address):
            return
        insn = None
        if size <= 15:
            try:
                insn = next(self.cs.disasm(bytes(uc.mem_read(address, size)), address))
                self._maybe_log_special_insn(uc, insn)
            except:
                insn = None
        # Detect dispatch: add rax, [r12+E0h]
        if size == 8:
            code = bytes(uc.mem_read(address, 8))
            if code == DISPATCH_SIG:
                self._on_dispatch(uc, address)
                return
        if address == VM_DISPATCH_LOOP:
            # At entry, rax/rbx not yet loaded; read directly from context
            rsp = uc.reg_read(UC_X86_REG_RSP)
            delta_raw = struct.unpack('<Q', bytes(uc.mem_read(rsp + 0x190, 8)))[0]
            target_raw = struct.unpack('<Q', bytes(uc.mem_read(rsp + 0x198, 8)))[0]
            delta_signed = struct.unpack('<q', struct.pack('<Q', delta_raw))[0]
            if self.verbose >= 1:
                print(f'  [dispatch-loop] delta={delta_signed:+d} (0x{delta_raw:X})'
                      f'  target=0x{target_raw:X}')
        if address == VM_DISPATCH_JMP:
            rbx = uc.reg_read(UC_X86_REG_RBX)
            rsp = uc.reg_read(UC_X86_REG_RSP)
            r12 = uc.reg_read(UC_X86_REG_R12)
            if self.verbose >= 1:
                print(f'  [dispatch-loop] jmp rbx = 0x{rbx:X}  rsp=0x{rsp:X}  r12=0x{r12:X}')
            # Check if target resolves to a known stub
            if 0x1402A1000 <= rbx < 0x14266F000:
                # Resolve if it's a thunk
                try:
                    b = uc.mem_read(rbx, 1)[0]
                    if b == 0xE9:
                        rel = struct.unpack('<i', bytes(uc.mem_read(rbx + 1, 4)))[0]
                        dest = (rbx + 5 + rel) & 0xFFFFFFFFFFFFFFFF
                        print(f'              -> 0x{dest:X} (thunk)')
                except:
                    pass
        # Detect handler epilog: jmp rax/rdx/rbx (FF E0/E2/E3)
        # in the seg006 region
        if size == 2 and 0x1402A1000 <= address < 0x14266F000:
            code = bytes(uc.mem_read(address, 2))
            if code[0] == 0xFF and code[1] in (0xE0, 0xE2, 0xE3):
                JMP_REG = {0xE0: (UC_X86_REG_RAX, 'rax'),
                           0xE2: (UC_X86_REG_RDX, 'rdx'),
                           0xE3: (UC_X86_REG_RBX, 'rbx')}
                uc_reg, regname = JMP_REG[code[1]]
                reg = uc.reg_read(uc_reg)
                target_rva = reg - IMAGEBASE if reg > IMAGEBASE else 0
                in_binary = 0x1000 <= target_rva < 0x266F000
                if in_binary and address != VM_DISPATCH_JMP:
                    thunk_dest = None
                    try:
                        b = uc.mem_read(reg, 1)[0]
                        if b == 0xE9:
                            rel = struct.unpack('<i', bytes(uc.mem_read(reg + 1, 4)))[0]
                            thunk_dest = (reg + 5 + rel) & 0xFFFFFFFFFFFFFFFF
                        elif b == 0xE8:
                            rel = struct.unpack('<i', bytes(uc.mem_read(reg + 1, 4)))[0]
                            thunk_dest = (reg + 5 + rel) & 0xFFFFFFFFFFFFFFFF
                    except:
                        pass
                    dest_str = f' -> 0x{thunk_dest:X}' if thunk_dest else ''
                    vm_exit = thunk_dest == VM_EXIT if thunk_dest else False
                    tag = ' [VM EXIT path]' if vm_exit else ''
                    if thunk_dest and not vm_exit:
                        self.post_dispatch_targets.append(thunk_dest)
                    if self.verbose >= 1:
                        print(f'  [epilog] jmp {regname} = 0x{reg:X}{dest_str}{tag}')
        # Detect native call: call [rsp+8] (FF 54 24 08) inside a native stub
        if self.in_native_stub and address == self.native_call_addr and size == 4:
            rsp = uc.reg_read(UC_X86_REG_RSP)
            try:
                native_target = struct.unpack('<Q', bytes(uc.mem_read(rsp + 8, 8)))[0]
            except:
                native_target = 0
            self.pending_native_target = native_target
            if self.verbose >= 1:
                print(f'  [NATIVE CALL] call [rsp+8] = 0x{native_target:X}')
            # Record in the last trace entry
            if self.trace:
                self.trace[-1]['native_target_va'] = native_target
                self.trace[-1]['dispatch_kind'] = 'native_call'
                self.trace[-1]['native_stub_va'] = self.native_stub_addr
                native_snapshot = self._capture_native_call_snapshot(
                    uc,
                    native_target,
                    stub_addr=self.native_stub_addr,
                    call_addr=address,
                    source='live_stub',
                    handler_after=self.trace[-1].get('handler_after_native', 0),
                )
                if native_snapshot is not None:
                    self.trace[-1]['_native_snapshot'] = native_snapshot
            self.native_calls.append({
                'step': self.step,
                'native_target_va': native_target,
                'stub_addr': self.native_stub_addr,
            })

        # Track VM nesting. A vmenter call at the tail of a native-call stub
        # is only a re-entry into the current VM level, not a nested VM.
        if address == VM_SETUP:
            if self._is_native_stub_reentry(uc):
                if self.verbose >= 1:
                    print(f'  [vmenter reentry] depth still {self.vm_depth}')
            else:
                self.vm_depth += 1
                if self.verbose >= 1:
                    print(f'  [vmenter] depth now {self.vm_depth}')

        if address == VM_EXIT:
            self._on_vm_exit(uc)
        elif address == 0xDEADDEADDEADDEAD:
            print(f"\n[!] Hit sentinel return")
            uc.emu_stop()

    def _is_legit_addr(self, address):
        """Check if address is in PE image, stack, or known objects."""
        for lo, hi in self.pe_mapped_ranges:
            if lo <= address < hi:
                return True
        if STACK_BASE <= address < STACK_BASE + STACK_SIZE:
            return True
        if DRIVER_OBJ <= address < DRIVER_OBJ + 0x10000:
            return True
        if REG_PATH <= address < REG_PATH + 0x10000:
            return True
        return False

    def _hook_mem(self, uc, access, address, size, value, _):
        page = address & ~0xFFF
        if page in self.auto_mapped:
            return True  # Already mapped, allow access
        rip = uc.reg_read(UC_X86_REG_RIP)
        if self.verbose >= 2:
            atype = {1: 'READ', 2: 'WRITE', 4: 'FETCH'}.get(access, '?')
            print(f'  [mem] unmapped {atype} 0x{address:X} @ RIP=0x{rip:X}')
        if access == 4:  # FETCH -- code execution at unmapped address
            return False
        try:
            self.mu.mem_map(page, 0x1000)
            # Fill with self-referencing pointers: reading any QWORD
            # at offset N returns page+N, keeping pointer chains alive
            # instead of returning 0 which triggers VM EXIT paths.
            fill = bytearray(0x1000)
            for off in range(0, 0x1000, 8):
                struct.pack_into('<Q', fill, off, page + off)
            self.mu.mem_write(page, bytes(fill))
            self.auto_mapped.add(page)
            return True
        except:
            return False

    def _ctx_qword(self, uc, field):
        r12 = uc.reg_read(UC_X86_REG_R12)
        return struct.unpack('<Q', bytes(uc.mem_read(r12 + CTX_OFF[field], 8)))[0]

    def _is_native_stub_reentry(self, uc):
        """Return True when VM_SETUP was reached from a native-call stub re-entry."""
        rsp = uc.reg_read(UC_X86_REG_RSP)
        try:
            ret_addr = struct.unpack('<Q', bytes(uc.mem_read(rsp, 8)))[0]
        except:
            return False

        if not ret_addr:
            return False

        try:
            jmp_byte = bytes(uc.mem_read(ret_addr, 1))
            mid_addr = ret_addr - len(NATIVE_CALL_MID) - 5
            mid = bytes(uc.mem_read(mid_addr, len(NATIVE_CALL_MID)))
        except:
            return False

        return jmp_byte == b'\xE9' and mid == NATIVE_CALL_MID

    def _outline_trace_entry(self):
        if not self.trace:
            return None
        return self.trace[-1]

    def _finish_outlined_exit(self, uc):
        self.vm_depth = 0
        self.final_vmexit_seen = True
        rax = self._ctx_qword(uc, 'rax')
        hsh = self._ctx_qword(uc, 'hash')
        print(f"\n{'='*70}")
        print(f" VM EXIT after {self.step} steps ({self.insn_count} insns) [outlined]")
        print(f"   ctx.rax = 0x{rax:X}  last_hash = 0x{hsh:016X}")
        if self.native_calls:
            print(f"   native calls: {len(self.native_calls)}")
            for nc in self.native_calls:
                print(f"     step {nc['step']}: 0x{nc['native_target_va']:X} (stub 0x{nc['stub_addr']:X})")
        print(f"{'='*70}")
        uc.emu_stop()

    def _summarize_outline_telemetry(self, telemetry):
        if not telemetry:
            return None
        summary = {}
        for key in ('mem_read_count', 'mem_write_count', 'unmapped_count', 'instr_count'):
            if key in telemetry:
                summary[key] = telemetry[key]
        events = telemetry.get('events', [])
        if events:
            summary['events'] = events[:8]
        if telemetry.get('error'):
            summary['error'] = telemetry['error']
        return summary if summary else None

    def _try_outline_loop(self, uc, address):
        if self.resolver is None or address not in self.outline_loop_heads or not self.trace:
            return False

        ctx_base = uc.reg_read(UC_X86_REG_R12)
        ctx_size = getattr(self.resolver, 'CTX_SIZE', 0x1A0)
        try:
            live_ctx = bytes(uc.mem_read(ctx_base, ctx_size))
            hash_in = struct.unpack('<Q', live_ctx[CTX_OFF['hash']:CTX_OFF['hash'] + 8])[0]
        except:
            return False

        key = (self.step, address, hash_in)
        if key in self.outline_attempted:
            return False
        self.outline_attempted.add(key)

        entry = self._outline_trace_entry()
        if entry is not None:
            entry['outlined_loop_head_va'] = address
            entry['outline_hash_in'] = hash_in

        trace_hash = entry.get('hash') if isinstance(entry, dict) else None
        candidate_hashes = []
        for candidate in (hash_in, trace_hash):
            if isinstance(candidate, int) and candidate not in candidate_hashes:
                candidate_hashes.append(candidate)
        if entry is not None and candidate_hashes:
            entry['outline_hash_candidates'] = candidate_hashes

        outline_mode = None
        selected_hash = None
        resolved = None
        committed_ctx = False
        attempt_summaries = []

        def _record_attempt(mode, attempt_hash, telemetry, error=None):
            summary = self._summarize_outline_telemetry(telemetry)
            if summary is None:
                summary = {}
            summary['mode'] = mode
            summary['hash_in'] = f'0x{attempt_hash:016X}'
            if error:
                summary['outline_error'] = error
            attempt_summaries.append(summary)

        for attempt_hash in candidate_hashes:
            telemetry = {}
            try:
                resolved = self.resolver.resolve_handler(
                    address,
                    attempt_hash,
                    prev_ctx=live_ctx,
                    telemetry=telemetry,
                    max_insns=OUTLINE_LIVE_MAX_INSNS,
                )
            except Exception as e:
                _record_attempt('live', attempt_hash, telemetry, str(e))
                if entry is not None:
                    entry['outline_error'] = str(e)
            else:
                if resolved is not None:
                    outline_mode = 'live'
                    selected_hash = attempt_hash
                    _record_attempt('live', attempt_hash, telemetry)
                    break
                _record_attempt('live', attempt_hash, telemetry)

        if resolved is None:
            for attempt_hash in candidate_hashes:
                telemetry = {}
                try:
                    resolved = self.resolver.resolve_handler(
                        address,
                        attempt_hash,
                        prev_ctx=None,
                        telemetry=telemetry,
                        max_insns=OUTLINE_SYNTH_MAX_INSNS,
                    )
                except Exception as e:
                    _record_attempt('synthetic', attempt_hash, telemetry, str(e))
                    if entry is not None:
                        entry['outline_fallback_error'] = str(e)
                else:
                    if resolved is not None:
                        outline_mode = 'synthetic'
                        selected_hash = attempt_hash
                        _record_attempt('synthetic', attempt_hash, telemetry)
                        break
                    _record_attempt('synthetic', attempt_hash, telemetry)

        if entry is not None and attempt_summaries:
            entry['outline_attempts'] = attempt_summaries

        if resolved is None:
            self.outline_failures += 1
            return False

        kind, const_or_caller, hash_out_or_ha, out_ctx = resolved
        snapshot_ctx = out_ctx if out_ctx is not None else live_ctx
        if out_ctx is not None and outline_mode == 'live':
            try:
                uc.mem_write(ctx_base, out_ctx)
                committed_ctx = True
            except:
                pass

        self.outline_hits += 1
        self.post_dispatch_targets = []
        self.in_native_stub = False
        self.native_stub_addr = 0
        self.native_call_addr = 0
        uc.reg_write(UC_X86_REG_R12, ctx_base)
        uc.reg_write(UC_X86_REG_RSP, ctx_base)

        if entry is not None:
            entry['outline_kind'] = kind
            entry['outline_ctx_mode'] = outline_mode
            entry['outline_selected_hash'] = selected_hash
            entry['outline_context_committed'] = committed_ctx

        if kind == 'exit':
            if entry is not None:
                entry['final_vmexit_seen'] = True
            self._finish_outlined_exit(uc)
            return True

        if kind == 'dispatch':
            target = (const_or_caller + BASE_DELTA) & 0xFFFFFFFFFFFFFFFF
            dtype, dinfo = self.resolver.classify_dispatch_entry(target)
            if entry is not None:
                entry['outlined_dispatch_target_va'] = target
            if dtype == 'jmp':
                next_handler = dinfo['handler']
                if entry is not None:
                    entry['outlined_resume_handler_va'] = next_handler
                    entry['outlined_resume_kind'] = 'jmp'
                uc.reg_write(UC_X86_REG_RIP, next_handler)
                return True
            if dtype == 'native_call':
                handler_after = dinfo.get('handler_after', 0)
                if entry is not None:
                    entry['dispatch_kind'] = 'native_call'
                    entry['handler_after_native'] = handler_after
                    entry['outlined_resume_handler_va'] = handler_after
                    entry['outlined_resume_kind'] = 'native_call'
                if self.resolver._last_native_target:
                    if entry is not None:
                        entry['native_target_va'] = self.resolver._last_native_target
                        native_snapshot = self._synthesize_native_call_snapshot(
                            snapshot_ctx,
                            self.resolver._last_native_target,
                            stub_addr=target,
                            handler_after=handler_after,
                            source='outlined_dispatch',
                            runtime_regions=self._clone_native_probe_pages(
                                uc, self.resolver._last_native_target),
                        )
                        if native_snapshot is not None:
                            entry['_native_snapshot'] = native_snapshot
                    self.native_calls.append({
                        'step': self.step,
                        'native_target_va': self.resolver._last_native_target,
                        'stub_addr': target,
                    })
                if handler_after:
                    uc.reg_write(UC_X86_REG_RIP, handler_after)
                    return True
            if dtype == 'final_exit':
                if entry is not None:
                    entry['final_vmexit_seen'] = True
                self._finish_outlined_exit(uc)
                return True
            self.outline_failures += 1
            return False

        if kind == 'native_call':
            handler_after = hash_out_or_ha if isinstance(hash_out_or_ha, int) else 0
            if entry is not None:
                entry['dispatch_kind'] = 'native_call'
                entry['handler_after_native'] = handler_after
                entry['outlined_resume_handler_va'] = handler_after
                entry['outlined_resume_kind'] = 'native_call'
                entry['outlined_native_stub_va'] = const_or_caller
            if self.resolver._last_native_target:
                if entry is not None:
                    entry['native_target_va'] = self.resolver._last_native_target
                    native_snapshot = self._synthesize_native_call_snapshot(
                        snapshot_ctx,
                        self.resolver._last_native_target,
                        stub_addr=const_or_caller,
                        handler_after=handler_after,
                        source='outlined_native_call',
                        runtime_regions=self._clone_native_probe_pages(
                            uc, self.resolver._last_native_target),
                    )
                    if native_snapshot is not None:
                        entry['_native_snapshot'] = native_snapshot
                self.native_calls.append({
                    'step': self.step,
                    'native_target_va': self.resolver._last_native_target,
                    'stub_addr': const_or_caller,
                })
            if handler_after:
                uc.reg_write(UC_X86_REG_RIP, handler_after)
                return True

        self.outline_failures += 1
        return False

    def _classify_dispatch_target(self, uc, target):
        """Classify a dispatch target as 'jmp' (simple handler) or 'native_call' (stub).

        Returns (kind, thunk_dest, native_handler_after).
          - 'jmp':         thunk_dest = handler VA,  native_handler_after = None
          - 'native_call': thunk_dest = None,        native_handler_after = handler VA after native call
          - 'unknown':     thunk_dest = None,        native_handler_after = None
        """
        try:
            first_byte = uc.mem_read(target, 1)[0]
        except:
            return ('unknown', None, None)

        if first_byte == 0xE9:  # jmp rel32 -> handler
            rel = struct.unpack('<i', bytes(uc.mem_read(target + 1, 4)))[0]
            thunk_dest = (target + 5 + rel) & 0xFFFFFFFFFFFFFFFF
            return ('jmp', thunk_dest, None)

        if first_byte == 0xE8:  # call vmexit -> possibly a native call stub
            # Verify the middle signature: lea; call [rsp+8]; lea
            try:
                mid = bytes(uc.mem_read(target + 5, 20))
                if mid == NATIVE_CALL_MID:
                    # Parse the jmp at the end (offset 30)
                    jmp_bytes = bytes(uc.mem_read(target + 30, 5))
                    if jmp_bytes[0] == 0xE9:
                        rel = struct.unpack('<i', jmp_bytes[1:5])[0]
                        handler_after = (target + 35 + rel) & 0xFFFFFFFFFFFFFFFF
                        return ('native_call', None, handler_after)
            except:
                pass

        return ('unknown', None, None)

    def _on_dispatch(self, uc, address):
        rax_const = uc.reg_read(UC_X86_REG_RAX)
        base     = self._ctx_qword(uc, 'base')
        vm_hash  = self._ctx_qword(uc, 'hash')
        vm_extra = self._ctx_qword(uc, 'extra')
        target   = (rax_const + base) & 0xFFFFFFFFFFFFFFFF
        rva      = target - IMAGEBASE

        self.step += 1

        # If we were in a native call stub, the native call has completed
        # and the VM has re-entered.  Reset the tracking state.
        if self.in_native_stub:
            self.in_native_stub = False
            self.native_stub_addr = 0
            self.native_call_addr = 0

        kind, thunk_dest, handler_after = self._classify_dispatch_target(uc, target)

        # For native call stubs, set up tracking so _hook_code can capture
        # the native function pointer when call [rsp+8] executes.
        if kind == 'native_call':
            self.in_native_stub = True
            self.native_stub_addr = target
            self.native_call_addr = target + 13  # offset of call [rsp+8]
            self.pending_native_target = 0

        db_stub = self.db.lookup_hash(vm_hash)
        db_info = ""
        if db_stub:
            db_info = f"  [DB match]"
            if db_stub.get('extra') is not None:
                db_info += f"  extra=0x{db_stub['extra']:016X}"

        entry = {
            'step': self.step,
            'at': address,
            'const': rax_const,
            'target': target,
            'rva': rva,
            'thunk': thunk_dest,
            'hash': vm_hash,
            'extra': vm_extra,
            'dispatch_kind': kind,
            'handler_after_native': handler_after,
            'vm_depth': self.vm_depth,
        }
        snapshot = self._capture_vm_snapshot(uc)
        if snapshot is not None:
            entry['_vm_snapshot'] = snapshot
        self.trace.append(entry)
        self.post_dispatch_targets = []

        kind_tag = ''
        if kind == 'native_call':
            kind_tag = ' [NATIVE CALL STUB]'
            dest_str = f" -> native_call -> 0x{handler_after:X}"
        elif thunk_dest:
            dest_str = f" -> 0x{thunk_dest:X}"
        else:
            dest_str = ''

        if self.verbose >= 1:
            print(f"[{self.step:4d}] DISPATCH @ 0x{address:X}{kind_tag}")
            print(f"       const=0x{rax_const:08X}  target=0x{target:X}{dest_str}")
            print(f"       hash=0x{vm_hash:016X}  extra=0x{vm_extra:016X}{db_info}")

        if self.verbose >= 2:
            r12 = uc.reg_read(UC_X86_REG_R12)
            gprs = {}
            for f in GPR_NAMES:
                if f in CTX_OFF:
                    gprs[f] = struct.unpack('<Q',
                        bytes(uc.mem_read(r12 + CTX_OFF[f], 8)))[0]
            entry['gprs'] = gprs
            vals = "  ".join(f"{k}=0x{v:X}" for k,v in list(gprs.items())[:6])
            print(f"       ctx: {vals}")

        if self.step >= self.max_steps:
            print(f"\n[!] Max steps ({self.max_steps}) reached")
            uc.emu_stop()

    def _on_vm_exit(self, uc):
        # Check if this is a transient vmexit (inside a native call stub).
        # A native call stub is: call VM_EXIT(5) + NATIVE_CALL_MID(20) + call vmenter(5) + jmp(5).
        # When VM_EXIT is reached via `call` from a native call stub, the
        # return address on the stack points to the lea rsp,[rsp+1C0h] which
        # is the start of NATIVE_CALL_MID.  Detect this by reading the bytes
        # at ret_addr — no pre-classification state required.
        rsp = uc.reg_read(UC_X86_REG_RSP)
        try:
            ret_addr = struct.unpack('<Q', bytes(uc.mem_read(rsp, 8)))[0]
        except:
            ret_addr = 0

        is_transient = False
        if ret_addr:
            try:
                ret_bytes = bytes(uc.mem_read(ret_addr, len(NATIVE_CALL_MID)))
                if ret_bytes == NATIVE_CALL_MID:
                    is_transient = True
                    stub_addr = ret_addr - 5  # call VM_EXIT is 5 bytes before
                    # Set up native stub tracking state so _hook_code can
                    # capture the native function pointer at call [rsp+8].
                    self.in_native_stub = True
                    self.native_stub_addr = stub_addr
                    # call [rsp+8] is at ret_addr + 8 (after the 8-byte lea)
                    self.native_call_addr = ret_addr + 8
            except:
                pass

        if is_transient:
            if self.verbose >= 1:
                print(f'  [VM EXIT transient] ret -> 0x{ret_addr:X} (native call stub @ 0x{stub_addr:X})')
            return  # let emulation continue through the stub

        # Inner VM exit: if we're nested (depth > 1), this is not the outer
        # VM's exit.  The inner VM returns to the vmenter wrapper body which
        # then returns to the outer VM's native call stub.  Decrement depth
        # and let emulation continue.
        if self.vm_depth > 1:
            self.vm_depth -= 1
            if self.verbose >= 1:
                print(f'  [VM EXIT inner] depth now {self.vm_depth}  ret -> 0x{ret_addr:X}')
            return  # let emulation continue out of the inner VM

        # Final vmexit — the outermost VM is done.
        self.vm_depth = 0
        self.final_vmexit_seen = True
        rax = self._ctx_qword(uc, 'rax')
        hsh = self._ctx_qword(uc, 'hash')
        print(f"\n{'='*70}")
        print(f" VM EXIT after {self.step} steps ({self.insn_count} insns)")
        print(f"   ctx.rax = 0x{rax:X}  last_hash = 0x{hsh:016X}")
        if self.native_calls:
            print(f"   native calls: {len(self.native_calls)}")
            for nc in self.native_calls:
                print(f"     step {nc['step']}: 0x{nc['native_target_va']:X} (stub 0x{nc['stub_addr']:X})")
        print(f"{'='*70}")
        uc.emu_stop()

    def run(self, max_steps=300, start=None):
        self.max_steps = max_steps
        entry = start or DRIVER_ENTRY
        self.final_vmexit_seen = False
        self.post_dispatch_targets = []
        self.outline_attempted.clear()
        self.outline_hits = 0
        self.outline_failures = 0

        self.mu.hook_add(UC_HOOK_CODE, self._hook_code)
        self.mu.hook_add(UC_HOOK_MEM_READ | UC_HOOK_MEM_WRITE, self._hook_mem_access)
        self.mu.hook_add(
            UC_HOOK_MEM_READ_UNMAPPED | UC_HOOK_MEM_WRITE_UNMAPPED |
            UC_HOOK_MEM_FETCH_UNMAPPED, self._hook_mem)

        print(f"\n{'='*70}")
        print(f" VM Emulation Trace")
        print(f" Entry: 0x{entry:X}   Max steps: {max_steps}")
        print(f"{'='*70}\n")

        t0 = time.time()
        try:
            self.mu.emu_start(entry, 0, timeout=300_000_000)
        except UcError as e:
            rip = self.mu.reg_read(UC_X86_REG_RIP)
            print(f"\n[!] UcError at RIP=0x{rip:X}: {e}")
            try:
                code = bytes(self.mu.mem_read(rip, 32))
                for insn in self.cs.disasm(code, rip):
                    print(f"     0x{insn.address:X}: {insn.mnemonic} {insn.op_str}")
                    if insn.address > rip + 20:
                        break
            except:
                pass
        dt = time.time() - t0
        print(f"\n Emulation: {self.step} dispatches, {self.insn_count} insns, {dt:.2f}s")
        print(f" Auto-mapped pages: {len(self.auto_mapped)}  Skips: {self.skip_count}")
        if self.outline_hits or self.outline_failures:
            print(f" Outlined loops: {self.outline_hits}  Outline failures: {self.outline_failures}")
        if self.watched_mem_events:
            print(f" Watched memory events: {len(self.watched_mem_events)}")
        if self.privileged_insn_events:
            print(f" Privileged/special instructions: {len(self.privileged_insn_events)}")
        if self.trace:
            if not self.final_vmexit_seen and self.post_dispatch_targets:
                counts = {}
                for target in self.post_dispatch_targets:
                    counts[target] = counts.get(target, 0) + 1
                internal_resume_va = max(counts.items(), key=lambda kv: kv[1])[0]
                self.trace[-1]['internal_resume_va'] = internal_resume_va
            self.trace[-1]['final_vmexit_seen'] = self.final_vmexit_seen
            self.trace[-1]['watched_mem_events'] = self.watched_mem_events[:128]
            self.trace[-1]['privileged_insn_events'] = self.privileged_insn_events[:64]
        return self.trace


# =============================================================================
#  Static Hash-Chain Walker
# =============================================================================

def static_trace(db, observed_hashes):
    """Walk the hash chain using observed hashes from emulation."""
    print(f"\n{'='*70}")
    print(f" Static Hash-Chain Resolution")
    print(f" {len(observed_hashes)} observed hashes from emulation")
    print(f"{'='*70}")

    for i, h in enumerate(observed_hashes):
        stub = db.lookup_hash(h)
        if stub:
            dest = stub['thunk_target'] or stub['target']
            ex = ""
            if stub.get('extra') is not None:
                ex = f"\n        extra=0x{stub['extra']:016X}"
            print(f" [{i+1:4d}] hash=0x{h:016X}")
            print(f"        stub @ 0x{stub['stub_addr']:X}")
            print(f"        const=0x{stub['const']:06X}  ->  0x{stub['target']:X}"
                  f"{f' -> 0x{dest:X}' if dest != stub['target'] else ''}{ex}")
        else:
            print(f" [{i+1:4d}] hash=0x{h:016X}  -- NOT FOUND in stub DB")


# =============================================================================
#  omill VMTraceRecord JSON Export
# =============================================================================

def export_omill_trace_json(trace, db, out_path):
    """
    Convert emulation trace to omill VMTraceRecord-compatible JSON.

    omill VMTraceRecord schema:
        handler_va:      uint64 -- handler body VA
        incoming_hash:   uint64 -- hash at dispatch entering this handler
        outgoing_hash:   uint64 -- hash set by this handler for next dispatch
        exit_target_va:  uint64 -- dispatch target VA (thunk entry)
        native_target_va: uint64 -- native function called via dispatch stub (0 if none)
        successors:      [uint64] -- resolved next handler VA(s)
        passed_vmexit:   bool
        is_vmexit:       bool
        is_error:        bool

    The trace is a sequence of dispatch events.  Each step i produces one record.
    For simple dispatches (jmp), the successor is the next handler.
    For native call dispatches, native_target_va is the called function and
    the successor is the handler that executes after the native call returns.
    """
    if not trace:
        return

    def _resume_step_index(start_idx):
        current_depth = trace[start_idx].get('vm_depth', 0)
        for idx in range(start_idx + 1, len(trace)):
            if trace[idx].get('vm_depth', 0) <= current_depth:
                return idx
        return None

    final_vmexit_seen = bool(trace[-1].get('final_vmexit_seen'))
    records = []
    for i, step in enumerate(trace):
        handler_va = step.get('thunk') or step.get('target', 0)
        incoming_hash = step.get('hash', 0)
        dispatch_kind = step.get('dispatch_kind', 'jmp')
        native_target = step.get('native_target_va', 0)
        handler_after_native = step.get('handler_after_native', 0)

        next_idx = i + 1 if i + 1 < len(trace) else None
        if dispatch_kind == 'native_call':
            next_idx = _resume_step_index(i)

        if next_idx is not None:
            nxt = trace[next_idx]
            outgoing_hash = nxt.get('hash', 0)
            exit_target_va = nxt.get('target', 0)
            succ_va = nxt.get('thunk') or nxt.get('target', 0)

            successors = [succ_va] if succ_va else []
            is_vmexit = False
        else:
            # Last step only exits the VM if emulation actually reached final vmexit.
            outgoing_hash = 0
            exit_target_va = 0
            successors = []
            is_vmexit = final_vmexit_seen

        records.append({
            'handler_va':       f'0x{handler_va:X}',
            'incoming_hash':    f'0x{incoming_hash:X}',
            'outgoing_hash':    f'0x{outgoing_hash:X}',
            'exit_target_va':   f'0x{exit_target_va:X}',
            'native_target_va': f'0x{native_target:X}' if native_target else '0x0',
            'successors':       [f'0x{s:X}' for s in successors],
            'passed_vmexit':    is_vmexit,
            'is_vmexit':        is_vmexit,
            'is_error':         False,
            'dispatch_kind':    dispatch_kind,
        })

    payload = {
        'vmenter_va': f'0x{VM_ENTRY:X}',
        'vmexit_va':  f'0x{VM_EXIT:X}',
        'records':    records,
    }

    with open(out_path, 'w') as f:
        json.dump(payload, f, indent=2)
    print(f'\n Exported {len(records)} VMTraceRecords to {out_path}')
    return payload


def _hex_int(value):
    if isinstance(value, int):
        return value
    if isinstance(value, str):
        try:
            return int(value, 16)
        except ValueError:
            return 0
    return 0


def _is_zero_hex(value):
    return _hex_int(value) == 0


def _merge_vmtrace_record(primary, secondary):
    """Merge two VMTraceRecord-like dicts, preferring observed primary data."""
    merged = dict(secondary)
    merged.update(primary)

    primary_kind = primary.get('dispatch_kind', 'unknown')
    if primary_kind == 'native_call' and primary.get('successors'):
        merged['successors'] = list(primary['successors'])
        if not _is_zero_hex(primary.get('outgoing_hash', '0x0')):
            merged['outgoing_hash'] = primary['outgoing_hash']
        if not _is_zero_hex(primary.get('exit_target_va', '0x0')):
            merged['exit_target_va'] = primary['exit_target_va']
        if not _is_zero_hex(primary.get('native_target_va', '0x0')):
            merged['native_target_va'] = primary['native_target_va']
        if primary_kind != 'unknown':
            merged['dispatch_kind'] = primary_kind
        return merged

    for field in ('outgoing_hash', 'exit_target_va', 'native_target_va'):
        if _is_zero_hex(merged.get(field, '0x0')) and not _is_zero_hex(secondary.get(field, '0x0')):
            merged[field] = secondary[field]

    if not merged.get('successors') and secondary.get('successors'):
        merged['successors'] = list(secondary['successors'])
    elif merged.get('successors') and secondary.get('successors'):
        seen = set()
        succs = []
        for succ in list(merged['successors']) + list(secondary['successors']):
            if succ not in seen:
                seen.add(succ)
                succs.append(succ)
        merged['successors'] = succs

    if not merged.get('passed_vmexit', False) and secondary.get('passed_vmexit', False):
        merged['passed_vmexit'] = True
    if not merged.get('is_vmexit', False) and secondary.get('is_vmexit', False):
        merged['is_vmexit'] = True
    if not merged.get('is_error', False) and secondary.get('is_error', False):
        merged['is_error'] = True

    if merged.get('dispatch_kind', 'unknown') == 'unknown':
        alt_kind = secondary.get('dispatch_kind', 'unknown')
        if alt_kind != 'unknown':
            merged['dispatch_kind'] = alt_kind

    return merged


def merge_vmtrace_records(primary_records, secondary_records):
    """Merge record lists by (handler_va, incoming_hash), primary wins on conflicts."""
    merged = {}
    order = []

    for rec in secondary_records:
        key = (rec['handler_va'], rec['incoming_hash'])
        if key not in merged:
            merged[key] = dict(rec)
            order.append(key)
        else:
            merged[key] = _merge_vmtrace_record(rec, merged[key])

    for rec in primary_records:
        key = (rec['handler_va'], rec['incoming_hash'])
        if key not in merged:
            merged[key] = dict(rec)
            order.append(key)
        else:
            merged[key] = _merge_vmtrace_record(rec, merged[key])

    return [merged[key] for key in order]


def collect_native_call_snapshots(trace):
    snapshots = []
    for step in trace or []:
        snap = step.get('_native_snapshot')
        if not snap:
            continue
        item = dict(snap)
        item['step'] = step.get('step', 0)
        item['dispatch_hash'] = step.get('hash', 0)
        item['dispatch_target_va'] = step.get('target', 0)
        item['dispatch_kind'] = step.get('dispatch_kind', 'unknown')
        snapshots.append(item)
    return snapshots


def replay_native_snapshot(snapshot, max_insns=200000):
    def maybe_int(value, default=0):
        if value is None:
            return default
        try:
            return int(value)
        except (TypeError, ValueError):
            return default

    mu = Uc(UC_ARCH_X86, UC_MODE_64)
    pe = pefile.PE(str(BINARY_PATH))

    for sec in pe.sections:
        va = IMAGEBASE + sec.VirtualAddress
        data = sec.get_data()
        vsize = max(sec.Misc_VirtualSize, len(data))
        size = (vsize + 0xFFF) & ~0xFFF
        if size == 0:
            size = 0x1000
        mu.mem_map(va, size)
        mu.mem_write(va, data[:vsize])

    auto_mapped = set()

    def map_region(base, size, data_hex=None):
        if size <= 0:
            return
        try:
            mu.mem_map(base, size)
        except UcError:
            pass
        if data_hex:
            try:
                mu.mem_write(base, bytes.fromhex(data_hex))
            except:
                pass

    for base, size in (
        (STACK_BASE, STACK_SIZE),
        (DRIVER_OBJ, 0x10000),
        (REG_PATH, 0x10000),
        (STUB_BASE, 0x10000),
        (KUSER_SHARED_DATA, KUSD_PAGE_SIZE),
    ):
        map_region(base, size)

    for region in snapshot.get('runtime_regions', []):
        base = maybe_int(region.get('base', 0))
        size = maybe_int(region.get('size', 0))
        data = region.get('data', b'')
        if isinstance(data, bytes):
            data_hex = data.hex()
        else:
            data_hex = region.get('data_hex', '')
        map_region(base, size, data_hex)
        if size == 0x1000:
            auto_mapped.add(base)

    # Mirror the tracer's deterministic synthetic runtime setup.
    kusd = bytearray(KUSD_PAGE_SIZE)
    filetime = 0x01DA5E9847800000
    struct.pack_into('<I', kusd, 0x14, filetime & 0xFFFFFFFF)
    struct.pack_into('<i', kusd, 0x18, (filetime >> 32) & 0xFFFFFFFF)
    struct.pack_into('<i', kusd, 0x1C, (filetime >> 32) & 0xFFFFFFFF)
    struct.pack_into('<I', kusd, 0x08, filetime & 0xFFFFFFFF)
    struct.pack_into('<i', kusd, 0x0C, (filetime >> 32) & 0xFFFFFFFF)
    struct.pack_into('<i', kusd, 0x10, (filetime >> 32) & 0xFFFFFFFF)
    struct.pack_into('<I', kusd, 0x26C, 10)
    struct.pack_into('<I', kusd, 0x270, 0)
    mu.mem_write(KUSER_SHARED_DATA, bytes(kusd))

    for off in range(0, 0x2000, 8):
        mu.mem_write(DRIVER_OBJ + off, struct.pack('<Q', 0xDEAD000000000000 | off))

    mu.mem_write(STUB_BASE, b'\xC3')
    mu.mem_write(STUB_BASE + 0x10, b'\x31\xC0\xC3')
    mu.mem_write(0x14019E000, struct.pack('<Q', STUB_BASE + 0x10))
    mu.mem_write(0x14019E010, struct.pack('<Q', STUB_BASE))
    cookie = 0xDEADBEEFCAFEBABE
    mu.mem_write(0x140221028, struct.pack('<Q', cookie))
    mu.mem_write(0x140221030, struct.pack('<Q', (~cookie) & 0xFFFFFFFFFFFFFFFF))

    stack_base = maybe_int(snapshot.get('stack_base', 0))
    stack_hex = snapshot.get('stack_bytes', '')
    if stack_base and stack_hex:
        try:
            mu.mem_write(stack_base, bytes.fromhex(stack_hex))
        except:
            pass

    regs = snapshot.get('regs', {})
    for name, reg in UC_REG_BY_NAME.items():
        if name in regs:
            mu.reg_write(reg, maybe_int(regs[name]))
    entry_rsp = maybe_int(snapshot.get('entry_rsp', regs.get('rsp', 0)))
    if entry_rsp:
        mu.reg_write(UC_X86_REG_RSP, entry_rsp)
    mu.reg_write(UC_X86_REG_EFLAGS, maybe_int(snapshot.get('eflags', 0x202), 0x202))

    sentinel = 0xDEADDEADDEADDEAD
    if entry_rsp:
        try:
            mu.mem_write(entry_rsp, struct.pack('<Q', sentinel))
        except:
            pass

    cs = Cs(CS_ARCH_X86, CS_MODE_64)
    insn_count = 0
    indirect_calls = []
    visited = []
    mem_events = []
    watched_mem_events = []
    watched_mem_seen = set()
    privileged_events = []
    privileged_seen = set()

    def hook_mem(uc, access, address, size, value, _):
        rip = uc.reg_read(UC_X86_REG_RIP)
        page = address & ~0xFFF
        if address in WATCHED_GLOBALS or page in WATCHED_PAGES:
            key = (access, address, size, value, rip)
            if key not in watched_mem_seen:
                watched_mem_seen.add(key)
                watched_mem_events.append({
                    'access': int(access),
                    'address': address,
                    'size': size,
                    'value': value,
                    'rip': rip,
                    'label': WATCHED_GLOBALS.get(address, ''),
                })
        mem_events.append({
            'access': int(access),
            'address': address,
            'size': size,
            'value': value,
            'rip': rip,
        })
        if access == UC_MEM_FETCH_UNMAPPED:
            return False
        if page in auto_mapped:
            return True
        try:
            mu.mem_map(page, 0x1000)
            fill = bytearray(0x1000)
            for off in range(0, 0x1000, 8):
                struct.pack_into('<Q', fill, off, page + off)
            mu.mem_write(page, bytes(fill))
            auto_mapped.add(page)
            return True
        except:
            return False

    def hook_code(uc, address, size, _):
        nonlocal insn_count
        insn_count += 1
        if len(visited) < 256:
            visited.append(address)
        if address == sentinel:
            uc.emu_stop()
            return
        try:
            code = bytes(uc.mem_read(address, size))
            insn = next(cs.disasm(code, address))
        except:
            insn = None
        if insn:
            mn = insn.mnemonic.lower()
            if mn in PRIVILEGED_MNEMONICS or SPECIAL_REG_TOKEN_RE.search((insn.op_str or '').lower()):
                key = (insn.address, mn, insn.op_str)
                if key not in privileged_seen:
                    privileged_seen.add(key)
                    privileged_events.append({
                        'rip': insn.address,
                        'mnemonic': insn.mnemonic,
                        'op_str': insn.op_str,
                    })
        if insn and insn.mnemonic == 'call' and insn.op_str.startswith('rax'):
            indirect_calls.append({
                'callsite_va': address,
                'target_va': uc.reg_read(UC_X86_REG_RAX),
                'rcx': uc.reg_read(UC_X86_REG_RCX),
                'rdx': uc.reg_read(UC_X86_REG_RDX),
            })
        if insn_count >= max_insns:
            uc.emu_stop()

    mu.hook_add(UC_HOOK_CODE, hook_code)
    mu.hook_add(UC_HOOK_MEM_READ | UC_HOOK_MEM_WRITE, hook_mem)
    mu.hook_add(
        UC_HOOK_MEM_READ_UNMAPPED |
        UC_HOOK_MEM_WRITE_UNMAPPED |
        UC_HOOK_MEM_FETCH_UNMAPPED,
        hook_mem)

    stop_reason = 'limit'
    exception_state = {}
    try:
        mu.emu_start(maybe_int(snapshot.get('native_target_va', 0)), sentinel, count=max_insns)
        stop_reason = 'returned'
    except UcError as e:
        stop_reason = f'uc_error:{e}'
        exception_state = {
            'rip': mu.reg_read(UC_X86_REG_RIP),
            'rax': mu.reg_read(UC_X86_REG_RAX),
            'rcx': mu.reg_read(UC_X86_REG_RCX),
            'rdx': mu.reg_read(UC_X86_REG_RDX),
            'r10': mu.reg_read(UC_X86_REG_R10),
        }

    return {
        'native_target_va': maybe_int(snapshot.get('native_target_va', 0)),
        'source': snapshot.get('source', 'unknown'),
        'step': maybe_int(snapshot.get('step', 0)),
        'dispatch_hash': maybe_int(snapshot.get('dispatch_hash', 0)),
        'stub_addr': maybe_int(snapshot.get('stub_addr', 0)),
        'handler_after_va': maybe_int(snapshot.get('handler_after_va', 0)),
        'entry_rsp': entry_rsp,
        'stop_reason': stop_reason,
        'insn_count': insn_count,
        'indirect_calls': indirect_calls,
        'visited_prefix': [f'0x{va:X}' for va in visited[:96]],
        'unmapped_events': mem_events[:32],
        'watched_mem_events': watched_mem_events[:64],
        'privileged_insn_events': privileged_events[:32],
        'exception_state': exception_state,
    }


def export_native_call_artifacts(trace, out_dir):
    def maybe_hex(value):
        if value is None:
            return None
        try:
            return f'0x{int(value):X}'
        except (TypeError, ValueError):
            return value

    snapshots = collect_native_call_snapshots(trace)
    if not snapshots:
        return [], []

    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    serializable_snapshots = []
    for snap in snapshots:
        item = dict(snap)
        item['regs'] = {
            k: maybe_hex(v) for k, v in item.get('regs', {}).items()
        }
        for key in (
            'native_target_va', 'stub_addr', 'call_addr', 'handler_after_va',
            'rsp_pre_call', 'entry_rsp', 'stack_base', 'dispatch_hash',
            'dispatch_target_va',
        ):
            if key in item:
                item[key] = maybe_hex(item[key])
        runtime_regions = []
        for region in item.get('runtime_regions', []):
            runtime_regions.append({
                'base': maybe_hex(region.get('base', 0)),
                'size': int(region.get('size', 0)),
                'data_hex': region.get('data', b'').hex() if isinstance(region.get('data'), bytes) else region.get('data_hex', ''),
            })
        item['runtime_regions'] = runtime_regions
        serializable_snapshots.append(item)

    snapshots_out = out_dir / 'native_call_snapshots.json'
    with open(snapshots_out, 'w') as f:
        json.dump({'snapshots': serializable_snapshots}, f, indent=2)

    probe_results = []
    seen_targets = set()
    for snap in snapshots:
        target = int(snap.get('native_target_va', 0))
        if not target or target in seen_targets:
            continue
        seen_targets.add(target)
        probe_results.append(replay_native_snapshot(snap))

    serializable_results = []
    for result in probe_results:
        item = dict(result)
        for key in ('native_target_va', 'dispatch_hash', 'stub_addr', 'handler_after_va', 'entry_rsp'):
            item[key] = maybe_hex(item.get(key, 0))
        converted_calls = []
        for call in item.get('indirect_calls', []):
            converted_calls.append({
                'callsite_va': maybe_hex(call.get('callsite_va')),
                'target_va': maybe_hex(call.get('target_va')),
                'rcx': maybe_hex(call.get('rcx')),
                'rdx': maybe_hex(call.get('rdx')),
            })
        item['indirect_calls'] = converted_calls
        converted_events = []
        for event in item.get('unmapped_events', []):
            converted_events.append({
                'access': event.get('access'),
                'address': maybe_hex(event.get('address')),
                'size': event.get('size'),
                'value': maybe_hex(event.get('value')),
                'rip': maybe_hex(event.get('rip')),
            })
        item['unmapped_events'] = converted_events
        watched_events = []
        for event in item.get('watched_mem_events', []):
            watched_events.append({
                'access': event.get('access'),
                'address': maybe_hex(event.get('address')),
                'size': event.get('size'),
                'value': maybe_hex(event.get('value')),
                'rip': maybe_hex(event.get('rip')),
                'label': event.get('label', ''),
            })
        item['watched_mem_events'] = watched_events
        item['privileged_insn_events'] = [
            {
                'rip': maybe_hex(event.get('rip')),
                'mnemonic': event.get('mnemonic', ''),
                'op_str': event.get('op_str', ''),
            }
            for event in item.get('privileged_insn_events', [])
        ]
        item['exception_state'] = {
            key: maybe_hex(value)
            for key, value in item.get('exception_state', {}).items()
        }
        serializable_results.append(item)

    probes_out = out_dir / 'native_call_probes.json'
    with open(probes_out, 'w') as f:
        json.dump({'results': serializable_results}, f, indent=2)

    print(f'  Exported {len(serializable_snapshots)} native snapshots -> {snapshots_out}')
    print(f'  Exported {len(serializable_results)} native probes -> {probes_out}')
    return serializable_snapshots, serializable_results


def _first_concrete_handler_from_chain(chain, fallback=0):
    """Return the first real handler reached by an inner-VM chain.

    parse_vm_wrapper_full can identify a wrapper's initial dispatch helper,
    but that helper may just be glue (e.g. 0x140C04245) before the first
    semantically relevant traced handler.  Prefer the first concrete handler
    in the traced chain when available.
    """
    if chain:
        first = chain[0]
        next_handler = first.get('next_handler', 0)
        if next_handler:
            return next_handler
        handler = first.get('handler', 0)
        if handler:
            return handler
        for step in chain[1:]:
            handler = step.get('handler', 0)
            if handler:
                return handler
            next_handler = step.get('next_handler', 0)
            if next_handler:
                return next_handler
    return fallback


def normalize_wrapper_trace_records(records, wrapper_seed_info):
    """Rewrite wrapper/native-target records to resume at traced inner handlers.

    `wrapper_seed_info` maps wrapper/native target VA -> (inner_hash, first_handler).
    The imported Unicorn record for a wrapper often uses incoming_hash=0 and points
    at a wrapper helper instead of the first traced inner handler.  Normalize that
    record in-place so the lifter can follow the wrapped inner chain.
    """
    if not records or not wrapper_seed_info:
        return records

    def _parse_u64(value):
        if isinstance(value, int):
            return value & 0xFFFFFFFFFFFFFFFF
        if isinstance(value, str):
            try:
                return int(value, 0) & 0xFFFFFFFFFFFFFFFF
            except ValueError:
                return 0
        return 0

    def _best_inbound_wrapper_record(wrapper_va, seed_hash):
        candidates = []
        for cand in records:
            if cand.get('native_target_va') != wrapper_va:
                continue
            succs = [s for s in cand.get('successors', [])
                     if isinstance(s, str) and s and s != wrapper_va]
            if not succs:
                continue
            cand_hash = _parse_u64(cand.get('outgoing_hash'))
            score = 0
            if seed_hash and cand_hash == seed_hash:
                score += 10
            if cand.get('dispatch_kind') == 'jmp':
                score += 2
            if cand.get('exit_target_va') not in (None, '0x0', '0'):
                score += 1
            score -= len(succs)
            candidates.append((score, cand, succs))
        if not candidates:
            return None
        candidates.sort(key=lambda item: item[0], reverse=True)
        return candidates[0]

    record_by_key = {(rec.get('handler_va'), rec.get('incoming_hash')): rec
                     for rec in records}
    for nt_va, (inner_hash, first_handler) in wrapper_seed_info.items():
        handler_key = f'0x{nt_va:X}'
        rec = record_by_key.get((handler_key, '0x0'))
        if rec is None:
            rec = {
                'handler_va': handler_key,
                'incoming_hash': '0x0',
                'outgoing_hash': '0x0',
                'exit_target_va': '0x0',
                'native_target_va': '0x0',
                'successors': [],
                'passed_vmexit': False,
                'is_vmexit': False,
                'is_error': False,
            }
            records.append(rec)
            record_by_key[(handler_key, '0x0')] = rec

        inbound = _best_inbound_wrapper_record(handler_key, inner_hash)
        if inbound is not None:
            _, inbound_rec, inbound_succs = inbound
            rec['outgoing_hash'] = inbound_rec.get(
                'outgoing_hash',
                f'0x{inner_hash:X}' if inner_hash else '0x0')
            rec['successors'] = list(dict.fromkeys(inbound_succs))
            exit_target_va = inbound_rec.get('exit_target_va')
            if exit_target_va not in (None, '', '0x0', '0'):
                rec['exit_target_va'] = exit_target_va
        else:
            if inner_hash:
                rec['outgoing_hash'] = f'0x{inner_hash:X}'
            rec['successors'] = [f'0x{first_handler:X}'] if first_handler else []
        if rec.get('dispatch_kind', 'unknown') == 'unknown':
            rec['dispatch_kind'] = 'jmp'

    return records


def bridge_unicorn_trace_records(trace, trace_payload, resolver):
    """Patch timed-out Unicorn records with a statically resolved continuation."""
    if not trace or not trace_payload:
        return trace_payload

    records = trace_payload.get('records', [])
    for step, record in zip(trace, records):
        if record.get('is_vmexit') or not step.get('internal_resume_va'):
            continue

        internal_va = step['internal_resume_va']
        incoming_hash = step.get('hash', 0)
        resolved = resolver.resolve_handler(internal_va, incoming_hash)
        if resolved is None:
            continue

        kind, const_or_caller, hash_out_or_ha, _ = resolved
        if kind == 'exit':
            record['outgoing_hash'] = '0x0'
            record['exit_target_va'] = '0x0'
            record['successors'] = []
            record['passed_vmexit'] = True
            record['is_vmexit'] = True
            continue

        if kind == 'dispatch':
            target = (const_or_caller + BASE_DELTA) & 0xFFFFFFFFFFFFFFFF
            dtype, dinfo = resolver.classify_dispatch_entry(target)
            if dtype == 'jmp':
                record['outgoing_hash'] = f'0x{hash_out_or_ha:X}'
                record['exit_target_va'] = f'0x{target:X}'
                record['successors'] = [f"0x{dinfo['handler']:X}"]
                record['dispatch_kind'] = 'jmp'
            elif dtype == 'native_call':
                handler_after = dinfo.get('handler_after', 0)
                if handler_after:
                    record['successors'] = [f'0x{handler_after:X}']
                if resolver._last_native_target:
                    record['native_target_va'] = f"0x{resolver._last_native_target:X}"
                record['dispatch_kind'] = 'native_call'
            continue

        if kind == 'native_call':
            handler_after = hash_out_or_ha if isinstance(hash_out_or_ha, int) else 0
            if handler_after:
                record['successors'] = [f'0x{handler_after:X}']
            if resolver._last_native_target:
                record['native_target_va'] = f"0x{resolver._last_native_target:X}"
            record['dispatch_kind'] = 'native_call'

    return trace_payload


def augment_records_with_live_snapshots(trace, trace_payload, resolver):
    """Use captured live VM snapshots to synthesize missing exact records."""
    if not trace or not trace_payload or resolver is None:
        return trace_payload

    records = trace_payload.get('records', [])
    if not records:
        return trace_payload

    record_by_key = {}
    for rec in records:
        key = (rec.get('handler_va'), rec.get('incoming_hash'))
        record_by_key[key] = rec

    augmented = 0
    for step in trace:
        snapshot = step.get('_vm_snapshot')
        if not snapshot:
            continue

        handler_va = step.get('thunk') or step.get('target', 0)
        incoming_hash = step.get('hash', 0)
        if not handler_va:
            continue

        key = (f'0x{handler_va:X}', f'0x{incoming_hash:X}')
        rec = record_by_key.get(key)
        if rec is not None:
            if rec.get('is_vmexit') or rec.get('is_error'):
                continue
            if rec.get('successors'):
                continue

        telemetry = {}
        try:
            resolved = resolver.resolve_handler(
                handler_va,
                incoming_hash,
                prev_ctx=snapshot['ctx'],
                telemetry=telemetry,
                max_insns=OUTLINE_LIVE_MAX_INSNS,
            )
        except Exception:
            resolved = None
        if resolved is None:
            continue

        if rec is None:
            rec = {
                'handler_va': f'0x{handler_va:X}',
                'incoming_hash': f'0x{incoming_hash:X}',
                'outgoing_hash': '0x0',
                'exit_target_va': '0x0',
                'native_target_va': '0x0',
                'successors': [],
                'passed_vmexit': False,
                'is_vmexit': False,
                'is_error': False,
                'dispatch_kind': 'unknown',
            }
            records.append(rec)
            record_by_key[key] = rec

        kind, const_or_caller, hash_out_or_ha, _ = resolved
        if kind == 'exit':
            rec['outgoing_hash'] = '0x0'
            rec['exit_target_va'] = '0x0'
            rec['successors'] = []
            rec['passed_vmexit'] = True
            rec['is_vmexit'] = True
            rec['dispatch_kind'] = 'exit'
            augmented += 1
            continue

        if kind == 'native_call':
            handler_after = hash_out_or_ha if isinstance(hash_out_or_ha, int) else 0
            if handler_after:
                rec['successors'] = [f'0x{handler_after:X}']
            if resolver._last_native_target:
                rec['native_target_va'] = f'0x{resolver._last_native_target:X}'
            rec['dispatch_kind'] = 'native_call'
            augmented += 1
            continue

        if kind != 'dispatch':
            continue

        target = (const_or_caller + BASE_DELTA) & 0xFFFFFFFFFFFFFFFF
        dtype, dinfo = resolver.classify_dispatch_entry(target)
        rec['exit_target_va'] = f'0x{target:X}'
        rec['outgoing_hash'] = f'0x{hash_out_or_ha:X}' if hash_out_or_ha else '0x0'
        if dtype == 'jmp':
            succ = dinfo.get('handler', 0)
            rec['successors'] = [f'0x{succ:X}'] if succ else []
            rec['dispatch_kind'] = 'jmp'
            augmented += 1
        elif dtype == 'native_call':
            handler_after = dinfo.get('handler_after', 0)
            rec['successors'] = [f'0x{handler_after:X}'] if handler_after else []
            if resolver._last_native_target:
                rec['native_target_va'] = f'0x{resolver._last_native_target:X}'
            rec['dispatch_kind'] = 'native_call'
            augmented += 1
        elif dtype == 'final_exit':
            rec['successors'] = []
            rec['passed_vmexit'] = True
            rec['is_vmexit'] = True
            rec['dispatch_kind'] = 'final_exit'
            augmented += 1

    if augmented:
        print(f'  Live snapshot augmentation: repaired {augmented} VMTraceRecord(s)')
    return trace_payload


# =============================================================================
#  Per-handler concolic dispatch chain resolver
# =============================================================================

class DispatchChainResolver:
    """Resolve the VM dispatch chain by executing each handler in isolation.

    Instead of tracing the full VM end-to-end (which fails when handlers
    read runtime-initialized pointers), execute each handler independently
    with a clean VM context containing only (hash, base_delta).  The MBA
    dispatch predicates depend only on the hash, so the outgoing const is
    resolved correctly even though the handler's payload reads return garbage.
    """

    # -- Signature bytes --------------------------------------------------
    DISPATCH_SIG = b'\x49\x03\x84\x24\xE0\x00\x00\x00'  # add rax,[r12+0E0h]
    EXIT_CALL    = 0x1402A112B  # vmexit
    WRAPPER_PFX  = b'\x48\x8D\xA4\x24\x40\xFE\xFF\xFF'  # lea rsp,[rsp-1C0h]
    VMENTER      = 0x1402A1000
    HASH_MOV_SIG = b'\x49\xC7\x84\x24\x90\x01\x00\x00'  # mov [r12+190h],imm32

    CTX_SIZE  = 0x1A0
    CTX_STACK = 0x7FFE00700000   # context frame base (in mapped stack region)
    HANDLER_RSP = 0x7FFE00700000 + 0x1A0 + 0x200  # handler rsp (above context)

    def __init__(self, pe_path, db, verbose=0):
        self.db = db
        self.verbose = verbose
        self.pe = pefile.PE(str(pe_path))
        self._pe_ranges = []
        # Build VA -> (section_data, section_va) map for direct byte reads.
        self._sec_map = []
        for sec in self.pe.sections:
            va = self.pe.OPTIONAL_HEADER.ImageBase + sec.VirtualAddress
            data = bytes(sec.get_data())
            self._sec_map.append((va, va + len(data), data))
        self._last_native_target = 0  # native target from most recent resolve_handler

    def _read_va(self, va, size):
        """Read `size` bytes at virtual address `va` from the PE sections."""
        for sec_va, sec_end, sec_data in self._sec_map:
            if sec_va <= va < sec_end:
                off = va - sec_va
                return sec_data[off:off + size]
        return None

    def _make_uc(self):
        """Create a Unicorn instance with PE + KUSD mapped."""
        uc = Uc(UC_ARCH_X86, UC_MODE_64)
        for sec in self.pe.sections:
            va = self.pe.OPTIONAL_HEADER.ImageBase + sec.VirtualAddress
            data = sec.get_data()
            vsize = max(sec.Misc_VirtualSize, len(data))
            size = (vsize + 0xFFF) & ~0xFFF
            if size == 0:
                size = 0x1000
            uc.mem_map(va, size)
            uc.mem_write(va, data[:vsize])
            self._pe_ranges.append((va, va + size))
        # Stack region (covers CTX_STACK and HANDLER_RSP)
        uc.mem_map(STACK_BASE, STACK_SIZE)
        # KUSER_SHARED_DATA
        uc.mem_map(KUSER_SHARED_DATA, KUSD_PAGE_SIZE)
        kusd = bytearray(KUSD_PAGE_SIZE)
        ft = 0x01DA5E9847800000
        struct.pack_into('<I', kusd, 0x14, ft & 0xFFFFFFFF)
        struct.pack_into('<i', kusd, 0x18, (ft >> 32) & 0xFFFFFFFF)
        struct.pack_into('<i', kusd, 0x1C, (ft >> 32) & 0xFFFFFFFF)
        uc.mem_write(KUSER_SHARED_DATA, bytes(kusd))
        return uc

    def _auto_map_hook(self, uc, access, address, size, value, _):
        if access == UC_MEM_FETCH_UNMAPPED:  # code fetch unmapped
            return False
        page = address & ~0xFFF
        try:
            # Map as RW only — no EXEC — so stray jumps to auto-mapped pages
            # cause UC_MEM_FETCH_UNMAPPED instead of running garbage.
            uc.mem_map(page, 0x1000, UC_PROT_READ | UC_PROT_WRITE)
            # Fill with self-referencing pointers (same as VMTracer)
            fill = bytearray(0x1000)
            for off in range(0, 0x1000, 8):
                struct.pack_into('<Q', fill, off, page + off)
            uc.mem_write(page, bytes(fill))
            return True
        except:
            return False

    def resolve_handler(self, handler_va, hash_in, prev_ctx=None, telemetry=None, max_insns=100_000):
        """Execute one handler with given hash.  Returns (kind, const, hash_out, ctx_bytes) or None.
        If prev_ctx is provided (bytes), it is used as the initial VM context
        (with hash/base_delta/rsp overwritten).  Otherwise a fresh context is used.
        """
        self._last_native_target = 0
        uc = self._make_uc()
        if telemetry is not None:
            telemetry.clear()
            telemetry['events'] = []
            telemetry['mem_read_count'] = 0
            telemetry['mem_write_count'] = 0
            telemetry['unmapped_count'] = 0
            telemetry['instr_count'] = 0

        def record_event(kind, address, size, value=None, rip=None):
            if telemetry is None:
                return
            events = telemetry.setdefault('events', [])
            if len(events) >= 64:
                return
            item = {
                'kind': kind,
                'addr': f'0x{address:X}',
                'size': size,
            }
            if value is not None:
                item['value'] = f'0x{value & 0xFFFFFFFFFFFFFFFF:X}'
            if rip is not None:
                item['rip'] = f'0x{rip:X}'
            events.append(item)

        # Hook unmapped memory (data read/write auto-map; code fetch -> log+stop)
        def _unmapped_hook(uc_, access, address, size, value, user):
            if telemetry is not None:
                telemetry['unmapped_count'] += 1
                try:
                    rip = uc_.reg_read(UC_X86_REG_RIP)
                except:
                    rip = None
                kind = {
                    UC_MEM_READ_UNMAPPED: 'read_unmapped',
                    UC_MEM_WRITE_UNMAPPED: 'write_unmapped',
                    UC_MEM_FETCH_UNMAPPED: 'fetch_unmapped',
                }.get(access, 'unmapped')
                record_event(kind, address, size, value=value, rip=rip)
            if access in (UC_MEM_FETCH_UNMAPPED, ):
                if self.verbose >= 2:
                    rip = uc_.reg_read(UC_X86_REG_RIP)
                    print(f'    Code fetch unmapped: addr=0x{address:X} (rip=0x{rip:X})')
                return False
            return self._auto_map_hook(uc_, access, address, size, value, user)
        uc.hook_add(UC_HOOK_MEM_READ_UNMAPPED | UC_HOOK_MEM_WRITE_UNMAPPED |
                    UC_HOOK_MEM_FETCH_UNMAPPED, _unmapped_hook)
        if telemetry is not None:
            def _mem_hook(uc_, access, address, size, value, _user):
                if access == UC_MEM_READ:
                    telemetry['mem_read_count'] += 1
                    record_event('read', address, size, rip=uc_.reg_read(UC_X86_REG_RIP))
                elif access == UC_MEM_WRITE:
                    telemetry['mem_write_count'] += 1
                    record_event('write', address, size, value=value, rip=uc_.reg_read(UC_X86_REG_RIP))
            uc.hook_add(UC_HOOK_MEM_READ | UC_HOOK_MEM_WRITE, _mem_hook)

        ctx_base = self.CTX_STACK
        if prev_ctx is not None:
            ctx = bytearray(prev_ctx)
        else:
            # Fresh context: fill with mapped filler addresses
            ctx = bytearray(self.CTX_SIZE)
            filler = self.HANDLER_RSP + 0x100
            for off in range(0, self.CTX_SIZE, 8):
                struct.pack_into('<Q', ctx, off, filler)
        # Overlay the fields that MUST be correct for dispatch resolution.
        struct.pack_into('<Q', ctx, 0x190, hash_in & 0xFFFFFFFFFFFFFFFF)
        struct.pack_into('<Q', ctx, 0xE0, BASE_DELTA)
        # ctx[0xB8] = "original RSP" before vmenter.  In the real VM,
        # vmenter does `lea rsp,[rsp-1C0h]`, so original_RSP = handler_RSP + 0x1C0.
        # The handler writes the native function pointer to [ctx[0xB8]+8].
        # The RSP+0x1D0 extraction at EXIT_CALL reads from the same location
        # only when ctx[0xB8] = HANDLER_RSP + 0x1C0.
        struct.pack_into('<Q', ctx, 0xB8, self.HANDLER_RSP + 0x1C0)
        uc.mem_write(ctx_base, bytes(ctx))

        # Set registers
        uc.reg_write(UC_X86_REG_R12, ctx_base)
        uc.reg_write(UC_X86_REG_RSP, self.HANDLER_RSP)
        # Write a sentinel return address on the stack
        uc.mem_write(self.HANDLER_RSP, struct.pack('<Q', 0xDEADDEADDEADDEAD))

        # Hook: stop when we hit the dispatch signature or vmexit
        result = {}
        insn_count = [0]
        def hook_code(uc_, address, size, _):
            insn_count[0] += 1
            if telemetry is not None:
                telemetry['instr_count'] = insn_count[0]
            # Check for dispatch: add rax,[r12+0E0h] (match by address bytes, not size)
            try:
                insn = bytes(uc_.mem_read(address, 8))
                if insn == self.DISPATCH_SIG:
                    rax = uc_.reg_read(UC_X86_REG_RAX)
                    const = rax & 0xFFFFFFFF
                    hash_out = struct.unpack('<Q',
                        bytes(uc_.mem_read(ctx_base + 0x190, 8)))[0]
                    result['const'] = const
                    result['hash_out'] = hash_out
                    uc_.emu_stop()
                    return
            except:
                pass
            # Check for vmexit call (handler exits VM directly)
            if address == self.EXIT_CALL:
                # Capture the return address to identify the caller.
                # If the caller is a native call stub, we can parse handler_after.
                try:
                    rsp = uc_.reg_read(UC_X86_REG_RSP)
                    ret_addr = struct.unpack('<Q', bytes(uc_.mem_read(rsp, 8)))[0]
                    result['exit_ret_addr'] = ret_addr
                    # Extract native call target from the stack.
                    # If this exit is via a native call stub, the stub will do:
                    #   lea rsp,[rsp+1C0h]; call [rsp+8]
                    # At vmexit entry, RSP has been decremented by 8 (call pushed
                    # return addr).  So the native target is at:
                    #   (RSP+8) + 0x1C0 + 8 = RSP + 0x1D0
                    native_target = struct.unpack('<Q',
                        bytes(uc_.mem_read(rsp + 0x1D0, 8)))[0]
                    result['exit_native_target'] = native_target
                except:
                    pass
                result['exit'] = True
                result['exit_insns'] = insn_count[0]
                uc_.emu_stop()
                return
        uc.hook_add(UC_HOOK_CODE, hook_code)

        try:
            uc.emu_start(handler_va, 0, timeout=10_000_000, count=max_insns)
        except UcError as e:
            if telemetry is not None:
                telemetry['error'] = str(e)
            if self.verbose >= 2:
                rip = uc.reg_read(UC_X86_REG_RIP)
                print(f'    UcError: {e} after {insn_count[0]} insns  rip=0x{rip:X}')

        # Read output context for chaining to the next handler.
        try:
            out_ctx = bytes(uc.mem_read(ctx_base, self.CTX_SIZE))
        except:
            out_ctx = None

        # Priority 1: dispatch signature found (definitive)
        if 'const' in result:
            return ('dispatch', result['const'], result['hash_out'], out_ctx)

        # Priority 2: recover from ctx[198] (handler wrote dispatch target
        # before the jmp-to-dispatch-loop instruction failed).
        try:
            ctx_198 = struct.unpack('<Q',
                bytes(uc.mem_read(ctx_base + 0x198, 8)))[0]
            ctx_190 = struct.unpack('<Q',
                bytes(uc.mem_read(ctx_base + 0x190, 8)))[0]
        except:
            ctx_198, ctx_190 = 0, 0
        if self.verbose >= 2:
            rip = uc.reg_read(UC_X86_REG_RIP)
            print(f'    No dispatch after {insn_count[0]} insns  rip=0x{rip:X}'
                  f'  ctx[190]={ctx_190:#018x}  ctx[198]={ctx_198:#018x}')

        recovered = self._try_recover_ctx198(ctx_198, out_ctx)
        if recovered:
            return recovered

        # Priority 3: exit classification — only if ctx[198] didn't resolve.
        # Try to recover from the exit return address: if the handler reached
        # vmexit via a native call stub, parse the stub to find handler_after.
        if 'exit' in result:
            ret_addr = result.get('exit_ret_addr', 0)
            if ret_addr:
                # The caller is at ret_addr - 5 (size of `call` instruction).
                caller = ret_addr - 5
                kind, info = self.classify_dispatch_entry(caller)
                if kind == 'native_call':
                    ha = info.get('handler_after', 0)
                    # Extract the native call target that the stub will call
                    # via call [rsp+8].  This was captured from the stack at
                    # vmexit entry (RSP + 0x1D0).
                    native_target = result.get('exit_native_target', 0)
                    # Validate: must be in PE image range to be useful.
                    if native_target:
                        nt_rva = native_target - IMAGEBASE
                        if not (0x1000 <= nt_rva < 0x266F000):
                            native_target = 0
                    self._last_native_target = native_target
                    if self.verbose >= 2:
                        nt_str = f' native_target=0x{native_target:X}' if native_target else ''
                        print(f'    exit via native call stub @ 0x{caller:X} -> handler_after=0x{ha:X}{nt_str}')
                    return ('native_call', caller, ha, out_ctx)
            return ('exit', 0, result.get('exit_insns', 0), out_ctx)

        return None

    def _try_recover_ctx198(self, ctx_198, out_ctx):
        """Try to resolve ctx[198] to a dispatch stub via direct match or thunk chain."""
        # Direct stub_addr match
        s = self.db.by_stub_addr.get(ctx_198)
        if s:
            if self.verbose >= 1:
                print(f'    -> recovered via ctx[198] stub @ 0x{ctx_198:X}  hash=0x{s["hash"]:016X}')
            return ('dispatch', s['const'], s['hash'], out_ctx)
        # Thunk chain
        if ctx_198 != 0:
            addr = ctx_198
            for depth in range(3):
                kind, info = self.classify_dispatch_entry(addr)
                if self.verbose >= 2:
                    print(f'      thunk[{depth}]: addr=0x{addr:X} kind={kind} info={info}')
                if kind != 'jmp':
                    break
                jmp_target = info['handler']
                s = self.db.by_stub_addr.get(jmp_target)
                if s:
                    if self.verbose >= 1:
                        print(f'    -> recovered: ctx[198]=0x{ctx_198:X} -> stub 0x{jmp_target:X}  hash=0x{s["hash"]:016X}')
                    return ('dispatch', s['const'], s['hash'], out_ctx)
                thunk_stubs = self.db.by_thunk.get(jmp_target, [])
                if thunk_stubs:
                    s = thunk_stubs[0]
                    if self.verbose >= 1:
                        print(f'    -> recovered: ctx[198] -> thunk_target=0x{jmp_target:X} -> stub 0x{s["stub_addr"]:X}  hash=0x{s["hash"]:016X}')
                    return ('dispatch', s['const'], s['hash'], out_ctx)
                addr = jmp_target
        return None

    def classify_dispatch_entry(self, target):
        """Classify a dispatch table entry.  Returns (kind, info)."""
        first = self._read_va(target, 35)
        if first is None or len(first) < 5:
            return ('unknown', {})
        if first[0] == 0xE9:  # jmp rel32 -> simple dispatch
            rel = struct.unpack_from('<i', first, 1)[0]
            handler = (target + 5 + rel) & 0xFFFFFFFFFFFFFFFF
            return ('jmp', {'handler': handler})
        if first[0] == 0xE8:  # call -> vmexit entry (native call or final exit)
            rel = struct.unpack_from('<i', first, 1)[0]
            call_tgt = (target + 5 + rel) & 0xFFFFFFFFFFFFFFFF
            if call_tgt != self.EXIT_CALL:
                return ('unknown', {})
            # Check for NATIVE_CALL_MID at +5
            if len(first) >= 25 and first[5:25] == NATIVE_CALL_MID:
                # Native call stub — parse final jmp for handler_after
                if len(first) >= 35 and first[30] == 0xE9:
                    jrel = struct.unpack_from('<i', first, 31)[0]
                    handler_after = (target + 35 + jrel) & 0xFFFFFFFFFFFFFFFF
                else:
                    handler_after = 0
                return ('native_call', {'handler_after': handler_after})
            # Check for final exit: call vmexit + lea + ret
            if len(first) >= 14 and first[13] == 0xC3:
                return ('final_exit', {})
            return ('unknown', {})
        return ('unknown', {})

    def parse_vm_wrapper(self, wrapper_addr):
        """Try to parse a VM re-entry wrapper.  Returns (hash, dispatch_const) or None."""
        # Follow thunk if needed
        raw = self._read_va(wrapper_addr, 5)
        if raw is None:
            return None
        if raw[0] == 0xE9:  # thunk
            rel = struct.unpack_from('<i', raw, 1)[0]
            wrapper_addr = (wrapper_addr + 5 + rel) & 0xFFFFFFFFFFFFFFFF
        d = self._read_va(wrapper_addr, 18)
        if d is None or len(d) < 18:
            return None
        if d[:8] != self.WRAPPER_PFX or d[8] != 0xE8:
            return None
        rel = struct.unpack_from('<i', d, 9)[0]
        if (wrapper_addr + 13 + rel) & 0xFFFFFFFFFFFFFFFF != self.VMENTER:
            return None
        # Follow jmp to post-VM code
        if d[13] != 0xE9:
            return None
        jr = struct.unpack_from('<i', d, 14)[0]
        pv = (wrapper_addr + 18 + jr) & 0xFFFFFFFFFFFFFFFF
        buf = self._read_va(pv, 128)
        if buf is None:
            return None
        # Scan for hash: mov [r12+190h], imm32 (signed 32-bit, sign-extended)
        hv = None
        for i in range(len(buf) - 12):
            if buf[i:i+8] == self.HASH_MOV_SIG:
                hv = struct.unpack_from('<i', buf, i+8)[0]
                break
        # Scan for dispatch const: add rax, imm32
        dc = None
        for i in range(len(buf) - 8):
            if buf[i] == 0x48 and buf[i+1] == 0x05:
                dc = struct.unpack_from('<i', buf, i+2)[0]
                break
            if buf[i] == 0x48 and buf[i+1] == 0x81 and (buf[i+2] & 0xF8) == 0xC0:
                dc = struct.unpack_from('<i', buf, i+3)[0]
                break
        if hv is not None and dc is not None:
            return (hv & 0xFFFFFFFFFFFFFFFF, dc)
        return None

    # -- Byte pattern for ctx[198] (extra/dispatch target) store --
    EXTRA_STORE_DISP = b'\x24\x98\x01\x00\x00'  # SIB + disp32 for [r12+198h]

    def parse_vm_wrapper_full(self, wrapper_addr):
        """Parse a VM re-entry wrapper.  Returns (hash, dispatch_const, first_handler_va) or None.

        Extends parse_vm_wrapper to also extract the first inner handler VA by
        parsing the ctx[198] store (the dispatch loop reads this as the first
        dispatch stub address).
        """
        # Follow thunk if needed
        raw = self._read_va(wrapper_addr, 5)
        if raw is None:
            return None
        if raw[0] == 0xE9:
            rel = struct.unpack_from('<i', raw, 1)[0]
            wrapper_addr = (wrapper_addr + 5 + rel) & 0xFFFFFFFFFFFFFFFF
        d = self._read_va(wrapper_addr, 18)
        if d is None or len(d) < 18:
            return None
        if d[:8] != self.WRAPPER_PFX or d[8] != 0xE8:
            return None
        rel = struct.unpack_from('<i', d, 9)[0]
        if (wrapper_addr + 13 + rel) & 0xFFFFFFFFFFFFFFFF != self.VMENTER:
            return None
        if d[13] != 0xE9:
            return None
        jr = struct.unpack_from('<i', d, 14)[0]
        pv = (wrapper_addr + 18 + jr) & 0xFFFFFFFFFFFFFFFF
        buf = self._read_va(pv, 256)
        if buf is None:
            return None

        # Extract hash: mov [r12+190h], imm32 (sign-extended)
        hv = None
        for i in range(len(buf) - 12):
            if buf[i:i+8] == self.HASH_MOV_SIG:
                hv = struct.unpack_from('<i', buf, i+8)[0]
                break
        # Extract dispatch const: add rax/rdx, imm32
        dc = None
        for i in range(len(buf) - 8):
            if buf[i] == 0x48 and buf[i+1] == 0x05:
                dc = struct.unpack_from('<i', buf, i+2)[0]
                break
            if buf[i] == 0x48 and buf[i+1] == 0x81 and (buf[i+2] & 0xF8) == 0xC0:
                dc = struct.unpack_from('<i', buf, i+3)[0]
                break
            # add rdx, imm32: 48 81 C2 xx xx xx xx
            if buf[i] == 0x48 and buf[i+1] == 0x81 and buf[i+2] == 0xC2:
                dc = struct.unpack_from('<i', buf, i+3)[0]
                break
        if hv is None or dc is None:
            return None
        hv = hv & 0xFFFFFFFFFFFFFFFF

        # Extract ctx[198] (extra): the first dispatch stub of the inner VM.
        # Pattern: 49/4D 89 <modrm> 24 98 01 00 00 where modrm encodes the source reg.
        # Preceding instruction: lea <src_reg>, [<base_reg> + disp32]
        first_handler = 0
        for i in range(len(buf) - 8):
            idx = buf.find(self.EXTRA_STORE_DISP, i)
            if idx == -1:
                break
            if idx < 3:
                i = idx + 1
                continue
            modrm = buf[idx - 1]
            if buf[idx - 2] != 0x89 or buf[idx - 3] not in (0x49, 0x4D):
                i = idx + 1
                continue
            src_reg = (modrm >> 3) & 7
            # Find lea <src_reg>, [any_reg + disp32]
            for j in range(max(0, idx - 25), idx):
                if buf[j] not in (0x48, 0x4C) or buf[j + 1] != 0x8D:
                    continue
                lea_modrm = buf[j + 2]
                if (lea_modrm & 0xC0) != 0x80:  # mod=10 (disp32)
                    continue
                if ((lea_modrm >> 3) & 7) != src_reg:
                    continue
                if (lea_modrm & 7) == 4:  # SIB form — skip
                    continue
                extra_const = struct.unpack_from('<i', buf, j + 3)[0]
                stub_va = (BASE_DELTA + extra_const) & 0xFFFFFFFFFFFFFFFF
                sb = self._read_va(stub_va, 5)
                if sb and sb[0] == 0xE9:
                    rel = struct.unpack_from('<i', sb, 1)[0]
                    first_handler = (stub_va + 5 + rel) & 0xFFFFFFFFFFFFFFFF
                else:
                    first_handler = stub_va
                break
            if first_handler:
                break
            i = idx + 1

        return (hv, dc, first_handler)

    def resolve_native_as_vmenter(self, native_target):
        """Check if a native call target is a VM re-entry wrapper.

        Follows up to 3 thunks from native_target, trying parse_vm_wrapper_full
        at each step.  Returns (hash, dispatch_const, first_handler_va) or None.
        """
        addr = native_target
        for _ in range(3):
            result = self.parse_vm_wrapper_full(addr)
            if result is not None:
                return result
            # Follow thunk
            raw = self._read_va(addr, 5)
            if raw is None or raw[0] != 0xE9:
                return None
            rel = struct.unpack_from('<i', raw, 1)[0]
            addr = (addr + 5 + rel) & 0xFFFFFFFFFFFFFFFF
        return None

    def resolve_inner_vm_chain(self, native_target, max_steps=200, outer_ctx=None):
        """If native_target is a vmenter wrapper, trace the inner VM handler chain.

        Returns a list of edges: [(handler_va, hash_in, next_handler_va, hash_out, const), ...]
        with a final entry marked as 'exit' when the inner VM exits.
        Returns empty list if native_target is not a vmenter wrapper.
        """
        entry = self.resolve_native_as_vmenter(native_target)
        if entry is None:
            return []
        inner_hash, inner_dc, first_handler = entry
        if not first_handler:
            return []
        if self.verbose >= 1:
            print(f'    [inner VM] native 0x{native_target:X} -> vmenter hash=0x{inner_hash:016X} handler=0x{first_handler:X}')

        chain = self.trace_chain(first_handler, inner_hash, max_steps=max_steps, initial_ctx=outer_ctx)
        return chain

    def resolve_native_wrapper(self, stub_target, hash_val, out_ctx):
        """Try to resolve the hash continuation after a native call stub."""
        # Not yet implemented for trace_chain. Requires knowing which
        # wrapper the native function dispatches to.
        return None

    def scan_all_wrappers(self):
        """Scan the PE for all VM re-entry wrappers and return their hashes."""
        results = []
        for sec_va, sec_end, sec_data in self._sec_map:
            pos = 0
            while pos < len(sec_data) - 18:
                idx = sec_data.find(self.WRAPPER_PFX, pos)
                if idx == -1:
                    break
                va = sec_va + idx
                r = self.parse_vm_wrapper(va)
                if r:
                    results.append({'addr': va, 'hash': r[0], 'const': r[1]})
                pos = idx + 1
        return results

    def trace_chain(self, first_handler, first_hash, max_steps=50, initial_ctx=None):
        """Walk the dispatch chain step by step, chaining context between handlers.
        If initial_ctx is provided (bytes), it is used as context for the first handler.
        """
        chain = []
        handler = first_handler
        hash_val = first_hash
        prev_ctx = initial_ctx  # None means resolve_handler uses fresh context

        for step in range(1, max_steps + 1):
            r = self.resolve_handler(handler, hash_val, prev_ctx=prev_ctx)
            if r is None:
                if self.verbose:
                    print(f'  [{step}] FAIL: handler 0x{handler:X} hash=0x{hash_val:016X} -- no dispatch')
                break

            kind, const, hash_out, out_ctx = r
            prev_ctx = out_ctx  # chain to next step

            if kind == 'exit':
                chain.append({'step': step, 'handler': handler, 'hash_in': hash_val,
                              'kind': 'exit'})
                if self.verbose:
                    print(f'  [{step}] 0x{handler:X} hash=0x{hash_val:016X} -> EXIT')
                break

            target = (const + BASE_DELTA) & 0xFFFFFFFFFFFFFFFF
            dtype, dinfo = self.classify_dispatch_entry(target)

            entry = {'step': step, 'handler': handler, 'hash_in': hash_val,
                     'hash_out': hash_out, 'const': const, 'target': target,
                     'dispatch_kind': dtype}

            if dtype == 'jmp':
                next_handler = dinfo['handler']
                entry['next_handler'] = next_handler
                if self.verbose:
                    print(f'  [{step}] 0x{handler:X} h=0x{hash_val:016X} -> const=0x{const:06X} -> jmp 0x{next_handler:X}')
                chain.append(entry)
                handler = next_handler
                hash_val = hash_out

            elif dtype == 'native_call':
                entry['handler_after'] = dinfo.get('handler_after', 0)
                if self.verbose:
                    print(f'  [{step}] 0x{handler:X} h=0x{hash_val:016X} -> const=0x{const:06X} -> NATIVE CALL STUB @ 0x{target:X}')
                chain.append(entry)
                # Try to resolve the native call wrapper to continue the chain.
                # The handler_after is where execution continues post-native-call.
                ha = dinfo.get('handler_after', 0)
                if ha:
                    # The dispatch stub AFTER the native call sets the hash.
                    # Look for a wrapper that provides (hash, const) for continuation.
                    wrapper_result = self.resolve_native_wrapper(target, hash_val, out_ctx)
                    if wrapper_result:
                        handler = ha
                        hash_val = wrapper_result[0]  # next hash
                        continue
                break

            elif dtype == 'final_exit':
                entry['kind'] = 'final_exit'
                if self.verbose:
                    print(f'  [{step}] 0x{handler:X} h=0x{hash_val:016X} -> const=0x{const:06X} -> FINAL EXIT @ 0x{target:X}')
                chain.append(entry)
                break

            else:
                if self.verbose:
                    print(f'  [{step}] 0x{handler:X} h=0x{hash_val:016X} -> const=0x{const:06X} -> UNKNOWN @ 0x{target:X}')
                chain.append(entry)
                break

        return chain

# =============================================================================
#  Main
# =============================================================================

def main():
    print("EasyAntiCheat VM Tracer")
    print("=" * 70)

    # 1. Load dispatch stub database
    pe_path = BINARY_PATH
    if STUBS_JSON.exists():
        print(f"\nLoading stub database from {STUBS_JSON.name}...")
        db = DispatchDB(stubs_path=STUBS_JSON)
    else:
        print(f"\nExtracting stubs from PE...")
        db = DispatchDB(pe_path=pe_path)
    db.print_summary()

    # 2. Show static resolution examples
    print(f"\n{'='*70}")
    print(f" Static Dispatch Resolution (first 20 by address)")
    print(f"{'='*70}")
    print(f" {'Const':>10}  {'Target':>18}  {'Handler':>18}  {'Hash':>18}  {'Extra':>18}")
    print(f" {'-'*10}  {'-'*18}  {'-'*18}  {'-'*18}  {'-'*18}")

    for s in sorted(db.stubs, key=lambda x: x['stub_addr'])[:20]:
        h = f"0x{s['hash']:016X}" if s['hash'] else "--"
        t = f"0x{s['thunk_target']:X}" if s['thunk_target'] else "--"
        ex = f"0x{s['extra']:016X}" if s.get('extra') is not None else "--"
        print(f" 0x{s['const']:08X}  0x{s['target']:016X}  {t:>18s}  {h}  {ex}")

    # 3. Show handler fanin examples
    print(f"\n{'='*70}")
    print(f" Handler Fan-in (stubs dispatching TO a handler)")
    print(f"{'='*70}")
    for h_va in [0x140C5416E, 0x141448082]:
        incoming = db.stubs_for_handler(h_va)
        print(f"\n Handler 0x{h_va:X}: {len(incoming)} incoming stubs")
        for s in incoming[:5]:
            h = f"0x{s['hash']:016X}" if s['hash'] else "--"
            print(f"   stub@0x{s['stub_addr']:X}  hash={h}  const=0x{s['const']:06X}")

    resolver = DispatchChainResolver(str(pe_path), db, verbose=0)

    # 4. Run emulation trace
    print("\nLoading binary for emulation...")
    tracer = VMTracer(str(pe_path), db, verbose=2, resolver=resolver)
    trace = tracer.run(max_steps=5000)

    # 5. Static hash-chain trace from observed hashes
    if trace:
        observed = [t['hash'] for t in trace]
        static_trace(db, observed)

    # 5b. Export omill-compatible VMTraceRecord JSON
    unicorn_trace_payload = None
    if trace:
        trace_json = Path(r"D:\binsnake\tracer\vm_trace_records.json")
        unicorn_trace_payload = export_omill_trace_json(trace, db, trace_json)
        unicorn_trace_payload = augment_records_with_live_snapshots(
            trace, unicorn_trace_payload, resolver)
        export_native_call_artifacts(trace, Path(r"D:\binsnake\tracer"))
        concrete_out = Path(r"D:\binsnake\tracer\vm_trace_concrete.json")
        with open(concrete_out, 'w') as f:
            json.dump(unicorn_trace_payload, f, indent=2)
        print(f"  Concrete export: {len(unicorn_trace_payload['records'])} VMTraceRecords -> {concrete_out}")

    # 6. Trace summary table
    print(f"\n{'='*70}")
    print(f" Trace Summary")
    print(f"{'='*70}")
    print(f" {'Step':>5}  {'Const':>10}  {'Target':>18}  {'Handler':>18}  {'Hash':>18}")
    print(f" {'-'*5}  {'-'*10}  {'-'*18}  {'-'*18}  {'-'*18}")
    for t in trace:
        dest = f"0x{t['thunk']:X}" if t.get('thunk') else "--"
        print(f" {t['step']:5d}  0x{t['const']:08X}  0x{t['target']:016X}  {dest:>18s}  0x{t['hash']:016X}")

    # 7. Write full resolution table
    out = Path(r"D:\binsnake\tracer\resolved_targets.txt")
    with open(out, 'w') as f:
        f.write(f"# EasyAntiCheat VM -- Resolved Dispatch Targets\n")
        f.write(f"# Formula: target = constant + 0x{BASE_DELTA:X}\n")
        f.write(f"# {len(db.stubs)} dispatch stubs, {len(db.by_target)} unique targets\n")
        f.write(f"# {sum(1 for s in db.stubs if s.get('extra') is not None)} stubs with extra field\n\n")
        f.write(f"{'Stub Address':>14}  {'Constant':>10}  {'Target VA':>18}  "
                f"{'Handler VA':>18}  {'Hash':>18}  {'Extra':>18}\n")
        f.write("-" * 115 + "\n")
        for s in sorted(db.stubs, key=lambda x: x['stub_addr']):
            h = f"0x{s['hash']:016X}" if s['hash'] else "--"
            e = f"0x{s['extra']:016X}" if s.get('extra') is not None else "--"
            t = f"0x{s['thunk_target']:X}" if s['thunk_target'] else "--"
            f.write(f"0x{s['stub_addr']:012X}  0x{s['const']:08X}  "
                    f"0x{s['target']:016X}  {t:>18s}  {h}  {e}\n")

    print(f"\n Full resolution table: {out}")
    print(f" {len(db.stubs)} dispatch stubs resolved.")

    # 8. Per-handler concolic dispatch graph: resolve every handler in the DB.
    print(f"\n{'='*70}")
    print(f" Concolic Dispatch Graph (per-handler isolation)")
    print(f"{'='*70}")
    if unicorn_trace_payload:
        unicorn_trace_payload = bridge_unicorn_trace_records(trace, unicorn_trace_payload, resolver)
    # Collect (handler_va -> thunk_target) from all stubs with known handlers.
    handler_hashes = {}  # handler_va -> list of (hash, stub_addr)
    for s in db.stubs:
        h_va = s.get('thunk_target') or s.get('target')
        if h_va and s.get('hash'):
            handler_hashes.setdefault(h_va, []).append((s['hash'], s['stub_addr']))
    unique_handlers = list(handler_hashes.keys())
    print(f"  {len(unique_handlers)} unique handlers to resolve")

    resolved = 0
    failed = 0
    edges = {}  # (handler_va, hash_in) -> (next_handler_va, hash_out, const)
    native_target_for_edge = {}  # (handler_va, hash_in) -> resolved native target VA
    exits = set()  # handlers that exit the VM
    ctx_out = {}  # handler_va -> output context bytes (for chaining)
    failed_set = set()  # handler VAs that failed first-pass resolution
    for i, h_va in enumerate(unique_handlers):
        pairs = handler_hashes[h_va]
        # Try the first hash for this handler.
        hash_in = pairs[0][0]
        r = resolver.resolve_handler(h_va, hash_in)
        if r is not None:
            kind, const_or_caller, hash_out_or_ha, out_ctx = r
            if out_ctx:
                ctx_out[h_va] = out_ctx
            if kind == 'exit':
                exits.add(h_va)
                resolved += 1
            elif kind == 'native_call':
                ha = hash_out_or_ha
                if ha:
                    edges[(h_va, hash_in)] = ('native_call_stub', 0, const_or_caller)
                    if resolver._last_native_target:
                        native_target_for_edge[(h_va, hash_in)] = resolver._last_native_target
                resolved += 1
            elif kind == 'dispatch':
                target = (const_or_caller + BASE_DELTA) & 0xFFFFFFFFFFFFFFFF
                dtype, dinfo = resolver.classify_dispatch_entry(target)
                if dtype == 'jmp':
                    next_h = dinfo['handler']
                    edges[(h_va, hash_in)] = (next_h, hash_out_or_ha, const_or_caller)
                    resolved += 1
                elif dtype == 'native_call':
                    edges[(h_va, hash_in)] = ('native_call', hash_out_or_ha, const_or_caller)
                    resolved += 1
                elif dtype == 'final_exit':
                    exits.add(h_va)
                    resolved += 1
                else:
                    failed += 1
                    failed_set.add(h_va)
        else:
            failed += 1
            failed_set.add(h_va)
        if (i + 1) % 500 == 0:
            print(f"    [{i+1}/{len(unique_handlers)}] resolved={resolved} failed={failed}")

    print(f"\n  Pass 1: {resolved} resolved, {failed} failed, {len(exits)} exits, {len(native_target_for_edge)} native targets")

    # Context chaining: retry failed handlers using predecessor's output context.
    # Build reverse map: handler_va -> list of predecessor handler_vas.
    successor_to_pred = {}  # handler_va -> (pred_handler_va, pred_hash_in)
    for (h, hi), (nh, ho, c) in edges.items():
        if isinstance(nh, int) and nh in failed_set:
            successor_to_pred.setdefault(nh, []).append((h, hi))
    chain_pass = 0
    while True:
        chain_pass += 1
        retried = 0
        newly_resolved = 0
        retry_candidates = []
        for h_va in list(failed_set):
            preds = successor_to_pred.get(h_va, [])
            for pred_h, pred_hi in preds:
                if pred_h in ctx_out:
                    retry_candidates.append((h_va, pred_h, pred_hi))
                    break
        if not retry_candidates:
            break
        for h_va, pred_h, pred_hi in retry_candidates:
            pairs = handler_hashes.get(h_va, [])
            if not pairs:
                continue
            hash_in = pairs[0][0]
            prev = ctx_out.get(pred_h)
            r = resolver.resolve_handler(h_va, hash_in, prev_ctx=prev)
            retried += 1
            if r is not None:
                kind, const_or_caller, hash_out_or_ha, out_ctx = r
                if out_ctx:
                    ctx_out[h_va] = out_ctx
                if kind == 'exit':
                    exits.add(h_va)
                    newly_resolved += 1
                elif kind == 'native_call':
                    ha = hash_out_or_ha
                    if ha:
                        edges[(h_va, hash_in)] = ('native_call_stub', 0, const_or_caller)
                        if resolver._last_native_target:
                            native_target_for_edge[(h_va, hash_in)] = resolver._last_native_target
                    newly_resolved += 1
                elif kind == 'dispatch':
                    target = (const_or_caller + BASE_DELTA) & 0xFFFFFFFFFFFFFFFF
                    dtype, dinfo = resolver.classify_dispatch_entry(target)
                    if dtype == 'jmp':
                        next_h = dinfo['handler']
                        edges[(h_va, hash_in)] = (next_h, hash_out_or_ha, const_or_caller)
                        newly_resolved += 1
                        # New edge may unlock more retries
                        if next_h in failed_set:
                            successor_to_pred.setdefault(next_h, []).append((h_va, hash_in))
                    elif dtype == 'native_call':
                        edges[(h_va, hash_in)] = ('native_call', hash_out_or_ha, const_or_caller)
                        newly_resolved += 1
                    elif dtype == 'final_exit':
                        exits.add(h_va)
                        newly_resolved += 1
                if h_va in failed_set:
                    failed_set.discard(h_va)
                    resolved += 1
                    failed -= 1
        print(f"  Chain pass {chain_pass}: retried {retried}, newly resolved {newly_resolved}, remaining {len(failed_set)}")
        if newly_resolved == 0:
            break

    # Generic context retry: use the best available context from any resolved
    # handler as a "warm" context for remaining failures.  The key dispatch fields
    # (hash, base_delta, rsp) are overwritten by resolve_handler, so a realistic
    # context with valid pointer patterns is far better than filler.
    if failed_set and ctx_out:
        # Pick the context from the most recently resolved handler with a successor.
        best_ctx = None
        for (h, hi), (nh, ho, c) in edges.items():
            if isinstance(nh, int) and h in ctx_out:
                best_ctx = ctx_out[h]
                break
        if best_ctx is None:
            best_ctx = next(iter(ctx_out.values()))
        generic_resolved = 0
        generic_retried = 0
        for h_va in list(failed_set):
            pairs = handler_hashes.get(h_va, [])
            if not pairs:
                continue
            hash_in = pairs[0][0]
            r = resolver.resolve_handler(h_va, hash_in, prev_ctx=best_ctx)
            generic_retried += 1
            if r is not None:
                kind, const_or_caller, hash_out_or_ha, out_ctx = r
                if out_ctx:
                    ctx_out[h_va] = out_ctx
                if kind == 'exit':
                    exits.add(h_va)
                    generic_resolved += 1
                elif kind == 'native_call':
                    ha = hash_out_or_ha
                    if ha:
                        edges[(h_va, hash_in)] = ('native_call_stub', 0, const_or_caller)
                    generic_resolved += 1
                elif kind == 'dispatch':
                    target = (const_or_caller + BASE_DELTA) & 0xFFFFFFFFFFFFFFFF
                    dtype, dinfo = resolver.classify_dispatch_entry(target)
                    if dtype == 'jmp':
                        next_h = dinfo['handler']
                        edges[(h_va, hash_in)] = (next_h, hash_out_or_ha, const_or_caller)
                        generic_resolved += 1
                    elif dtype == 'native_call':
                        edges[(h_va, hash_in)] = ('native_call', hash_out_or_ha, const_or_caller)
                        generic_resolved += 1
                    elif dtype == 'final_exit':
                        exits.add(h_va)
                        generic_resolved += 1
                if h_va in failed_set:
                    failed_set.discard(h_va)
                    resolved += 1
                    failed -= 1
            if generic_retried % 200 == 0:
                print(f"    [generic {generic_retried}/{len(failed_set)+generic_retried}] resolved={generic_resolved}")
        print(f"  Generic context retry: {generic_retried} retried, {generic_resolved} resolved, {len(failed_set)} remaining")

    print(f"\n Results: {resolved} resolved, {failed} failed, {len(exits)} exits")
    print(f"  {len(edges)} dispatch edges")
    # Validate against known trace: find edge for handler 0x140C5416E (any hash)
    expected_nh = 0x141448082
    expected_c = 0x2E9C37
    expected_ho = 0xE5D3BDF5888D2147
    found = False
    for (h, hi), (nh, ho, c) in edges.items():
        if h == 0x140C5416E:
            found = True
            print(f"  VALIDATION: handler 0x{h:X} (hash=0x{hi:016X})")
            if isinstance(nh, int):
                print(f"    -> next=0x{nh:X} const=0x{c:06X} hash_out=0x{ho:016X}")
                if nh == expected_nh and c == expected_c and ho == expected_ho:
                    print(f"  VALIDATION PASSED")
                else:
                    print(f"  VALIDATION MISMATCH")
            break
    if not found:
        print(f"  VALIDATION: handler 0x140C5416E not in edges")
    # (Graph export moved to after native call extension)

    # 8a-ctx. Context-propagation pass for native call target resolution.
    # The dispatch graph is correct (dispatch depends only on hash), but native
    # call targets depend on ctx[0x108] (RAX) which was filler in Pass 1.
    # Walk the graph from the entry point, propagating full context, and
    # re-resolve native call handlers with the correct predecessor context.
    nc_edges_set = set()  # (h_va, hash_in) keys that are native call edges
    for (h, hi), (nh, ho, c) in edges.items():
        if isinstance(nh, str) and 'native_call' in nh:
            nc_edges_set.add((h, hi))
    if nc_edges_set:
        print(f"\n  Context-propagation pass for {len(nc_edges_set)} native call edges...")
        # Build predecessor map: handler_va -> set of predecessor (handler_va, hash_in)
        pred_map = {}  # handler_va -> list of (pred_handler_va, pred_hash_in)
        for (h, hi), (nh, ho, c) in edges.items():
            if isinstance(nh, int):
                pred_map.setdefault(nh, []).append((h, hi))
        # BFS from entry handler, propagating context through the graph.
        # We re-resolve each handler with its predecessor's output context to
        # build an accurate ctx_out chain.  Only handlers on paths leading to
        # native call edges need full re-resolution, but for simplicity we
        # propagate through all reachable handlers (it's fast — Unicorn runs
        # are ~0.01s each).
        entry_h = 0x140C5416E
        # Find the entry handler's hash from handler_hashes.
        entry_hash = handler_hashes.get(entry_h, [(INITIAL_HASH, 0)])[0][0]
        # Re-resolve entry handler with a context where RAX=0 (as set by vmenter
        # when called from DriverEntry with RAX=0).
        import copy
        initial_ctx = bytearray(resolver.CTX_SIZE)
        filler = resolver.HANDLER_RSP + 0x100
        for off in range(0, resolver.CTX_SIZE, 8):
            struct.pack_into('<Q', initial_ctx, off, filler)
        struct.pack_into('<Q', initial_ctx, 0x190, entry_hash & 0xFFFFFFFFFFFFFFFF)
        struct.pack_into('<Q', initial_ctx, 0xE0, BASE_DELTA)
        struct.pack_into('<Q', initial_ctx, 0xB8, resolver.HANDLER_RSP + 0x1C0)
        # Set RAX (ctx[0x108]) to 0 — the value from DriverEntry via vmenter.
        struct.pack_into('<Q', initial_ctx, 0x108, 0)
        prop_ctx = {}  # (handler_va, hash_in) -> output context bytes
        r = resolver.resolve_handler(entry_h, entry_hash, prev_ctx=bytes(initial_ctx))
        if r:
            _, _, _, out_ctx_entry = r
            if out_ctx_entry:
                prop_ctx[(entry_h, entry_hash)] = out_ctx_entry
        # BFS through the graph, propagating context.
        from collections import deque
        ctx_queue = deque()  # (handler_va, hash_in, prev_ctx_bytes)
        # Seed the queue with successors of the entry handler.
        for (h, hi), (nh, ho, c) in edges.items():
            if h == entry_h and isinstance(nh, int) and (entry_h, hi) in prop_ctx:
                # Find the hash for the successor handler.
                for shi, _ in handler_hashes.get(nh, []):
                    ctx_queue.append((nh, shi, prop_ctx[(entry_h, hi)]))
                    break  # one hash per successor is enough for context propagation
        visited_prop = {(entry_h, entry_hash)}
        native_resolved_ctx = 0
        while ctx_queue:
            h_va, hash_in, prev = ctx_queue.popleft()
            key = (h_va, hash_in)
            if key in visited_prop:
                continue
            visited_prop.add(key)
            r = resolver.resolve_handler(h_va, hash_in, prev_ctx=prev)
            if r is None:
                continue
            kind, const_or_caller, hash_out_or_ha, out_ctx_h = r
            if out_ctx_h:
                prop_ctx[key] = out_ctx_h
            # If this handler dispatches to a native call, capture the target.
            if key in nc_edges_set:
                nt = resolver._last_native_target
                if nt and nt not in (0, filler):
                    # Validate: must be in PE image range.
                    nt_rva = nt - IMAGEBASE
                    if 0x1000 <= nt_rva < 0x266F000:
                        native_target_for_edge[key] = nt
                        native_resolved_ctx += 1
            # Propagate to successors.
            if kind == 'dispatch' and out_ctx_h:
                target = (const_or_caller + BASE_DELTA) & 0xFFFFFFFFFFFFFFFF
                dtype, dinfo = resolver.classify_dispatch_entry(target)
                if dtype == 'jmp':
                    next_h = dinfo['handler']
                    for shi, _ in handler_hashes.get(next_h, []):
                        if (next_h, shi) not in visited_prop:
                            ctx_queue.append((next_h, shi, out_ctx_h))
                        break
            elif kind == 'native_call' and out_ctx_h:
                # After a native call, the handler_after continues.
                ha = hash_out_or_ha
                if isinstance(ha, int) and ha:
                    for shi, _ in handler_hashes.get(ha, []):
                        if (ha, shi) not in visited_prop:
                            ctx_queue.append((ha, shi, out_ctx_h))
                        break
        print(f"    Propagated context through {len(visited_prop)} handlers")
        print(f"    Resolved {native_resolved_ctx} native call targets via context propagation")

    # 8b. Cross-reference e2e trace native calls into native_target_for_edge.
    # The Unicorn emulation captures the actual call [rsp+8] value for native
    # call stubs it traverses.  Use this to fill in native targets for edges
    # that the concolic resolver couldn't extract from its stack simulation.
    if trace:
        e2e_handler_native = {}  # handler_va -> native_target_va (hash-independent)
        for step in trace:
            # native_target_va is set on any step whose handler makes a
            # native call, regardless of how the handler was dispatched to.
            nt = step.get('native_target_va', 0)
            if nt:
                h_va = step.get('thunk') or step.get('target', 0)
                if h_va:
                    e2e_handler_native[h_va] = nt
        # A handler makes the same native call regardless of its incoming hash.
        # Populate native_target_for_edge for ALL known hashes of each handler,
        # not just the hash observed in the e2e trace.
        # E2E trace values are the most reliable (observed in real execution),
        # so they OVERRIDE any existing values from Pass 1 or context propagation.
        e2e_count = 0
        for h_va, nt in e2e_handler_native.items():
            hashes = handler_hashes.get(h_va, [])
            for (h_in, _) in hashes:
                key = (h_va, h_in)
                native_target_for_edge[key] = nt
                e2e_count += 1
        if e2e_handler_native:
            print(f"  E2E trace: {len(e2e_handler_native)} handler(s) with native targets -> {e2e_count} edge entries")
    print(f"  Total native_target_for_edge: {len(native_target_for_edge)} entries")

    # 9a. Scan VM re-entry wrappers and collect unique hashes.
    wrappers = resolver.scan_all_wrappers()
    wrapper_hashes = set(w['hash'] for w in wrappers)
    print(f"  {len(wrappers)} VM re-entry wrappers parsed, {len(wrapper_hashes)} unique hashes")

    # Validate native targets: check which are vmenter wrappers.
    wrapper_addrs = set(w['addr'] for w in wrappers)
    # Also collect thunk-resolved wrapper bodies.
    wrapper_bodies = set()
    for w in wrappers:
        raw = resolver._read_va(w['addr'], 5)
        if raw and raw[0] == 0xE9:
            rel = struct.unpack_from('<i', raw, 1)[0]
            body = (w['addr'] + 5 + rel) & 0xFFFFFFFFFFFFFFFF
            wrapper_bodies.add(body)
    all_wrapper_vas = wrapper_addrs | wrapper_bodies
    nt_wrapper_count = sum(1 for nt in native_target_for_edge.values() if nt in all_wrapper_vas)
    print(f"  Native targets: {len(native_target_for_edge)} total, {nt_wrapper_count} are vmenter wrappers")

    # 9b. For native_call_stub edges, try to resolve handler_after.
    # Cache by handler_after so we don't re-test the same continuation handler.
    native_extended = 0
    nc_edges = [(h, hi, nh, ho, c) for (h, hi), (nh, ho, c) in edges.items() if isinstance(nh, str)]
    # Collect unique (caller -> handler_after) pairs
    ha_cache = {}  # handler_after -> (wh, next_h, nc_hash_out, nc_const) or None
    unique_has = set()  # unique handler_after addresses
    for h_va, hash_in, kind, _, caller in nc_edges:
        if not caller or not isinstance(caller, int):
            continue
        nk, ninfo = resolver.classify_dispatch_entry(caller)
        if nk != 'native_call':
            continue
        ha = ninfo.get('handler_after', 0)
        if ha:
            unique_has.add(ha)
    print(f"  {len(unique_has)} unique handler_after targets from {len(nc_edges)} native call edges")
    # Resolve each unique handler_after with each wrapper hash
    sorted_wh = sorted(wrapper_hashes)
    for i, ha in enumerate(sorted(unique_has)):
        if ha in ha_cache:
            continue
        ha_cache[ha] = None
        for wh in sorted_wh:
            r = resolver.resolve_handler(ha, wh)
            if r and r[0] == 'dispatch':
                _, nc_const, nc_hash_out, _ = r
                target = (nc_const + BASE_DELTA) & 0xFFFFFFFFFFFFFFFF
                dtype, dinfo = resolver.classify_dispatch_entry(target)
                if dtype == 'jmp':
                    next_h = dinfo['handler']
                    ha_cache[ha] = (wh, next_h, nc_hash_out, nc_const)
                    edges[(ha, wh)] = (next_h, nc_hash_out, nc_const)
                    native_extended += 1
                    break
        if (i + 1) % 100 == 0:
            print(f"    [{i+1}/{len(unique_has)}] extended={native_extended}")
    print(f"  Extended {native_extended} edges through {len(unique_has)} unique handler_after targets")

    # 9c. Resolve inner VM chains: for native_call edges where the native
    #     target is a vmenter wrapper, trace the inner VM handler chain
    #     and add those edges to the dispatch graph.
    print(f"\n  Inner VM chain resolution...")
    inner_vm_entries = {}  # native_target_va -> (inner_hash, first_handler_va)
    inner_vm_edges = 0
    # Collect all native call targets from edges
    native_targets = set()
    native_edge_info = {}  # (h_va, hash_in) -> caller_addr (the native call stub)
    for (h, hi), (nh, ho, c) in edges.items():
        if isinstance(nh, str) and nh.startswith('native_call'):
            caller = c  # for native_call edges, c = caller_addr (the stub)
            if isinstance(caller, int):
                nk, ninfo = resolver.classify_dispatch_entry(caller)
                if nk == 'native_call':
                    ha = ninfo.get('handler_after', 0)
                    if ha:
                        native_edge_info[(h, hi)] = (caller, ha)
    # For each native call edge, find the actual native target.
    # The native target is the function called at [rsp+8] inside the stub.
    # We can read the native target from the stub's call [rsp+8] instruction.
    # For now, we use the end-to-end trace data if available, or we try to
    # detect vmenter wrappers among all known thunk targets in the binary.
    #
    # Strategy: for each handler_after, check if ANY of the known vmenter
    # wrappers produce a valid inner VM chain. Since the native target is
    # only known at runtime (it's read from [rsp+8]), we check whether
    # known thunk targets near native call stubs are wrappers.
    #
    # Actually, the robust approach: we already have the 351 wrappers.
    # Build a map: wrapper_body_addr -> (hash, dc, first_handler).
    # Then for each native call stub, the jmp at offset 30 gives handler_after,
    # but the call at offset 13 (call [rsp+8]) calls the native target which
    # at RUNTIME may be a wrapper.  We can't know statically which wrapper it is.
    #
    # Instead: for the outer handler that makes the native call, use the e2e trace
    # (if available) or the dispatch graph's native_target_va to identify the wrapper.
    # For a broader solution, for each native_call_stub edge, try resolving
    # handler_after with the hash from each wrapper (37 hashes) and if the
    # handler_after dispatches to a known handler, that inner chain is valid.
    #
    # Simplest approach for now: scan the e2e trace's native_calls list.
    # If a native call target is a vmenter wrapper, trace its inner chain.
    #
    # Even simpler: for each unique wrapper (37 hashes), resolve the inner VM chain
    # starting from its first_handler.  These chains are independent of which
    # native call stub invoked them.  Then link native_call edges that target
    # a vmenter wrapper to the inner chain's first handler.
    #
    # Build: inner_hash -> [(handler, hash_in, next_handler, hash_out, const), ...]
    wrapper_db = {}  # wrapper_hash -> {first_handler, chain: [...]}
    seen_wrapper_hashes = set()
    for w in wrappers:
        wh = w['hash']
        if wh in seen_wrapper_hashes:
            continue
        seen_wrapper_hashes.add(wh)
        result = resolver.parse_vm_wrapper_full(w['addr'])
        if result is None:
            continue
        inner_hash, inner_dc, first_handler = result
        if not first_handler:
            continue
        wrapper_db[wh] = {'first_handler': first_handler, 'chain': None}
    print(f"  {len(wrapper_db)} unique vmenter wrappers with known first handlers")

    # Now trace each inner VM chain (only unique first_handlers).
    # Use a warm context from the main resolution pass — inner VM handlers
    # need realistic pointer values (not filler) for context fields like
    # ctx[0x108], ctx[0xB8], etc.
    warm_ctx = None
    if ctx_out:
        for (h, hi), (nh, ho, c) in edges.items():
            if isinstance(nh, int) and h in ctx_out:
                warm_ctx = ctx_out[h]
                break
        if warm_ctx is None:
            warm_ctx = next(iter(ctx_out.values()))
    first_handler_to_chain = {}  # first_handler -> chain
    for wh, winfo in wrapper_db.items():
        fh = winfo['first_handler']
        if fh in first_handler_to_chain:
            winfo['chain'] = first_handler_to_chain[fh]
            continue
        chain = resolver.trace_chain(fh, wh, max_steps=200, initial_ctx=warm_ctx)
        winfo['chain'] = chain
        first_handler_to_chain[fh] = chain
        # Add chain edges to the main edges dict
        for step in chain:
            h_va = step['handler']
            h_in = step['hash_in']
            if 'next_handler' in step:
                nh = step['next_handler']
                ho = step.get('hash_out', 0)
                c = step.get('const', 0)
                key = (h_va, h_in)
                if key not in edges:
                    edges[key] = (nh, ho, c)
                    inner_vm_edges += 1
            elif step.get('kind') == 'exit':
                exits.add(h_va)
            elif step.get('dispatch_kind') == 'native_call':
                ha = step.get('handler_after', 0)
                c = step.get('const', 0)
                target = step.get('target', 0)
                key = (h_va, h_in)
                if key not in edges:
                    edges[key] = ('native_call', 0, target)
                    inner_vm_edges += 1
    print(f"  Traced {len(first_handler_to_chain)} unique inner VM chains, added {inner_vm_edges} edges")

    # Build lookup: first_handler -> wrapper_hash (for linking native call edges)
    first_handler_to_whash = {}  # first_handler -> wrapper_hash
    for wh, winfo in wrapper_db.items():
        fh = winfo['first_handler']
        if fh not in first_handler_to_whash:
            first_handler_to_whash[fh] = wh

    # Also build: wrapper_body_addr -> first_handler (for native target resolution)
    # All wrappers with the same hash share the same first_handler.
    wrapper_addr_to_first = {}  # wrapper body VA -> first_handler
    for w in wrappers:
        result = resolver.parse_vm_wrapper_full(w['addr'])
        if result and result[2]:
            wrapper_addr_to_first[w['addr']] = result[2]
            # Also map thunk targets
            raw = resolver._read_va(w['addr'], 5)
            if raw and raw[0] == 0xE9:
                rel = struct.unpack_from('<i', raw, 1)[0]
                body = (w['addr'] + 5 + rel) & 0xFFFFFFFFFFFFFFFF
                wrapper_addr_to_first[body] = result[2]

    print(f"  {len(wrapper_addr_to_first)} wrapper addresses mapped to first handlers")

    # Final graph export (after native call extension)
    graph_out = Path(r'D:\binsnake\tracer\dispatch_graph.json')
    total_dispatch = sum(1 for (h,_), (nh,_,_) in edges.items() if isinstance(nh, int) and nh != h)
    total_self_loop = sum(1 for (h,_), (nh,_,_) in edges.items() if isinstance(nh, int) and nh == h)
    total_nc = sum(1 for (h,_), (nh,_,_) in edges.items() if isinstance(nh, str))
    graph_data = {
        'stats': {
            'total_handlers': len(unique_handlers),
            'resolved': resolved,
            'failed': failed,
            'exits': len(exits),
            'total_edges': len(edges),
            'dispatch_edges': total_dispatch,
            'self_loops': total_self_loop,
            'native_call_edges': total_nc,
            'native_call_continuations': native_extended,
        },
        'edges': [
            {'handler': f'0x{h:X}', 'hash_in': f'0x{hi:016X}',
             'next_handler': f'0x{nh:X}' if isinstance(nh, int) else str(nh),
             'hash_out': f'0x{ho:016X}' if isinstance(ho, int) else str(ho),
             'const': f'0x{c:06X}' if isinstance(c, int) else str(c)}
            for (h, hi), (nh, ho, c) in edges.items()
        ],
        'exits': [f'0x{h:X}' for h in sorted(exits)],
    }
    with open(graph_out, 'w') as f:
        json.dump(graph_data, f, indent=2)
    print(f"  Total graph: {len(edges)} edges ({total_dispatch} dispatch, {total_self_loop} self-loops, {total_nc} native calls)")
    print(f"  Graph saved to {graph_out}")

    # 10. Export dispatch graph edges as VMTraceRecords for omill-lift.
    # For native_call edges, look up handler_after from the stub and use it as
    # the successor (the handler that resumes after the native call returns).
    # ha_cache maps handler_after -> (wh, next_h, hash_out, const) from step 9b.
    #
    # Build stub -> handler_after lookup.
    stub_to_ha = {}  # caller_addr -> handler_after
    for (h, hi), (nh, ho, c) in edges.items():
        if isinstance(nh, str) and nh.startswith('native_call'):
            caller = c  # const_or_caller for native call edges
            if isinstance(caller, int) and caller not in stub_to_ha:
                nk, ninfo = resolver.classify_dispatch_entry(caller)
                if nk == 'native_call':
                    ha = ninfo.get('handler_after', 0)
                    if ha:
                        stub_to_ha[caller] = ha

    graph_records = []
    seen_keys = set()  # (handler_va, incoming_hash) dedup
    for (h, hi), (nh, ho, c) in edges.items():
        key = (h, hi)
        if key in seen_keys:
            continue
        seen_keys.add(key)
        rec = {
            'handler_va':       f'0x{h:X}',
            'incoming_hash':    f'0x{hi:016X}',
            'outgoing_hash':    '0x0',
            'exit_target_va':   '0x0',
            'native_target_va': '0x0',
            'successors':       [],
            'passed_vmexit':    False,
            'is_vmexit':        False,
            'is_error':         False,
        }
        if isinstance(nh, int):
            rec['successors'] = [f'0x{nh:X}']
            rec['outgoing_hash'] = f'0x{ho:016X}'
        elif isinstance(nh, str) and nh.startswith('native_call'):
            # Native call: set handler_after as successor so VMDispatchResolution
            # can resolve the dispatch_jump to the correct handler.
            caller = c
            ha = stub_to_ha.get(caller, 0) if isinstance(caller, int) else 0
            successors = []
            if ha:
                successors.append(f'0x{ha:X}')
                # Use the resolved native target VA (the function called by
                # call [rsp+8] in the stub) instead of the stub address.
                nt = native_target_for_edge.get((h, hi), 0)
                rec['native_target_va'] = f'0x{nt:X}' if nt else '0x0'
                # If we resolved handler_after's continuation, also set outgoing_hash
                if ha in ha_cache and ha_cache[ha]:
                    _, _, nc_ho, _ = ha_cache[ha]
                    rec['outgoing_hash'] = f'0x{nc_ho:016X}'
            rec['successors'] = successors
        graph_records.append(rec)
    # Mark exit handlers
    for h in exits:
        has_record = any(r['handler_va'] == f'0x{h:X}' for r in graph_records)
        if not has_record:
            graph_records.append({
                'handler_va':       f'0x{h:X}',
                'incoming_hash':    '0x0',
                'outgoing_hash':    '0x0',
                'exit_target_va':   '0x0',
                'native_target_va': '0x0',
                'successors':       [],
                'passed_vmexit':    True,
                'is_vmexit':        True,
                'is_error':         False,
            })

    # Add records for vmenter-wrapper native targets so VMDispatchResolution
    # can resolve their dispatch_jump to the first inner handler.  These are
    # native call targets (e.g. 0x14014F994) that jmp-thunk into a vmenter
    # wrapper body.  The lift pipeline lifts them as sub_<va> and needs a
    # trace record to know where the inner VM chain begins.
    wrapper_native_targets = {}  # native_va -> (seed_hash, first_inner_handler_va)
    all_native_targets = set()
    for (h, hi), nt in native_target_for_edge.items():
        if nt:
            all_native_targets.add(nt)
    for nt_va in all_native_targets:
        entry = resolver.resolve_native_as_vmenter(nt_va)
        if entry is not None:
            inner_hash, inner_dc, first_handler = entry
            if first_handler:
                normalized_first = first_handler
                winfo = wrapper_db.get(inner_hash)
                if winfo:
                    normalized_first = _first_concrete_handler_from_chain(
                        winfo.get('chain'), fallback=first_handler)
                wrapper_native_targets[nt_va] = (inner_hash, normalized_first)
                # Add a record for the native target VA itself.
                key = (f'0x{nt_va:X}', '0x0')
                if key not in seen_keys:
                    seen_keys.add(key)
                    graph_records.append({
                        'handler_va':       f'0x{nt_va:X}',
                        'incoming_hash':    '0x0',
                        'outgoing_hash':    f'0x{inner_hash:X}' if inner_hash else '0x0',
                        'exit_target_va':   '0x0',
                        'native_target_va': '0x0',
                        'successors':       [f'0x{normalized_first:X}'],
                        'passed_vmexit':    False,
                        'is_vmexit':        False,
                        'is_error':         False,
                    })
    if wrapper_native_targets:
        print(f'  Added {len(wrapper_native_targets)} vmenter-wrapper native target records')
        for nt_va, (ih, fh) in sorted(wrapper_native_targets.items()):
            htxt = f' hash=0x{ih:016X}' if ih else ''
            print(f'    0x{nt_va:X}{htxt} -> first_handler 0x{fh:X}')

    unicorn_records = unicorn_trace_payload['records'] if unicorn_trace_payload else []
    merged_records = merge_vmtrace_records(unicorn_records, graph_records)
    merged_records = normalize_wrapper_trace_records(
        merged_records, wrapper_native_targets)

    # Merge with existing Unicorn-traced records (they have priority).
    trace_out = Path(r'D:\binsnake\tracer\vm_trace_records.json')
    trace_data = {
        'vmenter_va': f'0x{VM_ENTRY:X}',
        'vmexit_va': f'0x{VM_EXIT:X}',
        'records': merged_records,
    }
    with open(trace_out, 'w') as f:
        json.dump(trace_data, f, indent=2)
    total = len(trace_data['records'])
    print(f"  Full export: {total} VMTraceRecords -> {trace_out}")

    # Reachable-only export: BFS from the known entry handler.
    if unicorn_records:
        entry_handler = unicorn_records[0]['handler_va']
    else:
        entry_handler = '0x140C5416E'  # first handler from DriverEntry trace

    # Build adjacency from merged_records (handler_va -> successor handler_vas)
    rec_adj = {}  # handler_va -> set of successor handler_va strings
    native_call_handlers = set()  # handlers that make native calls
    for rec in merged_records:
        h = rec['handler_va']
        for s in rec.get('successors', []):
            rec_adj.setdefault(h, set()).add(s)
        rec_adj.setdefault(h, set())  # ensure entry
        # Track native call targets as additional BFS edges.
        nt = rec.get('native_target_va', '0x0')
        if nt != '0x0':
            native_call_handlers.add(h)
            # The native target is also a reachable function.
            rec_adj.setdefault(h, set()).add(nt)
    # For native call handlers, add inner VM first handlers as successors.
    # At runtime, a native call may invoke a vmenter wrapper (recursive VM entry).
    # We add edges from every native-call handler to every inner VM first handler
    # as a conservative reachability approximation.
    inner_first_strs = set(f'0x{fh:X}' for fh in first_handler_to_whash if fh)
    for h in native_call_handlers:
        rec_adj.setdefault(h, set()).update(inner_first_strs)
    visited = set()
    queue = [entry_handler]
    while queue:
        h = queue.pop(0)
        if h in visited:
            continue
        visited.add(h)
        for succ in rec_adj.get(h, []):
            if succ not in visited:
                queue.append(succ)
    # Filter records to only reachable handlers
    reachable_records = [r for r in merged_records if r['handler_va'] in visited]
    reachable_out = Path(r'D:\binsnake\tracer\vm_trace_reachable.json')
    reachable_data = {
        'vmenter_va': f'0x{VM_ENTRY:X}',
        'vmexit_va': f'0x{VM_EXIT:X}',
        'records': reachable_records,
    }
    with open(reachable_out, 'w') as f:
        json.dump(reachable_data, f, indent=2)
    print(f"  Reachable from {entry_handler}: {len(visited)} handlers, {len(reachable_records)} records -> {reachable_out}")

if __name__ == '__main__':
    main()
