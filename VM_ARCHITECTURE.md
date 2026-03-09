# Hash-Dispatch VM Architecture

## 1. Overview

The binary implements a hash-dispatch virtual machine that virtualizes native x64 code into a
sequence of opaque handler operations. The VM uses a flat register-save frame, a hash-based
opcode system, merged multi-op handler bodies, and MBA-obfuscated dispatch logic to resist
static analysis.

**Key constants:**

| Name | Value | Purpose |
|-|-|-|
| base_delta | `0x140002F09` | Added to dispatch constants to compute thunk addresses |
| vm_enter | `sub_1402A1000` | Saves all registers, sets up VM context |
| vm_exit | `sub_1402A112B` | Restores all registers from VM context |
| vm_enter_v2 | `sub_1402A14FF` | Re-entry variant used after trampoline calls |
| Dispatch region | `0x1402A1000`-`0x14033D000` | Contains dispatch stubs and thunks (E9 jump tables) |
| Handler region | `0x14033D000`-`0x14270B000` | Contains handler bodies and inline stubs |

**Scale:**
- 8,266 dispatch stubs (= 8,266 unique VM opcodes)
- 4,178 unique handler bodies (ops merged 1-5 per body)
- 269 VM entry points across the binary


## 2. VM Context Frame

### 2.1 Frame Layout

VM entry (`sub_1402A1000`) creates a 0x1C0-byte frame by `lea rsp, [rsp-1C0h]` then saving
all registers. The context pointer `r12` is set to `rsp + 8` at the end of vm_enter, pointing
directly at the first saved register slot.

```
r12+0x00  xmm7      (16 bytes)
r12+0x10  xmm11     (16 bytes)
r12+0x20  xmm9      (16 bytes)
r12+0x30  rbp
r12+0x38  rdx        <-- arg2 at entry (e.g., RegistryPath)
r12+0x40  rbx
r12+0x48  xmm1      (16 bytes)
r12+0x58  xmm0      (16 bytes)
r12+0x68  xmm12     (16 bytes)
r12+0x78  r8
r12+0x80  r9
r12+0x88  r13
r12+0x90  rcx        <-- arg1 at entry (e.g., DriverObject)
r12+0x98  saved_r12  (pre-VM value of r12)
r12+0xA0  xmm14     (16 bytes)
r12+0xB0  RFLAGS     (saved via pushfq/pop)
r12+0xB8  ptr_R      (pointer to original rsp before lea, = &above-frame)
r12+0xC0  xmm3      (16 bytes)
r12+0xD0  xmm15     (16 bytes)
r12+0xE0  base_delta (0x140002F09, computed RIP-relative)
r12+0xF0  xmm5      (16 bytes)
r12+0x100 xmm2      (16 bytes)
r12+0x108 rax        (also used as a GP virtual register by handlers)
r12+0x110 r14
r12+0x118 xmm8      (16 bytes)
r12+0x128 rsi
r12+0x130 xmm10     (16 bytes)
r12+0x140 r15
r12+0x148 xmm6      (16 bytes)
r12+0x158 r10
r12+0x160 xmm4      (16 bytes)
r12+0x170 rdi
r12+0x178 xmm13     (16 bytes)
r12+0x188 r11        (last saved register, at offset 0x190 from rsp)
r12+0x190 hash       (opcode selector, set by dispatch stubs)
r12+0x198 scratch    (used by some handlers for state)
```

### 2.2 Special Slots

- **`[r12+0xE0]` (base_delta):** Computed by `sub_1402A110E` during vm_enter. It takes the
  return address of its call site and adds a fixed offset (`0xFFFFFFFFFD61E74` = -0x29E18C)
  to derive `0x140002F09`. All dispatch constants are relative to this base.

- **`[r12+0xB8]` (ptr_R):** A pointer to the stack position ABOVE the VM frame (original rsp
  before the `lea rsp,[rsp-1C0h]`). Handlers use this for indirect writes to the caller's
  stack frame, including setting the native function address for trampoline calls.

- **`[r12+0x190]` (hash):** The 64-bit opcode selector. Set by each dispatch stub before
  jumping to a handler. The handler uses this value (via MBA-obfuscated comparisons) to
  determine which merged operation to execute.


## 3. Dispatch Mechanism

### 3.1 Dispatch Stubs

Each VM operation begins with a dispatch stub that sets the opcode hash and jumps to the
handler body:

```asm
mov  rax, 0xA26346B5C9C0B6DB    ; 64-bit hash (opcode ID)
mov  [r12+190h], rax             ; store in VM context
mov  eax, 0x2C6386               ; 32-bit dispatch constant
add  rax, [r12+0E0h]            ; + base_delta = thunk address
jmp  rax                         ; jump to thunk -> E9 chain -> handler
```

The dispatch constant + base_delta yields a thunk address in the dispatch region
(`0x1402A1000`-`0x14033D000`). Thunks are packed E9 (jmp rel32) instructions that chain
to the actual handler body in the handler region.

### 3.2 Address Resolution

```
const  ──(+ base_delta)──>  thunk_addr  ──(E9 chain)──>  handler_addr
0x2C6386  + 0x140002F09   = 0x14032958F  ──> E9 ──> ... ──> 0x140C5416E
```

### 3.3 Hash-to-Handler Mapping

- Each hash maps to exactly ONE handler (1:1, confirmed across all 8,266 stubs)
- Each handler serves 1-5 hashes (merged operations):
  - 1,574 handlers: 1 op (not merged)
  - 1,453 handlers: 2 ops merged
  - 820 handlers: 3 ops merged
  - 329 handlers: 4 ops merged
  - 2 handlers: 5 ops merged (maximum observed)

### 3.4 Exit Patterns

Handlers exit via one of these patterns:

**Pattern A: Inline dispatch (most common)**
Hash set + const dispatch embedded directly in the handler body:
```asm
mov  rax, NEW_HASH_64
mov  [r12+190h], rax
mov  eax, CONST_32
add  rax, [r12+0E0h]
jmp  rax
```

**Pattern B: Micro-op dispatch**
Handler dispatches to the dispatch region, landing on a separate dispatch stub:
```asm
mov  eax, CONST_32              ; const resolves to dispatch region
add  rax, [r12+0E0h]
jmp  rax                        ; -> dispatch region -> E9 -> dispatch stub
```
The dispatch stub (which is a separate code block) then sets the hash and dispatches to
the next handler. This is a 2-step dispatch.

**Pattern C: VM exit call**
Handler dispatches to a trampoline that exits the VM, calls native code, and re-enters:
```asm
mov  eax, CONST_32              ; resolves to trampoline address
add  rax, [r12+0E0h]
jmp  rax                        ; -> trampoline code
```

**Pattern D: Computed dispatch (lea-based)**
Handler loads base_delta, computes multiple target addresses, and conditionally selects:
```asm
mov  rax, [r12+0E0h]            ; base_delta
lea  r9, [rax+CONST_A]          ; candidate target A
lea  r10, [rax+CONST_B]         ; candidate target B
add  rax, CONST_C               ; candidate target C
; ... conditional selection via cmov ...
jmp  rax
```
This pattern is used by merged handlers that share exit logic across multiple operations.


## 4. Handler Merging & Demerging

### 4.1 The Merging Model

Handlers are multi-op blocks. A single handler body serves N different operations (one per
unique incoming hash). The handler's internal logic uses the hash at `[r12+190h]` to select
which operation to perform.

The selection logic uses **Mixed Boolean Arithmetic (MBA)** to obfuscate what is essentially
a switch-case on the hash value. Typical pattern:

```asm
mov  rbx, [r12+190h]            ; load opcode hash
mov  rax, 0x4C9488C3381AC494    ; obfuscated comparison constant
cmp  rbx, rax
setb cl                         ; flag = (hash < constant)
; ... many more MBA comparisons ...
; ... xor, imul, shr, or chains ...
; ... eventually selects one exit path
```

The result is that for each unique hash, the handler follows a deterministic single path
through the conditional maze, producing exactly one exit (hash, const) pair.

### 4.2 The Flat Execution Model

For any given execution trace (e.g., DriverEntry), the VM executes as a **flat linear
sequence** of operations:

```
stub_0(hash_0) -> handler_A -> stub_1(hash_1) -> handler_B -> ... -> vm_exit -> native -> reenter -> ...
```

There are NO real conditionals in a single trace. Every branch is predetermined by the
hash chain. What appear as conditional branches (cmov, cmp+jcc) are actually the merged
operation selection logic, which resolves to a single path for each specific hash.

### 4.3 Demerging Strategy

**Goal:** Split each merged handler into N single-op clones (one per hash it serves),
producing 8,266 flat, unconditional operation blocks.

**Approach 1: Hash-keyed symbolic execution**
1. For each (handler, hash) pair in the stub database:
   a. Set `[r12+190h]` = hash
   b. Symbolically execute the handler body
   c. Track which branches are taken (all resolve deterministically on hash)
   d. Record the single exit path: output (hash_out, const_out)
   e. Record the data-flow operations performed on VM registers
2. Output: a clone of the handler containing only the taken path

**Approach 2: Pattern matching on dispatch stubs**
1. Scan each handler for ALL embedded dispatch stubs (hash-set + const-dispatch patterns)
2. Each stub corresponds to one exit for one merged operation
3. Map stubs to operations by:
   a. Scanning backward from each dispatch for the `mov [r12+190h], hash` store
   b. Each (hash_out, const_out) pair is one operation's exit
   c. Match against the stub DB to determine which incoming hash selects each exit

**Approach 3: Trace-based demerging**
1. Instrument the VM at the dispatch stub level
2. Log (incoming_hash, handler_addr, outgoing_hash, outgoing_const) for each step
3. Build the flat chain for each entry point
4. Clone handlers per observed (handler, incoming_hash) pair

### 4.4 Challenges

- **MBA obfuscation:** The hash comparison logic uses extensive Mixed Boolean Arithmetic,
  making it hard to symbolically determine which path corresponds to which hash without
  executing the comparisons.

- **Handler size variance:** Handlers range from ~50 to 10,000+ instructions. The hash
  store can be 4,000+ bytes before the dispatch constant, requiring wide-range scanning.

- **Merged exit logic:** Some handlers use Pattern D (lea-based computed dispatch) where
  the exit targets are computed via conditional cmov chains rather than explicit branches.
  These require tracking data flow through the exit selection logic.

- **Cross-handler state:** Some operations span multiple handlers (one sets up state that
  the next consumes). Demerging individual handlers is insufficient; the full operation
  context requires tracing the hash chain.


## 5. Trampoline Mechanism (VM Exit/Re-enter)

### 5.1 Trampoline Structure

When the VM needs to call native (non-virtualized) code, it uses a trampoline pattern:

```asm
; ---- VM EXIT ----
call  sub_1402A112B              ; vm_exit: restore all GPRs, XMMs, RFLAGS
lea   rsp, [rsp+1C0h]           ; pop VM frame (rsp = original pre-VM rsp)
; ---- NATIVE CALL ----
call  [rsp+8]                    ; call native function (address at [R+8])
; ---- VM RE-ENTER ----
lea   rsp, [rsp-1C0h]           ; push VM frame back
mov   qword ptr [rsp+190h], 0   ; clear hash state
call  sub_1402A14FF              ; vm_enter_v2: re-save all registers
jmp   REENTRY_HANDLER            ; continue VM execution
```

### 5.2 Native Function Address

The native function pointer is at `[R+8]` (8 bytes above the original stack pointer before
VM entry). This slot is set by VM handlers through the `[r12+0xB8]` pointer indirection:

1. `[r12+0xB8]` = pointer to R (original rsp position)
2. A handler loads this pointer and stores a function address at `[ptr+8]`
3. The trampoline calls `[rsp+8]` after popping the VM frame, which equals `[R+8]`

**For a given hash chain (flat trace), the native function is static** -- it is deterministically
computed by the handlers and always resolves to the same function for the same entry path.

### 5.3 Re-entry Handler

After the native call, the trampoline re-enters the VM and jumps to a re-entry handler.
This handler reads `[r12+190h]` (which was cleared to 0 by the trampoline) and other
state to dispatch to the next post-native handler.

Re-entry handlers typically use Pattern D (computed dispatch with conditional selection
based on pre-exit state stored at `[r12+190h]` or `[r12+198h]`).

### 5.4 Exit Types

Two types of VM exits exist:

| Type | Count | Pattern after vm_exit |
|-|-|-|
| TRAMPOLINE | ~9,317 | `lea rsp+1C0; call [rsp+8]; lea rsp-1C0; call vm_enter; jmp handler` |
| TERMINAL | ~838 | `lea rsp+1C0; retn` (returns to caller, VM execution ends) |


## 6. Tracing Correct Paths (Hash Chain Following)

### 6.1 The Problem

The merged CFG shows each handler with multiple exits (one per merged op). This creates
a graph of 7,000+ nodes and 23,000+ edges. But for any specific entry point, only ONE
path through this graph is actually taken -- determined by the hash chain.

### 6.2 Algorithm: Flat Trace via Hash Chain

```
Input: entry_hash, entry_handler (from the vmenter wrapper's dispatch stub)
Output: linear sequence of (handler, hash, operation_semantics)

1. current_hash = entry_hash
2. current_handler = entry_handler
3. REPEAT:
   a. Find the exit stub within current_handler that corresponds to current_hash
      - Scan handler body for dispatch patterns (hash-set + const-dispatch)
      - Match the hash store to the incoming hash via MBA analysis or brute-force
   b. Extract (next_hash, next_const) from the matched exit stub
   c. Resolve next_const to next_handler via base_delta + thunk following
   d. If exit is vm_exit_call: record trampoline, follow re-entry
   e. If exit is terminal: STOP
   f. current_hash = next_hash; current_handler = next_handler
4. UNTIL terminal or loop detected
```

### 6.3 Practical Implementation

For a static tracer, the main challenge is step 3a: determining which exit stub fires for
a given incoming hash. Two practical approaches:

**Approach A: Proximity heuristic (used in current implementation)**
- For each handler edge in the CFG, find the `mov [r12+190h]` store closest before the
  dispatch constant in the handler body
- Assume the closest hash store is the one associated with that dispatch
- This works for most handlers but can fail when hash stores are very far from dispatches
  or when the handler has complex conditional exit selection

**Approach B: Stub DB cross-reference**
- Each handler serves N hashes (from the dispatch stub DB)
- Each handler has N exit stubs (one per merged op)
- If we can extract ALL N exit stubs from a handler, we can match them 1:1 with the N
  incoming hashes
- Cross-reference: the outgoing hash of exit stub K should appear as an incoming hash
  in the stub DB, mapping to the next handler

### 6.4 DriverEntry Flat Trace (Example)

```
Step  Handler         Hash (incoming)       Exit Type
 0    0x140C5416E     0xA26346B5C9C0B6DB   micro_op -> dispatch stub
 1    0x141448082     0xE5D3BDF5888D2147   inline dispatch
 2    0x1420ADE76     0x0FFF6210CFE9DB43   inline dispatch
 3    0x1419F5E87     0xC1D9205D085C44FB   micro_op -> dispatch stub
 4    0x140C92272     0x6031A279E6E3C0E1   inline dispatch
 5    0x1415972E7     0x066A33160AFA2FD6   inline dispatch
 6    0x141B95F4B     0xAAACECAB22B163DEC  inline dispatch
 7    0x141BD98F4     0xA9E93C81D73660D8   inline dispatch
 8    0x14145F69D     0x66BD18E4731801ED   inline dispatch
 9    0x14184F0CE     0x1A32783C49B4FE95   VM EXIT -> native call -> re-enter
10    0x1404ED80B     0x4A74CA0F........   post-trampoline continuation
```

10 flat handler steps from DriverEntry to the first native function call, then continuation
after re-entry. The native function called is static for this specific hash chain.


## 7. Patterns Reference

### 7.1 Byte Patterns for Scanning

| Pattern | Bytes | Purpose |
|-|-|-|
| add rax, [r12+E0h] | `49 03 84 24 E0 00 00 00` | Dispatch: add base_delta to const |
| add rcx, [r12+E0h] | `49 03 8C 24 E0 00 00 00` | Dispatch variant (rcx) |
| add rdx, [r12+E0h] | `49 03 94 24 E0 00 00 00` | Dispatch variant (rdx) |
| mov rax, [r12+E0h] | `49 8B 84 24 E0 00 00 00` | Load base_delta |
| mov [r12+190h], rax | `49 89 84 24 90 01 00 00` | Store hash (opcode selector) |
| mov rax, imm64 | `48 B8 xx xx xx xx xx xx xx xx` | Load 64-bit hash value |
| mov eax, imm32 | `B8 xx xx xx xx` | Load dispatch constant |
| jmp rax | `FF E0` | Dispatch jump |
| E9 rel32 | `E9 xx xx xx xx` | Thunk jump (packed jump tables) |
| call vm_exit | `E8` + offset to `0x1402A112B` | VM exit call |

### 7.2 Dispatch Stub Identification

A dispatch stub is identified by the sequence:
```
48 B8 [8 bytes]                  -- mov rax, HASH_64
49 89 84 24 90 01 00 00          -- mov [r12+190h], rax
B8 [4 bytes]                     -- mov eax, CONST_32
49 03 84 24 E0 00 00 00          -- add rax, [r12+E0h]
FF E0                            -- jmp rax
```
Total: 31 bytes per dispatch stub.

### 7.3 Trampoline Identification

A trampoline is identified by:
```
E8 [4 bytes]                     -- call vm_exit (target = 0x1402A112B)
48 8D A4 24 C0 01 00 00          -- lea rsp, [rsp+1C0h]
FF 54 24 08                      -- call [rsp+8]
48 8D A4 24 40 FE FF FF          -- lea rsp, [rsp-1C0h]
```


## 8. File Inventory

| File | Description |
|-|-|-|
| dispatch_stubs.json | 8,266 dispatch stubs: (stub_addr, hash, const, target, thunk_target) |
| vm_cfg_true.json | Merged CFG: 4,453 sources, 23,081 edges across all edge types |
| vm_cfg_graph.json | Full graph export with nodes/edges/stubs for external tools |
| vm_cfg_adj.json | Compact adjacency list (handler + handler_internal edges only) |
| driver_entry_chain.json | BFS subgraph from DriverEntry: 9,280 nodes, 51,601 edges |
| vm_cfg_viewer.html | Interactive Canvas/JS visualizer with force-directed layout |
| _graph_data.json | Preprocessed compact graph data for the viewer |


## 9. Next Steps

### 9.1 Immediate: Complete Flat Trace
- Extend the hash-chain tracer to handle all exit patterns (Pattern D lea-based, etc.)
- Trace DriverEntry to completion (through all trampolines to terminal exit)
- Identify the static native function(s) called at each trampoline

### 9.2 Short-term: Automated Demerging
- Build a demerger that:
  1. Scans each handler for all exit stubs (extract all hash_out + const pairs)
  2. Maps each exit stub to its corresponding incoming hash
  3. Produces N cloned handler blocks per handler (one per hash)
  4. Each clone contains only the path taken for its specific hash
- Output: 8,266 flat operation blocks, each unconditional

### 9.3 Medium-term: Semantic Recovery
- Classify demerged operations by their data-flow on VM registers
- Map VM register reads/writes to native register semantics
- Identify common operation types: mov, add, cmp, call, etc.
- Reconstruct the original control flow graph from the flat traces

### 9.4 Long-term: Full Decompilation
- Lift demerged VM operations to an intermediate representation
- Apply standard compiler optimizations (constant propagation, dead code elimination)
- Reconstruct native x64 code from the lifted IR
- Verify correctness against the original VM execution
