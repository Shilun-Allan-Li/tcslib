# 12.2c T1 — batch 11A delivery

## Result and base

**Tasks 1–4 implemented and kernel-checked. The strict duplication gate remains open on escalation E1:** Task 1’s mandated verbatim promotion produces two new file/name pairs with Catalog, outside the brief’s Loop-only carry-over exception. This archive is a complete, reviewable refactor, not a claim that that contradictory gate is satisfied. No new mathematics or statement weakening. Only the two owned Lean files are changed. No push, PR, rebase, or repository-wide build was performed. The cache command’s internal ProofWidgets build hook failed; the dependency setup exception is recorded under verification below.

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`. Starting branch: `complexity/arora-barak-ch3-4`.
- Base: `baee8819838137522ea43e59deb9fea446bbf3dc`.
- Required ancestor: `9270021ab6499f02b0912bc614fd142761e7339f`; `git merge-base --is-ancestor` exited 0.
- Fresh branch: `refactor/12.2c-t1-loop`; delivery head: `ccaee4b548b50ed93737e81f4a9b53947ea3f77e`.
- Binding brief, plan §4d items 6/11 and §4e, ledger rows, RB4 report, RB5’s withdrawn-task account, and policy were read.

| File | Lines before → after | Private before → after | Public before → after |
| --- | ---: | ---: | ---: |
| Build/Loop.lean | 5,472 → 4,980 (−492) | 190 → 185 (−5) | 8 → 8 |
| Finite.lean | 276 → 331 (+55) | 0 → 0 | 14 → 17 |

## Task accounting

1. **Run facts.** Inserted the brief’s three public declarations and proofs verbatim after `spaceUsed_le_mul_succ`, without attributes, and added the requested Main results bullet. `runFrom_output_prepend` uses `runFrom_comm_of_step`.
2. **Copies, rider, and alias.** Deleted the three private run-fact copies, both private input-displacement lemmas, and the `emCall_state_run` notation. Consumers cite the public facts; `emCall_bank_step` changes only that transport token. Its statement and docstring are unchanged.
3. **Shared host.** Moved the controller table and its docstring into `loopHostM`; the table differs only in the prescribed body branch. Capture and forwarding hosts are abbreviations. The administrative phases are generalized in place, the body run has one proof split on the mode, and anchor return/startup are shared. Removed the forwarding prepare/anchor/start family and round’s inlined reject/borrow proofs. Capture-only statements remain unchanged.
4. **Scans and glue.** One `loop_scan_left` induction serves the payload scan and the counter rewinds. `loopHost_payload_scan` replaces both phase-1/2 and phase-12/13 payload rewinds. `loopCall_frame` is the prescribed symmetric instance of `loopCall_reframe`; it moves immediately after that lemma so it can cite it.

## Declaration inventory and statement freeze

**Added in Finite:** `step_output_prepend`, `runFrom_output_prepend`, `runFrom_state_ne_none_of_le` in `Turing.MultiTapeTM`.

**Added in Loop:** `loopBodyDispatch`, `loopBodyImage`, `loopBodyImage_nil`, `loopHostM`, `loopHost_body_run`, `loopHost_payload_scan`, `loop_scan_left`.

**Deleted from Loop (docstring and declaration):** `emLoopHost_agree`, `emLoopHost_anchor_return`, `emLoopHost_prepare`, `emLoopHost_start`, `emLoop_run_prefix`, `emLoop_step_prefix`, `loopHost_body_capture`, `loopHost_fuel_rewind`, `loopHost_payload_rewind`, `loop_input_move_le`, `loop_input_run_le`, `loop_live_prefix`. The associated notation and its comment are also deleted.

**Moved byte-identically:** `emLoopForwardCfg`, `emLoopCall`, `emLoopCall_frame`, `emLoopCall_empty` move after `loopCall`. `loopHost`’s table/docstring moves to `loopHostM` with the name, mode binder, and body branch substitutions only. `loopCall_frame` moves after `loopCall_reframe`, with its prescribed proof replacement.

**`def` → `abbrev`:** `loopHost` and `emLoopHost`, respectively selecting `false` and `true` body modes. No phase wrappers remain.

Every existing public statement is byte-identical. Seven Loop public blocks are entirely byte-identical. The eighth, `exists_emitLoopTM`, has exactly these sanctioned substitutions (no `simp only [E]` was needed):

```lean
emLoopHost_prepare body F anchor true R T hF x
-- becomes
loopHost_prepare body F anchor true true R T hF x

emLoopHost_start body F anchor true (s0 x) btime fuel hbguard hbend
-- becomes
loopHost_start body F anchor true true (s0 x) btime fuel hbguard hbend
```

Its docstring changes only `` `emLoop_run_prefix` `` to `` `Turing.MultiTapeTM.runFrom_output_prepend` ``. All previously existing Finite declaration blocks are unchanged. Both files’ imports are unchanged. The historical `loopHost_contracts` docstring is unchanged.

Exact before/after statements for every changed surviving private appear in the appendix and `verification/loop-surface.json`; deleted/renamed declarations are separately enumerated above. `verification/static-checks.log` records the byte comparisons.

## Duplication governance

The two unmodified repository scripts were run before and after. The baseline reproduces the brief’s 596 screened declarations, 673 pairs and 280,141 reproduced characters. The immutable base checkout supplies the baseline census.

| Screen scope | Pairs before → after | Reproduced characters before → after |
| --- | ---: | ---: |
| All five files | 673 → 540 | 280,141 → 223,798 |
| Loop.lean → Loop.lean | 110 → 65 | 56,666 → 33,502 |
| Loop.lean → Catalog.lean | 115 → 87 | 59,686 → 41,451 |
| Catalog.lean → Loop.lean | 161 → 100 | 63,588 → 48,556 |

### Removed-pair checklist

- The `emLoopHost_*` → `loopHost_*` copy pairs are gone, including round versus reject/borrow/fuel-return and round versus the removed forwarding start.
- All 18 in-file pairs involving `emLoop_run_prefix` are gone.
- The two payload/fuel-rewind directions are gone; their declarations are replaced by one scan.
- `loopCall_reframe` → `loopCall_frame` is gone.

### E1 — the verbatim promotion and the cross-file rule conflict

The required proof of `Finite.runFrom_state_ne_none_of_le` contains exactly the same 156 normalized body characters as `Catalog.f2_loop_live_prefix`. At baseline those 156 characters were Loop’s `loop_live_prefix`, paired with Catalog in both directions at 100%. Task 1 moves that proof to Finite, Task 2 deletes Loop’s copy, and Catalog is explicitly outside ownership. The final screen therefore necessarily reports:

- `Finite.runFrom_state_ne_none_of_le` → `Catalog.f2_loop_live_prefix`: 156/156 = 100%.
- `Catalog.f2_loop_live_prefix` → `Finite.runFrom_state_ne_none_of_le`: 156/170 = 92%. The extra 14 normalized characters are the namespace-closing text counted by the existing screen.

This relocates acknowledged duplication; it adds no duplicate proof body to the tree. Nevertheless, the brief’s exception explicitly requires a **Loop** side, so these two pairs do not qualify. The instruction to insert Task 1 verbatim and leave Catalog untouched prevents a source-only resolution within the brief. The required disclosure does not itself waive the no-new-cross-file-pair rule.

**Proposed fix to the brief:** explicitly allow the promotion carry-over `Finite.runFrom_state_ne_none_of_le` ← deleted `Loop.loop_live_prefix`, with the same partner and nonincreasing share. Both directions qualify under that amended rule. An alternative is to authorize replacing Catalog’s copy by a citation in its owning tranche. No such exception or out-of-scope edit is silently assumed here.

The first scan proof also produced new short-induction matches. Its final proof uses `Nat.rec`, the one-step run equation, and `congrArg` in an explicit equality chain. This keeps the prescribed induction and statement, with no copied phase proof or extra wrapper. Only final measurements below are used for the gate.

### Every new pair

| Target | Source | Share after | Classification / baseline carry-over |
| --- | --- | ---: | --- |
| `Finite.lean::runFrom_state_ne_none_of_le` | `Catalog.lean::f2_loop_live_prefix` | 156/156 (100%) | E1: mandated public promotion; pre-existing Loop–Catalog pair moved to Finite, outside the literal exception. |
| `Catalog.lean::f2_loopHost` | `Loop.lean::loopHostM` | 2368/2417 (98%) | Carry-over: `Catalog.lean::f2_loopHost` → `Loop.lean::loopHost`, 2477/2477 |
| `Loop.lean::loopHostM` | `Catalog.lean::f2_loopHost` | 2368/2495 (95%) | Carry-over: `Loop.lean::loopHost` → `Catalog.lean::f2_loopHost`, 2477/2495 |
| `Catalog.lean::f2_loop_live_prefix` | `Finite.lean::runFrom_state_ne_none_of_le` | 156/170 (92%) | E1: mandated public promotion; pre-existing Loop–Catalog pair moved to Finite, outside the literal exception. |
| `Loop.lean::loopBodyImage` | `Loop.lean::emLoopCall` | 87/134 (65%) | The required shared image contains the existing forwarding-call expression; the existing call helper is moved unchanged as prescribed. Configuration adapter, not a duplicated proof. |
| `Loop.lean::loopBodyDispatch` | `Loop.lean::loopBodyImage` | 118/190 (62%) | Action and configuration branches use the same prescribed state/return mapping; they have different result types and roles. |
| `Loop.lean::loopHost_fuel_return` | `Loop.lean::loopHost_payload_scan` | 422/688 (61%) | Carry-over: `Loop.lean::loopHost_fuel_return` → `Loop.lean::loopHost_fuel_rewind`, 1047/1261; `Loop.lean::loopHost_fuel_return` → `Loop.lean::loopHost_payload_rewind`, 1047/1269 |
| `Loop.lean::loopHost_body_run` | `Catalog.lean::f2_loopHost_body_capture` | 64/117 (55%) | Carry-over: `Loop.lean::loopHost_body_capture` → `Catalog.lean::f2_loopHost_body_capture`, 92/117 |
| `Loop.lean::loopHost_borrow_rewind` | `Loop.lean::loopHost_payload_scan` | 359/688 (52%) | Carry-over: `Loop.lean::loopHost_borrow_rewind` → `Loop.lean::loopHost_fuel_rewind`, 733/1261; `Loop.lean::loopHost_borrow_rewind` → `Loop.lean::loopHost_payload_rewind`, 733/1269 |

### Required special-name disclosure

The new-pair table includes both directions for all pairs touching `loop_scan_left`, `loopBodyDispatch`, `loopHostM`, `loopBodyImage`, `loopBodyImage_nil`, `loopHost_body_run`, or `loopHost_payload_scan`. Names with no new pairs are recorded below.

- `loop_scan_left`: 0 new directed pair(s).
- `loopBodyDispatch`: 1 new directed pair(s).
- `loopHostM`: 2 new directed pair(s).
- `loopBodyImage`: 2 new directed pair(s).
- `loopBodyImage_nil`: 0 new directed pair(s).
- `loopHost_body_run`: 1 new directed pair(s).
- `loopHost_payload_scan`: 2 new directed pair(s).

**Task 1:** the two E1 pairs touch `runFrom_state_ne_none_of_le`; the other two new public facts have no pairs.

**`loopHost_fuel_copy` disposition:** retained and generalized only by body mode; its copying mathematics and induction are unchanged. All before/after pair measurements follow.

| Direction | Before | After |
| --- | ---: | ---: |
| `Catalog.lean::f2_loopHost_fuel_copy` → `Loop.lean::loopHost_fuel_copy` | 1356/1458 (93%) | 1319/1466 (90%) |
| `Loop.lean::loopHost_fuel_copy` → `Catalog.lean::f2_loopHost_fuel_copy` | 1356/1527 (89%) | 1319/1527 (86%) |
| `Loop.lean::loopHost_fuel_copy` → `Loop.lean::emLoop_run_prefix` | 65/129 (50%) | removed / absent |
| `Loop.lean::loopHost_fuel_copy` → `Loop.lean::loopHost_fuel_rewind` | 827/1261 (66%) | removed / absent |
| `Loop.lean::loopHost_fuel_copy` → `Loop.lean::loopHost_payload_rewind` | 829/1269 (65%) | removed / absent |
| `Loop.lean::loopHost_fuel_rewind` → `Loop.lean::loopHost_fuel_copy` | 827/1458 (57%) | removed / absent |
| `Loop.lean::loopHost_payload_rewind` → `Loop.lean::loopHost_fuel_copy` | 829/1458 (57%) | removed / absent |

### Census

**Before:**

```text
   Loop                98/198 =  49.5%   historical 88 + from pairs 10
   Catalog            318/428 =  74.3%
```

**After:**

```text
   Loop                92/193 =  47.7%   historical 81 + from pairs 11
   Catalog            312/428 =  72.9%
```

The two E1 promotion pairs are disclosed, not classified as permitted carry-overs. Every other new cross-file pair has a qualifying carry-over. Loop’s pass-4 source membership is at most 98. Catalog itself is unchanged; its generated membership falls because Loop’s source population changes. The complete before/after screens, censuses, and machine-readable directed-pair comparison are included.

## Verification

- Lean 4.25.0, commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`; mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.
- Bootstrap: **120/120** modules, in the exact order of `briefs/orders/ch34-t1-loop.txt`, on the recorded immutable base.
- Final: **104/104** checks: Finite, Loop, then every subsequent module of the same list. All exit statuses are zero, no error diagnostics, fresh nonempty `.olean` files. Finite and Loop have zero sorry warnings; every replayed module has exactly its baseline sorry-warning count.
- Bootstrap sorry warnings: 84. Final replay sorry warnings: 84; all are inherited and unchanged.
- The only Lean source-checking command was `bash scripts/lean_check_tree.sh <module>`, including the temporary axiom probes. No checker script was edited.
- Dependency setup: the first `lake exe cache get` could not detect the installation. A local `readlink` shim redirects only this process’s `/proc/<pid>/exe` lookup to `/proc/self/exe`; it leaves Lean and its libraries unchanged. Retrying the required cache command built its cache utility but its internal ProofWidgets cloud-release hook failed. `lake exe cache unpack` then successfully unpacked 3,232 existing hash-keyed cache files. Pins and repository sources were unchanged. Logs and the shim source are included.
- Existing ordinary unused-argument and oversized-file warnings remain. Task 1 is verbatim despite the two unused-simp-argument warnings. No warning category or checker was disabled. The brief fixes these large files’ scope; no size split was attempted.

Final sweep tail:

```text
PASS {"module": "TCSlib/Complexity/TuringMachine/Robustness/Bidirectional", "exit": 0, "errors": 0, "sorry_warnings": 0, "seconds": 2.57, "olean_bytes": 1192576}
PASS {"module": "TCSlib/Complexity/TuringMachine", "exit": 0, "errors": 0, "sorry_warnings": 0, "seconds": 1.48, "olean_bytes": 45400}
PASS {"module": "TCSlib/Complexity/TuringMachine/Build/CounterLoop", "exit": 0, "errors": 0, "sorry_warnings": 0, "seconds": 4.37, "olean_bytes": 2247488}
PASS {"module": "TCSlib/Complexity/TuringMachine/Build/VirtualInput", "exit": 0, "errors": 0, "sorry_warnings": 0, "seconds": 1.6, "olean_bytes": 584504}
PASS {"module": "TCSlib/Complexity/TuringMachine/Build/Zone", "exit": 0, "errors": 0, "sorry_warnings": 2, "seconds": 5.15, "olean_bytes": 2575408}
PASS {"module": "TCSlib/Complexity/TuringMachine/Codes2Tape", "exit": 0, "errors": 0, "sorry_warnings": 1, "seconds": 3.6, "olean_bytes": 2300872}
COMPLETE 104/104
```

All eleven axiom prints (the first eight are byte-identical to the base):

```text
'Turing.stateWord' does not depend on any axioms
'Turing.loop_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.exists_loopCfgTM' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.exists_loopTM' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.exists_loopFindTM' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.exists_emitLoopTM' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.exists_installCallTM' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.exists_emitCallTM' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.MultiTapeTM.step_output_prepend' depends on axioms: [propext, Quot.sound]
'Turing.MultiTapeTM.runFrom_output_prepend' depends on axioms: [propext, Quot.sound]
'Turing.MultiTapeTM.runFrom_state_ne_none_of_le' depends on axioms: [propext, Quot.sound]
```

Directory lint summaries:

```text
style_lint: 0 FAIL, 14 WARN over 46 files
style_lint: 0 FAIL, 6 WARN over 12 files
```

## Out of scope, preserved

- 11B: `emCall*`’s remaining layout/frame duplication; `loop_run` / `loop_halted_run` / `loop_find_run`; the `exists_*` proof parallels.
- T2 and item 6: EmitIterEmbed’s five run facts become citations later; `loopBodyTM` / `loopBodyCfg` versus `padAction` / `embedCfg` remain assigned there.
- Later Task-1 citations: Catalog `f2_loop_live_prefix`; Hardness `clA5_live_prefix`; SAT `sat_live_prefix`; Catalog `f2_loop_input_*` and the `f2_loopHost*` twins (item 1).
- Item 12: fuel-debit re-derivation waits for T3’s layout; importing CounterLoop into Loop would cycle through Catalog.
- G1’s `Simulation`, `Embed`, `Seam`, and `Catalog` were not changed. The maintainer’s full 205-module Finite closure is not claimed here.

## Package and replay

- `REPORT.md`; both full sources under their original `TCSlib/...` paths.
- `patches/`: the ordered `git format-patch` series.
- `12.2c-t1-loop.bundle`: incremental bundle requiring the recorded base.
- `sweep.log`, `axioms.log`, and `verification/`: baseline/final logs, both screen and census outputs, exact changed-private statements, freeze checks, lint, source hashes, and patch/bundle replay evidence.
- `SHA256SUMS`: every archive member except itself.
- Applying the patch series from the base reproduces the committed tree; both full source files match that tree. `verification/patch-replay.log` and `verification/bundle-verify.log` record the checks.

## Appendix: every changed surviving private statement

These are literal before/after source headers, including declaration kind. They introduce the prescribed mode/prefix parameters or replace the two host definitions by abbreviations; no statement is weakened.

### `emLoopHost`

**Before**

```lean
private def emLoopHost (body F : FinTM Bool) (anchor : body.State) (findMode : Bool) :
    FinTM Bool
```

**After**

```lean
private abbrev emLoopHost (body F : FinTM Bool) (anchor : body.State) (findMode : Bool) :
    FinTM Bool
```

### `loopHost`

**Before**

```lean
private def loopHost (body F : FinTM Bool) (anchor : body.State) (findMode : Bool) :
    FinTM Bool
```

**After**

```lean
private abbrev loopHost (body F : FinTM Bool) (anchor : body.State) (findMode : Bool) :
    FinTM Bool
```

### `loopHost_anchor_return`

**Before**

```lean
private lemma loopHost_anchor_return (body F : FinTM Bool) (anchor : body.State)
    (findMode startup : Bool) {x : List Bool}
    (c : Cfg body.k Bool body.State x) (release : Bool) (t : ℕ)
    (word : List Bool) (fuel : Cfg F.k Bool F.State x)
    (hend : (body.tm.runFrom c t).state = some anchor)
    (hreleased : t = 0 → release = false)
    (hanchor : ∀ u < t, (u = 0 ∧ release = true) ∨
      (body.tm.runFrom c u).state ≠ some anchor) :
    (loopHost body F anchor findMode).tm.runFrom
        (loopCall body F anchor startup c release none word fuel) (t + 1) =
      loopCall body F anchor startup {body.tm.runFrom c t with state := none}
        false (some false) word fuel
```

**After**

```lean
private lemma loopHost_anchor_return (body F : FinTM Bool) (anchor : body.State)
    (forward findMode startup : Bool) (pre : List Bool) {x : List Bool}
    (c : Cfg body.k Bool body.State x) (release : Bool) (t : ℕ)
    (word : List Bool) (fuel : Cfg F.k Bool F.State x)
    (hend : (body.tm.runFrom c t).state = some anchor)
    (hreleased : t = 0 → release = false)
    (hanchor : ∀ u < t, (u = 0 ∧ release = true) ∨
      (body.tm.runFrom c u).state ≠ some anchor) :
    (loopHostM body F anchor forward findMode).tm.runFrom
        (loopBodyImage body F forward startup pre
          (loopBodyPadded body F anchor c release none word fuel)) (t + 1) =
      loopBodyImage body F forward startup pre
        (loopBodyPadded body F anchor {body.tm.runFrom c t with state := none}
          false (some false) word fuel)
```

### `loopHost_borrow`

**Before**

```lean
private lemma loopHost_borrow (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (p : Fin (x.length + 2)) (word : List Bool) :
    2 * loopBorrowPos word + 2 ≤ 2 * word.length + 2 ∧
    (loopHost body F anchor findMode).tm.runFrom
        (loopFrame body F base (some (.inr (.inr 8))) p (bufferTape [])
          (bufferTape word) (bufferTape []) 0 0 []) (2 * loopBorrowPos word + 2) =
      loopFrame body F base
        (some (if (loopDebit word).2 then .inr (.inl (false, (anchor, true)))
          else .inr (.inr 11))) p
        (bufferTape []) (bufferTape (loopDebit word).1) (bufferTape []) 0 0 []
```

**After**

```lean
private lemma loopHost_borrow (body F : FinTM Bool) (anchor : body.State) (forward : Bool)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (p : Fin (x.length + 2)) (word : List Bool) :
    2 * loopBorrowPos word + 2 ≤ 2 * word.length + 2 ∧
    (loopHostM body F anchor forward findMode).tm.runFrom
        (loopFrame body F base (some (.inr (.inr 8))) p (bufferTape [])
          (bufferTape word) (bufferTape []) 0 0 []) (2 * loopBorrowPos word + 2) =
      loopFrame body F base
        (some (if (loopDebit word).2 then .inr (.inl (false, (anchor, true)))
          else .inr (.inr 11))) p
        (bufferTape []) (bufferTape (loopDebit word).1) (bufferTape []) 0 0 []
```

### `loopHost_borrow_rewind`

**Before**

```lean
private lemma loopHost_borrow_rewind (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (p : Fin (x.length + 2)) (word : List Bool) (success : Bool) :
    ∀ j, j ≤ word.length →
    (loopHost body F anchor findMode).tm.runFrom
        (loopFrame body F base (some (.inr (.inr (if success then 9 else 10)))) p
          (bufferTape []) (bufferTape word) (bufferTape []) ((j : ℤ) - 1) 0 []) (j + 1) =
      loopFrame body F base
        (some (if success then .inr (.inl (false, (anchor, true))) else .inr (.inr 11))) p
        (bufferTape []) (bufferTape word) (bufferTape []) 0 0 []
```

**After**

```lean
private lemma loopHost_borrow_rewind (body F : FinTM Bool) (anchor : body.State) (forward : Bool)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (p : Fin (x.length + 2)) (word : List Bool) (success : Bool) :
    ∀ j, j ≤ word.length →
    (loopHostM body F anchor forward findMode).tm.runFrom
        (loopFrame body F base (some (.inr (.inr (if success then 9 else 10)))) p
          (bufferTape []) (bufferTape word) (bufferTape []) ((j : ℤ) - 1) 0 []) (j + 1) =
      loopFrame body F base
        (some (if success then .inr (.inl (false, (anchor, true))) else .inr (.inr 11))) p
        (bufferTape []) (bufferTape word) (bufferTape []) 0 0 []
```

### `loopHost_borrow_run`

**Before**

```lean
private lemma loopHost_borrow_run (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (p : Fin (x.length + 2)) (word : List Bool) : ∀ pre,
    (loopHost body F anchor findMode).tm.runFrom
        (loopFrame body F base (some (.inr (.inr 8))) p (bufferTape [])
          (bufferTape (pre ++ word)) (bufferTape []) pre.length 0 [])
        (loopBorrowPos word + 1) =
      loopFrame body F base (some (.inr (.inr (if (loopDebit word).2 then 9 else 10)))) p
        (bufferTape []) (bufferTape (pre ++ (loopDebit word).1)) (bufferTape [])
        ((pre.length : ℤ) + loopBorrowPos word - 1) 0 []
```

**After**

```lean
private lemma loopHost_borrow_run (body F : FinTM Bool) (anchor : body.State) (forward : Bool)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (p : Fin (x.length + 2)) (word : List Bool) : ∀ pre,
    (loopHostM body F anchor forward findMode).tm.runFrom
        (loopFrame body F base (some (.inr (.inr 8))) p (bufferTape [])
          (bufferTape (pre ++ word)) (bufferTape []) pre.length 0 [])
        (loopBorrowPos word + 1) =
      loopFrame body F base (some (.inr (.inr (if (loopDebit word).2 then 9 else 10)))) p
        (bufferTape []) (bufferTape (pre ++ (loopDebit word).1)) (bufferTape [])
        ((pre.length : ℤ) + loopBorrowPos word - 1) 0 []
```

### `loopHost_borrow_step`

**Before**

```lean
private lemma loopHost_borrow_step (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (p : Fin (x.length + 2)) (pre rest : List Bool) :
    (loopHost body F anchor findMode).tm.step
      (loopFrame body F base (some (.inr (.inr 8))) p (bufferTape [])
        (bufferTape (pre ++ rest)) (bufferTape []) pre.length 0 []) =
      match rest with
      | [] => loopFrame body F base (some (.inr (.inr 10))) p (bufferTape [])
          (bufferTape pre) (bufferTape []) (pre.length - 1) 0 []
      | true :: us => loopFrame body F base (some (.inr (.inr 9))) p (bufferTape [])
          (bufferTape (pre ++ false :: us)) (bufferTape []) (pre.length - 1) 0 []
      | false :: us => loopFrame body F base (some (.inr (.inr 8))) p (bufferTape [])
          (bufferTape (pre ++ true :: us)) (bufferTape []) (pre.length + 1) 0 []
```

**After**

```lean
private lemma loopHost_borrow_step (body F : FinTM Bool) (anchor : body.State) (forward : Bool)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (p : Fin (x.length + 2)) (pre rest : List Bool) :
    (loopHostM body F anchor forward findMode).tm.step
      (loopFrame body F base (some (.inr (.inr 8))) p (bufferTape [])
        (bufferTape (pre ++ rest)) (bufferTape []) pre.length 0 []) =
      match rest with
      | [] => loopFrame body F base (some (.inr (.inr 10))) p (bufferTape [])
          (bufferTape pre) (bufferTape []) (pre.length - 1) 0 []
      | true :: us => loopFrame body F base (some (.inr (.inr 9))) p (bufferTape [])
          (bufferTape (pre ++ false :: us)) (bufferTape []) (pre.length - 1) 0 []
      | false :: us => loopFrame body F base (some (.inr (.inr 8))) p (bufferTape [])
          (bufferTape (pre ++ true :: us)) (bufferTape []) (pre.length + 1) 0 []
```

### `loopHost_fuel_capture`

**Before**

```lean
private lemma loopHost_fuel_capture (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (c : Cfg (body.k + 1 + (1 + F.k)) Bool F.State x) (t : ℕ)
    (hlive : ∀ u < t, ¬((loopFuelSource body F).runFrom c u).Halted) :
    (loopHost body F anchor findMode).tm.runFrom
        (captureCfg Sum.inl (Sum.inr (Sum.inr (0 : Fin 14))) [] [] c) t =
      captureCfg Sum.inl (Sum.inr (Sum.inr (0 : Fin 14))) [] []
        ((loopFuelSource body F).runFrom c t)
```

**After**

```lean
private lemma loopHost_fuel_capture (body F : FinTM Bool) (anchor : body.State) (forward : Bool)
    (findMode : Bool) {x : List Bool}
    (c : Cfg (body.k + 1 + (1 + F.k)) Bool F.State x) (t : ℕ)
    (hlive : ∀ u < t, ¬((loopFuelSource body F).runFrom c u).Halted) :
    (loopHostM body F anchor forward findMode).tm.runFrom
        (captureCfg Sum.inl (Sum.inr (Sum.inr (0 : Fin 14))) [] [] c) t =
      captureCfg Sum.inl (Sum.inr (Sum.inr (0 : Fin 14))) [] []
        ((loopFuelSource body F).runFrom c t)
```

### `loopHost_fuel_copy`

**Before**

```lean
private lemma loopHost_fuel_copy (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (p : Fin (x.length + 2)) (flag : ℤ → Option Bool) (out : List Bool)
    (rest : List Bool) : ∀ pre,
    (loopHost body F anchor findMode).tm.runFrom
        (loopFrame body F base (some (.inr (.inr 2))) p flag (bufferTape pre)
          (loopCopyTape pre rest) pre.length pre.length out) (rest.length + 1) =
      loopFrame body F base (some (.inr (.inr 3))) p flag (bufferTape (pre ++ rest))
        (bufferTape []) ((pre ++ rest).length - 1) ((pre ++ rest).length - 1) out
```

**After**

```lean
private lemma loopHost_fuel_copy (body F : FinTM Bool) (anchor : body.State) (forward : Bool)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (p : Fin (x.length + 2)) (flag : ℤ → Option Bool) (out : List Bool)
    (rest : List Bool) : ∀ pre,
    (loopHostM body F anchor forward findMode).tm.runFrom
        (loopFrame body F base (some (.inr (.inr 2))) p flag (bufferTape pre)
          (loopCopyTape pre rest) pre.length pre.length out) (rest.length + 1) =
      loopFrame body F base (some (.inr (.inr 3))) p flag (bufferTape (pre ++ rest))
        (bufferTape []) ((pre ++ rest).length - 1) ((pre ++ rest).length - 1) out
```

### `loopHost_fuel_return`

**Before**

```lean
private lemma loopHost_fuel_return (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (p : Fin (x.length + 2)) (flag : ℤ → Option Bool) (word out : List Bool) :
    ∀ j, j ≤ word.length →
    (loopHost body F anchor findMode).tm.runFrom
        (loopFrame body F base (some (.inr (.inr 3))) p flag (bufferTape word)
          (bufferTape []) ((j : ℤ) - 1) ((j : ℤ) - 1) out) (j + 1) =
      loopFrame body F base (some (.inr (.inr 4))) p flag (bufferTape word)
        (bufferTape []) 0 0 out
```

**After**

```lean
private lemma loopHost_fuel_return (body F : FinTM Bool) (anchor : body.State) (forward : Bool)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (p : Fin (x.length + 2)) (flag : ℤ → Option Bool) (word out : List Bool) :
    ∀ j, j ≤ word.length →
    (loopHostM body F anchor forward findMode).tm.runFrom
        (loopFrame body F base (some (.inr (.inr 3))) p flag (bufferTape word)
          (bufferTape []) ((j : ℤ) - 1) ((j : ℤ) - 1) out) (j + 1) =
      loopFrame body F base (some (.inr (.inr 4))) p flag (bufferTape word)
        (bufferTape []) 0 0 out
```

### `loopHost_fuel_setup`

**Before**

```lean
private lemma loopHost_fuel_setup (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (p : Fin (x.length + 2)) (flag : ℤ → Option Bool) (word out : List Bool) :
    (loopHost body F anchor findMode).tm.runFrom
        (loopFrame body F base (some (.inr (.inr 0))) p flag (bufferTape [])
          (bufferTape word) 0 word.length out) (3 * word.length + 4) =
      loopFrame body F base (some (.inr (.inr 4))) p flag (bufferTape word)
        (bufferTape []) 0 0 out
```

**After**

```lean
private lemma loopHost_fuel_setup (body F : FinTM Bool) (anchor : body.State) (forward : Bool)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (p : Fin (x.length + 2)) (flag : ℤ → Option Bool) (word out : List Bool) :
    (loopHostM body F anchor forward findMode).tm.runFrom
        (loopFrame body F base (some (.inr (.inr 0))) p flag (bufferTape [])
          (bufferTape word) 0 word.length out) (3 * word.length + 4) =
      loopFrame body F base (some (.inr (.inr 4))) p flag (bufferTape word)
        (bufferTape []) 0 0 out
```

### `loopHost_init`

**Before**

```lean
private lemma loopHost_init (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) (x : List Bool) :
    (loopHost body F anchor findMode).tm.initCfg x =
      captureCfg Sum.inl (Sum.inr (Sum.inr (0 : Fin 14))) [] []
        ((loopFuelSource body F).initCfg x)
```

**After**

```lean
private lemma loopHost_init (body F : FinTM Bool) (anchor : body.State) (forward : Bool)
    (findMode : Bool) (x : List Bool) :
    (loopHostM body F anchor forward findMode).tm.initCfg x =
      captureCfg Sum.inl (Sum.inr (Sum.inr (0 : Fin 14))) [] []
        ((loopFuelSource body F).initCfg x)
```

### `loopHost_input_rewind`

**Before**

```lean
private lemma loopHost_input_rewind (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (cfg : Cfg (loopHost body F anchor findMode).k Bool (loopHost body F anchor findMode).State x)
    (hs : cfg.state = some (.inr (.inr (4 : Fin 14)))) :
    ∃ t ≤ cfg.inputPos.val + 2,
      (loopHost body F anchor findMode).tm.runFrom cfg t =
        {cfg with state := some (.inr (.inl (true, (body.tm.q₀, false)))), inputPos := 1}
```

**After**

```lean
private lemma loopHost_input_rewind (body F : FinTM Bool) (anchor : body.State) (forward : Bool)
    (findMode : Bool) {x : List Bool}
    (cfg : Cfg (loopHostM body F anchor forward findMode).k Bool (loopHostM body F anchor forward findMode).State x)
    (hs : cfg.state = some (.inr (.inr (4 : Fin 14)))) :
    ∃ t ≤ cfg.inputPos.val + 2,
      (loopHostM body F anchor forward findMode).tm.runFrom cfg t =
        {cfg with state := some (.inr (.inl (true, (body.tm.q₀, false)))), inputPos := 1}
```

### `loopHost_prepare`

**Before**

```lean
private lemma loopHost_prepare (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) (R T : ℕ → ℕ)
    (hF : F.ComputesFunInTime (fun x => Nat.bits (R x.length)) T) (x : List Bool) :
    ∃ (c : Cfg F.k Bool F.State x) (t : ℕ),
      c.state = none ∧ c.output = Nat.bits (R x.length) ∧ t ≤ 5 * T x.length + 7 ∧
      (loopHost body F anchor findMode).tm.runFrom
        ((loopHost body F anchor findMode).tm.initCfg x) t = loopReady body F c
```

**After**

```lean
private lemma loopHost_prepare (body F : FinTM Bool) (anchor : body.State) (forward : Bool)
    (findMode : Bool) (R T : ℕ → ℕ)
    (hF : F.ComputesFunInTime (fun x => Nat.bits (R x.length)) T) (x : List Bool) :
    ∃ (c : Cfg F.k Bool F.State x) (t : ℕ),
      c.state = none ∧ c.output = Nat.bits (R x.length) ∧ t ≤ 5 * T x.length + 7 ∧
      (loopHostM body F anchor forward findMode).tm.runFrom
        ((loopHostM body F anchor forward findMode).tm.initCfg x) t = loopReady body F c
```

### `loopHost_reject`

**Before**

```lean
private lemma loopHost_reject (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool} (c : Cfg body.k Bool body.State x)
    (word : List Bool) (fuel : Cfg F.k Bool F.State x)
    (hc : c.state = none) (ho : c.output = []) :
    ∃ t ≤ 2 * word.length + 4,
      if (loopDebit word).2 then
        (loopHost body F anchor findMode).tm.runFrom
            (loopCall body F anchor false c false (some false) word fuel) t =
          loopCall body F anchor false {c with state := some anchor} true none (loopDebit word).1 fuel
      else
        ((loopHost body F anchor findMode).tm.runFrom
          (loopCall body F anchor false c false (some false) word fuel) t).state = none ∧
        ((loopHost body F anchor findMode).tm.runFrom
          (loopCall body F anchor false c false (some false) word fuel) t).output =
            (if findMode then [] else [false])
```

**After**

```lean
private lemma loopHost_reject (body F : FinTM Bool) (anchor : body.State) (forward : Bool)
    (findMode : Bool) {x : List Bool} (c : Cfg body.k Bool body.State x)
    (word : List Bool) (fuel : Cfg F.k Bool F.State x)
    (hc : c.state = none) (ho : c.output = []) :
    ∃ t ≤ 2 * word.length + 4,
      if (loopDebit word).2 then
        (loopHostM body F anchor forward findMode).tm.runFrom
            (loopCall body F anchor false c false (some false) word fuel) t =
          loopCall body F anchor false {c with state := some anchor} true none (loopDebit word).1 fuel
      else
        ((loopHostM body F anchor forward findMode).tm.runFrom
          (loopCall body F anchor false c false (some false) word fuel) t).state = none ∧
        ((loopHostM body F anchor forward findMode).tm.runFrom
          (loopCall body F anchor false c false (some false) word fuel) t).output =
            (if findMode then [] else [false])
```

### `loopHost_release`

**Before**

```lean
private lemma loopHost_release (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool} (c : Cfg body.k Bool body.State x)
    (word : List Bool) (fuel : Cfg F.k Bool F.State x) :
    (loopHost body F anchor findMode).tm.step
        (loopCall body F anchor true {c with state := none} false (some false) word fuel) =
      loopCall body F anchor false {c with state := some anchor} true none word fuel
```

**After**

```lean
private lemma loopHost_release (body F : FinTM Bool) (anchor : body.State) (forward : Bool)
    (findMode : Bool) {x : List Bool} (c : Cfg body.k Bool body.State x)
    (word : List Bool) (fuel : Cfg F.k Bool F.State x) :
    (loopHostM body F anchor forward findMode).tm.step
        (loopCall body F anchor true {c with state := none} false (some false) word fuel) =
      loopCall body F anchor false {c with state := some anchor} true none word fuel
```

### `loopHost_start`

**Before**

```lean
private lemma loopHost_start (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool} (s : List Bool) (t : ℕ)
    (fuel : Cfg F.k Bool F.State x)
    (hguard : ∀ u < t, (body.tm.runFrom (body.tm.initCfg x) u).state ≠ some anchor)
    (hend : body.tm.runFrom (body.tm.initCfg x) t = Cfg.ofWords anchor (stateWord body.k s)) :
    (loopHost body F anchor findMode).tm.runFrom (loopReady body F fuel) (t + 2) =
      loopCall body F anchor false (Cfg.ofWords anchor (stateWord body.k s))
        true none fuel.output fuel
```

**After**

```lean
private lemma loopHost_start (body F : FinTM Bool) (anchor : body.State) (forward : Bool)
    (findMode : Bool) {x : List Bool} (s : List Bool) (t : ℕ)
    (fuel : Cfg F.k Bool F.State x)
    (hguard : ∀ u < t, (body.tm.runFrom (body.tm.initCfg x) u).state ≠ some anchor)
    (hend : body.tm.runFrom (body.tm.initCfg x) t = Cfg.ofWords anchor (stateWord body.k s)) :
    (loopHostM body F anchor forward findMode).tm.runFrom (loopReady body F fuel) (t + 2) =
      loopCall body F anchor false (Cfg.ofWords anchor (stateWord body.k s))
        true none fuel.output fuel
```
