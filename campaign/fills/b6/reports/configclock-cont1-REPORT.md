# B6 F3 continuation 1 — partial fill report

## Result and checklist

**0/1 targets closed.** Phase 0 is instantiated at actual configuration records. Phase 1
has component lemmas but no clock writer: adjacent-write bookkeeping is escalated as E2.
An independent Phase 2 cleanup endpoint is also supplied. The sole open declaration in the
owned file remains `Turing.exists_configWindowRunnerTM`.

- [x] Phase reached, base hash, and ancestor checks recorded.
- [x] Every new declaration, proposed writer contract, one-cell leaf, and appendix recorded.
- [x] Pass count and conditional time/head ledgers recorded step by step.
- [x] Promotion candidates and escalation E2 recorded.
- [x] External citations, expanded import probe, and canonical R3 diff scan recorded below.
- [x] Both complete v3 screens, new-pair disposition, and “new copies: none” recorded below.
- [x] File size, final sweep, axiom prints, lint, and owned-region comparison recorded below.

The checklist marks reporting obligations, not completion of the target.

## Pin, inputs, and recovery

Base: `94b986d4db7167ab2a8b20d38d4385f11e60be0e`.
The initial clone checked out `complexity/arora-barak-ch3-4` at
`744ed435ece2af4c7f6d4ddd47339d7fb3934815`; the required ancestor check succeeded, and
`fill/b6-configclock-cont1` was created directly at the base.

After the network interruption, automated workspace maintenance had removed the checkout,
candidate, runtime, and logs. No completed delivery ZIP existed. The input attachments were
recovered, and the repository was cloned again on the campaign branch, now at
`df2ef06273c2d3e6de9a4748fc1d12a8298ccf31`. The same ancestor check succeeded again,
before recreating the work branch at exactly the same base. No later campaign source is used.
No rebase, merge, cherry-pick, push, or PR was performed.

The six helper proofs were reconstructed from their complete retained conversation text;
the permitted appendix was rewritten to describe the same partial. The initial helper check
had passed, but its raw log was lost. The verification results and raw logs shipped here are
fresh recovery runs, not reconstructed logs. The earlier interrupted bootstrap is not counted
as a completed bootstrap. Recovery reruns the prescribed sequence from its first module.

Both attachment hashes were verified initially and again after recovery:

| Input | SHA-256 |
|---|---|
| `b6-fill-configclock-cont1.md` | `2196f09ed759323eab6d82708b9b274ecc762c6e0063134faaccdc0651a5fe26` |
| `fill-environment-addendum(9).md` | `a25474c52b6b8e8bc1295fad48278b3356b8fed482d2e49c5874554f6d8d2928` |

The repository brief matches the attachment byte for byte after replacing `@ANCESTOR@`
with the base hash. The consumer probe and recommended helper source are at the original
`audits/evidence/b6-fill-configclock/` paths; the continuation folder has the import probe
and overlay. The original consumer probe is rerun unchanged.

## Source changes

Only the allowed home and Fill appendix of
`TCSlib/Complexity/SpaceComplexity/WindowClock.lean` changed. The target signature and body,
all other public declarations, both imports, module header, and pre-appendix docstring remain
byte-identical to the base. The original five `cw_` lemmas are unchanged. No writer stub,
additional admission, axiom, or public declaration was inserted. No import was added.

| New private declaration | Role |
|---|---|
| `cw_field_total` | Obtains the field-cell total from public layout-length and field-count facts. |
| `cw_record_clock` | Supplies linear clock width and the budget for every `N ≤ configBound + 1`. |
| `cw_leftTM` | The explicitly authorized one-step left-move controller. |
| `cw_left_run` | Its exact endpoint and strict first-return cut at one step. |
| `cw_copy_constant` | Specializes the framed mapped copy to a constant-symbol destination interval. |
| `cw_clear_patch` | Clears a patch with blankness outside its interval, making the entire selected tape blank while preserving all other tapes, all heads, input position, and output. |

The appendix records the helpers, missing writer, E2, and a literal **Proof sketch**.
Two frozen descriptions need maintainer attention at integration: the original Route A sketch
uses width `c_M * L` and mentions `copyTM`/`scanTM`, whereas the binding brief uses field-cell
passes and `copyMapTM`; the “Main definitions” sentence says existing definitions only,
although this partial adds the private leaf `cw_leftTM`. Neither frozen text was edited.

## Arithmetic ledger

Put `n = x.length`, `k = M.k`, `p = posWidth n`, `q = Fintype.card M.State`,
`B = M.configBound n s`, and `L = recordLength k n s`. Let `C` be F2's certification constant.

1. The public layout facts give `L = k(2s + 1) + p + k + 4` and field count `k + 3`.
   Subtracting the separators gives
   `F = sum (map length (cfgRecord s d τ)) = k(2s + 1) + p + 2`.
   Hence `F ≥ 2`, `F ≤ L`, and `L ≤ 2F`.
2. Choose exactly `c = C + q + 8`, and `W = cF`. Then `W ≤ cL`.
   The pass count is fixed by the machine and F2's chosen constant; the word width varies
   with the record. The lemma is generic in `C`.
3. `record_pos_lt` supplies `n + 2 ≤ 2^p`, and the owned module's proved
   `configBound_le_two_pow` supplies `B ≤ 2^(q + p + 3k(2s + 1))`.
4. The retained `cw_round_cost` gives `L + n + 1 ≤ 2^(L + 1)`.
   Also `C ≤ 2^C` and `B + 1 ≤ 2^(q + p + 3k(2s + 1) + 1)`.
   The exponent of their product is at most `C + q + 5F + 2`, strictly below
   `(C + q + 8)F` because `F ≥ 2`.
5. Thus the retained `cw_budget` yields `C(B + 1)(L + n + 1) ≤ 2^W - 1`.
   Monotonicity for `N ≤ B + 1` and `cw_true_value` give `cw_record_clock`'s exact
   `Nat.ofDigits` budget. This includes the extra halt-test round.
6. The retained **conditional** time inequality is
   `A(L + 1) + (5(2^W - 1) + 2W + 3) + (2W + 2) + D`
   `≤ (A + 4c + D + 10) * 2^((A + 4c + D + 10)(L + 1))`.
   A proved writer must supply `A`; the actual dispatch composition must supply `D`.
   Neither is instantiated by a machine construction here.
7. The retained head inequality is `C(L + W + 1) ≤ C(c + 1)(L + 1)`.
   The new clear lemma supplies an endpoint only. The composed first-return cut, all-times
   head envelope, silence, space bound, semantic exits, and a single common final constant
   remain obligations of the open target.

## Escalation and promotion requests

**E2 — shared adjacent-write bookkeeping is private.** Consecutive constant field writes
must be identified with one contiguous clock word. The pinned tree already proves the shared
adjacent-write identity as the private `rt_adjacentWrites` in `Build/RecordTable.lean`,
base line 3199. Its signature was inspected; its proof was not copied or cited.
No public adjacent-write or `wordPatch`-append theorem was found at the pin. The public
`wordPatch_of_mem` and `wordPatch_of_not_mem` give cell cases, but repeating the adjacent-write
argument would duplicate existing shared bookkeeping. Rule 7 forbids that duplication;
rule 10 forbids citing the private lemma. Work stopped on the writer under rule 4.

Requested resolution: expose the existing adjacent-write identity, or its constant-fill
specialization, identifying

```text
if o + a ≤ z ∧ z < o + a + b then some e
else if o ≤ z ∧ z < o + a then some e
else tape z
```

with

```text
if o ≤ z ∧ z < o + (a + b) then some e else tape z.
```

Here `a,b` are natural widths cast to integers. This is a reuse-policy escalation, not a
counterexample to the target or a claim of mathematical difficulty. Publishing the identity
does not itself complete the writer: its prescribed composition and ledger are still needed.

**Cleanup interface resolved without another escalation.** An earlier plan considered the
private `sc_wordPatch_twice` in `Build/StepClock.lean`, base line 263; only its signature was
inspected. `cw_clear_patch` avoids normalizing two patches. It accepts any underlying tape
blank outside the interval, uses public cell equations, and applies the framed clear row.
It neither cites nor replaces that private overwrite identity. The actual writer/F2
composition and its frame hypotheses remain open.

Route B was not executed. Its general-alphabet counter-loop layout would require the separate
escalation prescribed by the brief; no alternate host or layout unfolding was attempted.

Promotion candidates, notes only:

- `cw_leftTM`, with `cw_left_run`: `Bool` states, entry `false`, exit `true`, exactly one
  left move on the selected work head, preserved input/tapes/output, and a strict first-return
  cut. This is the brief's authorized leaf.
- The **uninserted** generic clock writer, with the recommended contract: for alphabet `Γ`,
  symbol `e`, fixed field count `m` and pass count `c`, a finite-state two-tape machine takes
  `RecordAt d 0 fs`, `fs.length = m`, nonempty fields, and blank tape 1, to a contiguous word
  of `e` of width `c * (fs.map List.length).sum` at tape 1's initial head. It returns both
  heads, input position, and output; preserves tape 0 and the tape-1 exterior; has a strict
  first-return cut and unchanged output throughout; and has time and head displacement at
  most `C_writer * ((joinFields fs).length + 1)`. This was not weakened into a delivered theorem.

## Open declaration

`Turing.exists_configWindowRunnerTM` is the only open declaration in the owned file.

**Proof sketch (remaining).** After obtaining the public adjacent-write identity, assemble
the fixed number of mapped-copy/skip/left-move passes with the prescribed seams or phase host.
Rewind the source across its fields and return the contiguous clock head. Embed the proved
writer by R1, run F2, clear only halted/left endpoints, and dispatch through the prescribed
host. Use `cw_record_clock` for certification and the conditional time/head inequalities
for a common constant; use the determined endpoint and `windowRun_stop_unique` as required.
That composition is absent. The target's axiom walk below still includes `sorryAx`.

## Runtime

The unmodified official Lean 4.25.0 release was installed. Its first version check failed with
`error: failed to locate application`, both initially and after recovery. The exact attached
environment addendum was followed. The included source `evidence/runtime/executable-path.c`
has SHA-256 `985924ad83d39e108c0a2107bab07e65cdeb88641453508ab5acda115534fba7`.
It was compiled with `cc -shared -fPIC -O2 ... -ldl`. No compiled shim or build product is shipped.
The preload is scoped to Lean/Lake and the prescribed check script; no toolchain files or
filesystem permissions were changed. The exact recovery environment is printed below.

Mathlib is pinned at `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.
Recovery ran `lake exe cache get` for the 54 Mathlib roots used by the order list and unpacked
their 1,025-module closure. It ran in the pinned Mathlib project; its dependency directories
were exposed to the root checker through symlinks under `.lake/packages`.
Extraction used `--no-same-owner`, with `TAR_OPTIONS=--no-same-owner` for cache setup.
No `lake build` was run. Every proof check used the unmodified `scripts/lean_check_tree.sh`.

## Verification results

The recovered bootstrap checked all 176 prescribed modules sequentially on the unchanged base.
The final sweep rechecked all 176 using two isolated output trees, seeded with hard links
to the completed bootstrap and the successful final owned-module check. The unmodified
checker unlinks its target before each compilation. Dependencies are read-only, and sources
remain fixed throughout the sweep. The combined log is in prescribed module order.

Each worker additionally sets `TCSLIB_OLEANS` to
`/workspace/scratch/8032237c75d4/runtime/final-oleans-01/worker-0` or `worker-1`.

| Check | Result |
|---|---|
| Bootstrap | 176/176; zero errors; exact base admission set. |
| Final sweep | 176/176; zero errors; same 28 admissions in 11 modules. |
| Owned module | Exactly one warning, for the unchanged open target; no other warning. |
| Other modules | Exactly the 27 named out-of-scope admissions. |
| Expanded import probe | Zero errors and zero warnings. |
| Unchanged consumer probe | Zero errors and zero warnings. |
| Axiom prints | Target has `sorryAx`; all six new privates have only standard axioms. |
| Freeze | Only permitted home and appendix changed; all public statements and imports unchanged. |

Source and region check:
```text
OWNED REGIONS PASS; imports/public declarations/target signature and body unchanged
Original five helpers unchanged; no declaration removed
Lines: 452 ; public: 4 ; private: 11
New: cw_field_total, cw_record_clock, cw_leftTM, cw_left_run, cw_copy_constant, cw_clear_patch
No new line over 100 characters
```

Final sweep tail:
```text
CHECK 171 TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenStage
EXIT 0; seconds 4.55
CHECK 172 TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenLoop
EXIT 0; seconds 4.93
CHECK 173 TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenCorrect
EXIT 0; seconds 4.61
CHECK 174 TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi
EXIT 0; seconds 1.53
CHECK 175 TCSlib/Complexity/SpaceComplexity/Savitch
TCSlib/Complexity/SpaceComplexity/Savitch.lean:81:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Savitch.lean:114:8: warning: declaration uses 'sorry'
EXIT 0; seconds 1.54
CHECK 176 TCSlib/Complexity/SpaceComplexity
EXIT 0; seconds 1.55
FINAL SWEEP PASS: 176/176 modules; failures=0
```

Lint summary:
```text
style_lint: 0 FAIL, 81 WARN over 107 files
```

Exact runtime environment and version:
```text
Unmodified Lean --version: exit 1; error: failed to locate application
Lean (version 4.25.0, x86_64-unknown-linux-gnu, commit cdd38ac5115bdeec5f609e9126cce00f51ae88b3, Release)

Exact recovery environment:
PATH=/workspace/scratch/8032237c75d4/runtime/lean-4.25.0-linux/bin:/root/.codex/tmp/arg0/codex-arg0r0Q923:/opt/codex/codex-path:/opt/codex/runtimes/codex-primary-runtime/dependencies/bin/override:/opt/codex/runtimes/codex-primary-runtime/dependencies/python/bin:/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin:/opt/codex/runtimes/codex-primary-runtime/dependencies/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/opt/codex/runtimes/codex-primary-runtime/dependencies/bin/fallback
LEAN_SYSROOT=/workspace/scratch/8032237c75d4/runtime/lean-4.25.0-linux
LAKE_HOME=/workspace/scratch/8032237c75d4/runtime/lean-4.25.0-linux
LD_PRELOAD=/workspace/scratch/8032237c75d4/runtime/executable-path.so
```

Recovered pin and attachment verification:
```text
b6-fill-configclock-cont1.md SHA-256 2196f09ed759323eab6d82708b9b274ecc762c6e0063134faaccdc0651a5fe26
fill-environment-addendum(9).md SHA-256 a25474c52b6b8e8bc1295fad48278b3356b8fed482d2e49c5874554f6d8d2928
Repository brief matches after @ANCESTOR@ substitution
Recovery campaign HEAD df2ef06273c2d3e6de9a4748fc1d12a8298ccf31
Ancestor check PASS
Work branch created at 94b986d4db7167ab2a8b20d38d4385f11e60be0e
```

### Admission inventory

The base list was recorded before recovery proof checks:

```text
TuringMachine/Simulation: 1: branchTM_spaceUsed
TuringMachine/Composition: 3: idTM_computes, ifEqTM_computes, condTM_computes_iff
TuringMachine/Build/Wrappers: 2: timedCondTM_computes, timedCondTM_spaceUsed
TuringMachine/Build/Loop: 5: loopHostTM_contracts, loopHostTM_decides, loopHostTM_finds, loopHostTM_spaceUsed_le_budget, emitLoopTM_computes
TuringMachine/Encoding: 1: pairDiagTM_computes
ClassP/TimeConstructible: 2: _root_.Turing.FinTM.lengthBitsTM_computes, _root_.Turing.FinTM.lengthBitsTM_spaceUsed
TuringMachine/Build/Primitives: 3: polyUnaryTM_spaceUsed, unaryTokenTM_computes, appendBitTM_computes
TuringMachine/Build/RecordTable: 4: exists_tableFindTM, exists_tableAppendTM, exists_recordValidTM, exists_recordNextTM
SpaceComplexity/Hierarchy: 4: space_universal, space_hierarchy, LOGSPACE_ssubset_PSPACE, SPACE_linear_ne_NP
SpaceComplexity/WindowClock: 1: exists_configWindowRunnerTM
SpaceComplexity/Savitch: 2: spaceConstructible_poly, savitch
TOTAL 28
```

Final declaration-keyed comparison:
```text
Admission warnings: 28 ; distinct declarations: 28 ; modules: 11
Added: []
Missing: []
ClassP/TimeConstructible: _root_.Turing.FinTM.lengthBitsTM_computes
ClassP/TimeConstructible: _root_.Turing.FinTM.lengthBitsTM_spaceUsed
SpaceComplexity/Hierarchy: LOGSPACE_ssubset_PSPACE
SpaceComplexity/Hierarchy: SPACE_linear_ne_NP
SpaceComplexity/Hierarchy: space_hierarchy
SpaceComplexity/Hierarchy: space_universal
SpaceComplexity/Savitch: savitch
SpaceComplexity/Savitch: spaceConstructible_poly
SpaceComplexity/WindowClock: exists_configWindowRunnerTM
TuringMachine/Build/Loop: emitLoopTM_computes
TuringMachine/Build/Loop: loopHostTM_contracts
TuringMachine/Build/Loop: loopHostTM_decides
TuringMachine/Build/Loop: loopHostTM_finds
TuringMachine/Build/Loop: loopHostTM_spaceUsed_le_budget
TuringMachine/Build/Primitives: appendBitTM_computes
TuringMachine/Build/Primitives: polyUnaryTM_spaceUsed
TuringMachine/Build/Primitives: unaryTokenTM_computes
TuringMachine/Build/RecordTable: exists_recordNextTM
TuringMachine/Build/RecordTable: exists_recordValidTM
TuringMachine/Build/RecordTable: exists_tableAppendTM
TuringMachine/Build/RecordTable: exists_tableFindTM
TuringMachine/Build/Wrappers: timedCondTM_computes
TuringMachine/Build/Wrappers: timedCondTM_spaceUsed
TuringMachine/Composition: condTM_computes_iff
TuringMachine/Composition: idTM_computes
TuringMachine/Composition: ifEqTM_computes
TuringMachine/Encoding: pairDiagTM_computes
TuringMachine/Simulation: branchTM_spaceUsed
BASE SORRY SET MATCH: 28 total, 27 outside the target
```

### Rule 10 and Rule 11

No added proof unfolds an external TCSlib definition. The frozen public bridges, including
their pre-existing implementation, are unchanged. Every new helper consumes public APIs.
The explicit external declarations named in new and retained helper text, including public
model fields and standard Lean/Mathlib names, are:

```text
Turing.Cfg
Turing.Cfg.ext
Turing.FinTM
Turing.MultiTapeTM
Turing.SweepPhase
Turing.cfgRecord_length
Turing.cfgRecord
Turing.joinFields_length
Turing.joinFields_cfgRecord_length
Turing.recordLength
Turing.recordLength_eq
Turing.posWidth
Turing.record_pos_lt
Turing.tapeAction
Turing.MultiTapeTM.runFrom
Turing.MultiTapeTM.runFrom_zero
Turing.MultiTapeTM.runFrom_succ_eq_step'
Turing.step_of_tapeAction_move
Turing.moveInputPos_zero
Turing.copyMapTM
Turing.copyMapTM_run_ofCfg
Turing.FinTM.bufferTape
Turing.FinTM.bufferTape_nat
Turing.FinTM.bufferTape_left
Turing.clearTM
Turing.clearTM_run_ofCfg
Turing.wordPatch
Turing.wordPatch_of_mem
Turing.wordPatch_of_not_mem
Nat.mul_le_mul_left
Nat.mul_le_mul_right
Int.toNat_of_nonneg
List.length_nil
List.getElem?_eq_getElem
List.getElem?_length
SignType.coe_neg_one
sub_eq_add_neg
Fintype.card
Function.update
Bool
Fin
List.replicate
Nat.ofDigits
Bool.toNat
List.map
List.sum
List.length
List.replicate_succ
List.map_cons
Nat.ofDigits_cons
Bool.toNat_true
pow_succ
Nat.pow_pos
Nat.pow_le_pow_right
Nat.lt_two_pow_self
pow_add
Nat.mul_le_mul
Nat.pow_lt_pow_right
Nat.le_sub_one_of_lt
lt_of_le_of_lt
Nat.one_le_pow
Nat.sub_le
if_pos
if_neg
ite_true
true_and
false_and
ite_false
Turing.FinTM.configBound
Turing.joinFields
Turing.Cfg.mk
Turing.Cfg.state
Turing.Cfg.inputPos
Turing.Cfg.workTapes
Turing.Cfg.workTapePos
Turing.Cfg.output
Turing.MultiTapeTM.mk
Turing.MultiTapeTM.q₀
Turing.MultiTapeTM.tr
Turing.FinTM.k
Turing.FinTM.State
Turing.SweepPhase.sweep
Turing.SweepPhase.done
SignType.neg
```

The expanded probe has 128 checks: the original 60 plus 68 additions. Its exact source
and output are in `logs/final-sweep.log`. Original probe names unused by the partial are
not claimed as proof dependencies.

Added-line scan for the six prohibited canonical R3 rows:
```text
Added-line diff scan with rg -n \b(copyTM_run|transferTM_run|clearTM_run|compareTM_run|incrementTM_run_succ|incrementTM_run_overflow)\b
Exit 1: no forbidden canonical R3 row name found.
```

### Axiom walk

A scratch copy of the exact final source prints the target, original five
helpers, and all six new private declarations:

```text
F3Axioms.lean:420:8: warning: declaration uses 'sorry'
'Turing.exists_configWindowRunnerTM' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'_private.F3Axioms.0.Turing.cw_true_value' depends on axioms: [propext, Quot.sound]
'_private.F3Axioms.0.Turing.cw_round_cost' depends on axioms: [propext, Quot.sound]
'_private.F3Axioms.0.Turing.cw_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.F3Axioms.0.Turing.cw_time_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.F3Axioms.0.Turing.cw_head_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.F3Axioms.0.Turing.cw_field_total' depends on axioms: [propext, Quot.sound]
'_private.F3Axioms.0.Turing.cw_record_clock' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.F3Axioms.0.Turing.cw_leftTM' does not depend on any axioms
'_private.F3Axioms.0.Turing.cw_left_run' depends on axioms: [propext, Quot.sound]
'_private.F3Axioms.0.Turing.cw_copy_constant' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.F3Axioms.0.Turing.cw_clear_patch' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Duplication ledger

Before: declarations screened: 1043; copy pairs (target reproduces >= half of source): 510; reproduced text: 147,693 chars
After: declarations screened: 1048; copy pairs (target reproduces >= half of source): 510; reproduced text: 147,693 chars
New cross-file pairs involving the owned file: 0.
New in-file pairs: 0. Removed pairs: 0.
new copies: none
Copied proved material introduced: 0 lines (0%).
All 21 after-screen inputs match the final delivery tree byte-for-byte, with unchanged saved hashes.

All 107 Lean files used by the detached-worktree lint also match the final delivery tree byte-for-byte.

After-screen source hashes
Pinned base plus final owned source
3ee710b1abf69670926e0dd1f6b2429d330960aa28562fe38499964c50cb53ae  TCSlib/Complexity/TuringMachine/Build/WindowRun.lean
77409831e63abc4d12d2bda4f195d8f50a8dc20cdd3e001ebca9c26db19f2674  TCSlib/Complexity/TuringMachine/Build/StepClock.lean
1a2569fcb962efd00afff557e707def3d9f43dbe5cc2de11ee24f1fabddfe420  TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean
62a3309f46a609ebc0e3fcb13e3385d56cd77962bb0655a39bf3561e720569e9  TCSlib/Complexity/TuringMachine/Build/RecordTable.lean
a81e9992e6b20051a7e3131512518490ca979092cae15c3098784d2bd7eb3b6c  TCSlib/Complexity/TuringMachine/Build/Catalog.lean
14b3b7978928ceba4af9438ce26639be19e96557693fbecfe1bdabad4958675c  TCSlib/Complexity/TuringMachine/Build/Seam.lean
95ae78fafbc8c7585f9b0c603796ae843d1e7ae25788359cb6a94c8e9ad25575  TCSlib/Complexity/TuringMachine/Build/Embed.lean
0b9ac758e248b875bbadb898f178d459fd90d15a0ec536bb81c427e9b2d6019e  TCSlib/Complexity/TuringMachine/StateRenaming.lean
3df8fee97b9d07ac0a201ae4f8a20d305b518d9ad3ad69ba7aad8ffad5f44556  TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean
794de6c5654e3b7bda869f5ff21128946871118c2b49b59809aa5f676e6ed3ec  TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean
1f734ac5fa5ffd51f3e2025f444362999096a909d53fd1023717603ce323bfcb  TCSlib/Complexity/TuringMachine/Build/Contract/Embed.lean
afefb6f3cf85c537de6b40d7951d3519ab73bcbecf95428a97386c275e871938  TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean
427daa23c459618e5397d7c7c332c1e269e1dbe3b873c45e114eb6b3a87edd21  TCSlib/Complexity/TuringMachine/Build/InputCall.lean
a8decd2fe79b24797a18c17c3df003a6add03383a5567d5043501be6a6ca61cf  TCSlib/Complexity/TuringMachine/Simulation.lean
7ac69ec66e94226e16f97ccd0981b1dc6f25ca321bae15469532da7f3ba1d925  TCSlib/Complexity/TuringMachine/Deterministic.lean
3081733db115d264eac736a0359e6db3ec5f0238aa3639d2f905fec1972681dc  TCSlib/Complexity/TuringMachine/Configuration.lean
92c869b49c01621b9d0fcf5f77371839b770df07345ff3c9338224bd42ec42ac  TCSlib/Complexity/TuringMachine/Finite.lean
fba3964b3d79123b9aa0400e14acd50f8dd6c509f5a7657c1d143be0b2ac8556  TCSlib/Complexity/SpaceComplexity/WindowClock.lean
eaaddf6236b46d143a1f420196137ec52fd2d978cd48b7126e3dce4642996a93  TCSlib/Complexity/SpaceComplexity/Hierarchy.lean
50dfa99307ab6716850ef897e8e0839e8490d4d2645d790860cc84d99508692e  TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean
b852e62030fd8cf4b6c607a908da378370590d1d526632788c7824530eac04ed  TCSlib/Complexity/SpaceComplexity/ConfigCount.lean

Six declarations were added; five meet the screen floor. `cw_leftTM` has a body shorter
than 60 characters. Both runs used the unmodified v3 screen under `nice -n 10`, with
the same 21 repository paths, one run at a time. The before run finished before the after
run began. The before output is byte-identical to the supplied baseline. The after run
used a detached worktree at the same base with only the final owned source replaced, so
the bootstrap source could stay unchanged. All 21 files were compared against the final
delivery tree. No private proof from another file was transcribed.

### Complete before output

```text
declarations screened: 1043; copy pairs (target reproduces >= half of source): 510; reproduced text: 147,693 chars
   Simulation.lean::ComputesInTime.spaceUsed_le  reproduces  Catalog.lean::f2_space_of_time: 713/713 = 100%
   Catalog.lean::f2_space_of_time  reproduces  Simulation.lean::ComputesInTime.spaceUsed_le: 713/713 = 100%
   Simulation.lean::timed_rewind  reproduces  Catalog.lean::f2_catalogRewind: 435/435 = 100%
   Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::timed_rewind: 435/435 = 100%
   Catalog.lean::f2_finSumEquiv  reproduces  Catalog.lean::a2_mapSumEquiv: 362/362 = 100%
   Catalog.lean::a2_mapSumEquiv  reproduces  Catalog.lean::f2_finSumEquiv: 362/362 = 100%
   CfgRecord.lean::recordRun_trans  reproduces  Basic.lean::Turing.Segment.trans: 291/291 = 100%
   Catalog.lean::step_of_tapeAction_write  reproduces  Catalog.lean::step_of_tapeAction_move: 167/167 = 100%
   Catalog.lean::step_of_tapeAction_move  reproduces  Catalog.lean::step_of_tapeAction_write: 167/167 = 100%
   Finite.lean::runFrom_state_ne_none_of_le  reproduces  Catalog.lean::f2_loop_live_prefix: 156/156 = 100%
   Catalog.lean::f2_loop_live_prefix  reproduces  Finite.lean::runFrom_state_ne_none_of_le: 156/156 = 100%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right: 135/135 = 100%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr: 135/135 = 100%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::skipTM: 129/129 = 100%
   ConfigGraph.lean::outSummary_eq_empty_iff  reproduces  ConfigGraph.lean::outSummary_eq_accept_iff: 77/77 = 100%
   ConfigGraph.lean::outSummary_eq_accept_iff  reproduces  ConfigGraph.lean::outSummary_eq_empty_iff: 77/77 = 100%
   CfgRecord.lean::Turing.{k#2  reproduces  CfgRecord.lean::Turing.{k#1: 66/66 = 100%
   CfgRecord.lean::Turing.{k#1  reproduces  CfgRecord.lean::Turing.{k#2: 66/66 = 100%
   TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::branch_positive  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::seq_positive: 62/62 = 100%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 1304/1306 = 100%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Simulation.lean::rewind_from_any: 465/466 = 100%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::Cfg.ofWords_transfer_endpoint: 478/480 = 100%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 1304/1314 = 99%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::Cfg.ofWords_copy_endpoint: 228/230 = 99%
   Basic.lean::Turing.Segment.trans  reproduces  CfgRecord.lean::recordRun_trans: 291/294 = 99%
   Catalog.lean::Cfg.ofWords_transfer_endpoint  reproduces  Catalog.lean::Cfg.ofWords_copy_endpoint: 227/230 = 99%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentRetTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmitRetTM: 215/219 = 98%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::Cfg.ofWords_copy_endpoint: 225/230 = 98%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_left  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr: 132/135 = 98%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_left  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right: 132/135 = 98%
   Catalog.lean::f2_lenSuffix_run  reproduces  Catalog.lean::f2_lenParse_first: 312/320 = 98%
   Configuration.lean::moveInputPos_pos_of_ne_right  reproduces  Configuration.lean::moveInputPos_rightBoundary: 71/73 = 97%
   Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairConcat_spaceUsed: 305/314 = 97%
   Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairConcat_spaceUsed: 305/314 = 97%
   Catalog.lean::f2_scanTrues_run  reproduces  Catalog.lean::f2_scanStep_right: 159/164 = 97%
   Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairSnd_spaceUsed: 305/317 = 96%
   Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairFst_spaceUsed: 305/317 = 96%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::copyTM_run: 388/404 = 96%
   Catalog.lean::transferMapTM  reproduces  Catalog.lean::copyMapTM: 478/498 = 96%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmitRetTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentRetTM: 215/224 = 96%
   Catalog.lean::clearTM_run  reproduces  Catalog.lean::Cfg.ofWords_copy_endpoint: 220/230 = 96%
   Catalog.lean::f2_extract_replay  reproduces  Catalog.lean::f2_rawStrip_replay: 393/412 = 95%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::a2_call_run: 299/315 = 95%
   Catalog.lean::f2_loopCall_reframe  reproduces  Catalog.lean::f2_loopCall_frame: 500/527 = 95%
   Basic.lean::RoundContract  reproduces  Basic.lean::ReturnContract: 412/436 = 94%
   Catalog.lean::f2_incFixed_computes  reproduces  Catalog.lean::f2_scanStep_right: 154/164 = 94%
   Configuration.lean::moveInputPos_neg_of_ne_left  reproduces  Configuration.lean::moveInputPos_rightBoundary: 68/73 = 93%
   Catalog.lean::f2_pairDup_double  reproduces  Catalog.lean::f2_scanStep_right: 152/164 = 93%
   Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairFst_spaceUsed: 293/317 = 92%
   Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairSnd_spaceUsed: 293/317 = 92%
   Catalog.lean::f2_branch_space  reproduces  Catalog.lean::catalog_space_one: 115/125 = 92%
   Catalog.lean::a2_map_block  reproduces  Catalog.lean::a2_map_move: 331/362 = 91%
   CounterLoop.lean::counterLoopTMVia  reproduces  CounterLoop.lean::counterLoopTM: 261/287 = 91%
   Simulation.lean::rewind_heads  reproduces  Simulation.lean::timed_rewind: 395/435 = 91%
   Simulation.lean::rewind_heads  reproduces  Catalog.lean::f2_catalogRewind: 395/435 = 91%
   Simulation.lean::rewind_from_any  reproduces  Catalog.lean::f2_loop_rewind_bounded: 465/514 = 90%
   Catalog.lean::f2_splitEmbed_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr: 122/135 = 90%
   Catalog.lean::f2_splitEmbed_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right: 122/135 = 90%
   Catalog.lean::copyMapTM  reproduces  Catalog.lean::clearTM: 369/409 = 90%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_move: 326/362 = 90%
   Catalog.lean::incrementTM_run_succ_ofCfg  reproduces  Catalog.lean::incrementTM_run_overflow_ofCfg: 617/686 = 90%
   Catalog.lean::copyMapTM  reproduces  Catalog.lean::transferMapTM: 478/533 = 90%
   StateRenaming.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr: 121/135 = 90%
   StateRenaming.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right: 121/135 = 90%
   Catalog.lean::f2_loopHost_halt_return  reproduces  Catalog.lean::a2_call_run: 279/315 = 89%
   Deterministic.lean::step  reproduces  Deterministic.lean::outputSymbol: 76/86 = 88%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::transferTM_spaceUsedByTape: 625/713 = 88%
   Deterministic.lean::outputSymbol  reproduces  Deterministic.lean::step: 76/87 = 87%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::clearTM_run: 336/385 = 87%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 632/725 = 87%
   Catalog.lean::f2_loopHost_borrow_run  reproduces  Catalog.lean::f2_loopBorrow_run: 414/476 = 87%
   Catalog.lean::a2_map_backB  reproduces  Catalog.lean::a2_map_backA: 806/927 = 87%
   Catalog.lean::f2_loopHost_body_capture  reproduces  Catalog.lean::f2_loopHost_fuel_capture: 96/111 = 86%
   CfgRecord.lean::recordStep_reject_run  reproduces  CfgRecord.lean::recordStep_empty_run: 467/541 = 86%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::copyTM_spaceUsedByTape: 625/727 = 86%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentCfg  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmitCfg: 165/192 = 86%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 664/776 = 86%
   CfgRecord.lean::recordStep_empty_run  reproduces  CfgRecord.lean::recordStep_reject_run: 467/547 = 85%
   Basic.lean::Cfg.SameOutside.keep_blank  reproduces  Basic.lean::endpoint_not_mem: 97/114 = 85%
   TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::seq_positive  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::branch_positive: 62/73 = 85%
   Basic.lean::safeSegment_iff  reproduces  Basic.lean::segment_iff: 84/99 = 85%
   Basic.lean::time_box  reproduces  Basic.lean::time_envelope: 123/146 = 84%
   Catalog.lean::transferMapTM  reproduces  Catalog.lean::clearTM: 344/409 = 84%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::seekEndTM: 173/206 = 84%
   CounterLoop.lean::counterLoopTM  reproduces  CounterLoop.lean::counterLoopTMVia: 261/311 = 84%
   Catalog.lean::a2_call_heads  reproduces  Catalog.lean::a2_fuel_heads: 515/615 = 84%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 1092/1306 = 84%
   CounterLoop.lean::counterLoopTM_run_escape  reproduces  CounterLoop.lean::counterLoopTM_run_done: 393/471 = 83%
   Catalog.lean::clearTM_run  reproduces  Catalog.lean::copyTM_run: 336/404 = 83%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 1092/1314 = 83%
   WindowRun.lean::wl_Ctrl_decidableEq  reproduces  WindowRun.lean::wr_Ctrl_decidableEq: 63/76 = 83%
   Catalog.lean::a2_map_backA  reproduces  Catalog.lean::a2_map_backB: 806/975 = 83%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_extract_rewind: 632/767 = 82%
   Catalog.lean::f2_loopHost_fuel_capture  reproduces  Catalog.lean::f2_loopHost_body_capture: 96/117 = 82%
   Basic.lean::hullLo  reproduces  Basic.lean::hullHi: 114/139 = 82%
   Basic.lean::hullHi  reproduces  Basic.lean::hullLo: 114/139 = 82%
   CfgRecord.lean::recordStep_copyback_run  reproduces  CfgRecord.lean::recordStep_reject_run: 448/547 = 82%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 664/814 = 82%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::clearTM_run: 314/385 = 82%
   StateRenaming.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Catalog.lean::f2_splitEmbed_run: 153/188 = 81%
   Catalog.lean::f2_sum_add  reproduces  Catalog.lean::a2_map_sum: 153/188 = 81%
   Catalog.lean::a2_map_sum  reproduces  Catalog.lean::f2_sum_add: 153/188 = 81%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 1077/1329 = 81%
   Simulation.lean::rightCfg_step  reproduces  Simulation.lean::leftCfg_step: 306/378 = 81%
   Catalog.lean::step_of_tapeAction_write  reproduces  Catalog.lean::step_of_inputMoveAction: 68/84 = 81%
   Catalog.lean::step_of_tapeAction_move  reproduces  Catalog.lean::step_of_inputMoveAction: 68/84 = 81%
   Catalog.lean::f2_counter_count_space  reproduces  Catalog.lean::f2_counter_count: 363/452 = 80%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::skipBackTM: 162/202 = 80%
   CounterLoop.lean::counterLoopTMVia_done_segment  reproduces  CounterLoop.lean::counterLoopTMVia_escape_segment: 332/414 = 80%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilent_step  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmit_step: 315/393 = 80%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1092/1366 = 80%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1092/1366 = 80%
   Simulation.lean::leftCfg_step  reproduces  Simulation.lean::rightCfg_step: 306/384 = 80%
   Catalog.lean::f2_extract_suffix  reproduces  Catalog.lean::f2_extract_first: 238/300 = 79%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentRet_step  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentRetTM_visitedByTapeHead: 106/134 = 79%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::skipTM: 102/129 = 79%
   Catalog.lean::a2_call_heads  reproduces  Catalog.lean::f2_loopCall_heads: 520/658 = 79%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitPrepare_scan: 526/666 = 79%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1077/1366 = 79%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::branchTM_computes: 632/802 = 79%
   Catalog.lean::transferTM_run_ofCfg  reproduces  Catalog.lean::copyTM_run_ofCfg: 89/113 = 79%
   Configuration.lean::moveInputPos_neg_of_ne_left  reproduces  Configuration.lean::moveInputPos_pos_of_ne_right: 85/108 = 79%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::a2_mapSetup_run: 128/163 = 79%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::skipTM: 101/129 = 78%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::incrementTM_run_overflow: 383/491 = 78%
   CfgRecord.lean::recordStep_position_run  reproduces  CfgRecord.lean::recordStep_reject_run: 426/547 = 78%
   Catalog.lean::a2_loop_prepare  reproduces  Catalog.lean::f2_loopHost_prepare: 1165/1499 = 78%
   Basic.lean::endpoint_not_mem  reproduces  Basic.lean::traj_iff: 80/103 = 78%
   Basic.lean::Frames.trans  reproduces  Basic.lean::traj_iff: 80/103 = 78%
   Basic.lean::Cfg.SameOutside.keep_blank  reproduces  Basic.lean::traj_iff: 80/103 = 78%
   Catalog.lean::incrementTM_run_overflow  reproduces  Catalog.lean::clearTM_run: 299/385 = 78%
   Catalog.lean::compareTM  reproduces  Catalog.lean::incrementTM: 408/526 = 78%
   Catalog.lean::f2_counterTape_write  reproduces  Catalog.lean::f2_loopBuffer_write: 311/408 = 76%
   Catalog.lean::f2_scanCopy_run  reproduces  Catalog.lean::f2_scanStep_right: 125/164 = 76%
   CounterLoop.lean::counterLoopTMVia_escape_witness  reproduces  CounterLoop.lean::counterLoopTMVia_done_witness: 738/969 = 76%
   CounterLoop.lean::decrementTM_run_succ_ofCfg  reproduces  CounterLoop.lean::counter_complement_twice: 67/88 = 76%
   Catalog.lean::f2_loopBorrow_run  reproduces  Catalog.lean::f2_loopHost_borrow_run: 414/544 = 76%
   ConfigCount.lean::visitedByTapeHead_mono  reproduces  Deterministic.lean::mem_visitedByTapeHead_iff: 60/79 = 76%
   ConfigCount.lean::ComputesInTime.of_spaceUsed_le  reproduces  Deterministic.lean::mem_visitedByTapeHead_iff: 60/79 = 76%
   Basic.lean::round_iff  reproduces  Basic.lean::segment_iff: 75/99 = 76%
   Catalog.lean::f2_loopBorrow_step  reproduces  Catalog.lean::f2_loopReplay_step: 258/341 = 76%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmitRet_step  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmitRetTM_visitedByTapeHead: 87/115 = 76%
   Simulation.lean::rightCfg_apply  reproduces  Simulation.lean::leftCfg_apply: 142/188 = 76%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM: 148/196 = 76%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::a2_mapSetup_run: 123/163 = 75%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Catalog.lean::f2_splitPrepare_extra: 356/472 = 75%
   CounterLoop.lean::RoundContract.counterLoopEscape  reproduces  CounterLoop.lean::RoundContract.counterLoopDone: 1154/1540 = 75%
   Catalog.lean::f2_extract_replay  reproduces  Catalog.lean::f2_extract_replay_finish: 230/307 = 75%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::a2_mapSetup_run: 122/163 = 75%
   Catalog.lean::incrementTM  reproduces  Catalog.lean::clearTM: 305/409 = 75%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::catalog_redirect_loop  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::a2_mapSetup_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::compareTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_run: 286/384 = 74%
   Catalog.lean::f2_counterInc_potential  reproduces  Catalog.lean::f2_counterInc_length: 106/143 = 74%
   Catalog.lean::clearTM  reproduces  Catalog.lean::copyMapTM: 369/498 = 74%
   Catalog.lean::f2_extract_block  reproduces  Catalog.lean::f2_extract_first: 222/300 = 74%
   Catalog.lean::f2_loopCall_heads  reproduces  Catalog.lean::a2_call_heads: 520/703 = 74%
   Simulation.lean::leftCfg_apply  reproduces  Simulation.lean::rightCfg_apply: 142/192 = 74%
   Catalog.lean::incrementTM_run_overflow_ofCfg  reproduces  Catalog.lean::incrementTM_run_succ_ofCfg: 617/839 = 74%
   Basic.lean::segment_iff  reproduces  Basic.lean::round_iff: 75/102 = 74%
   Basic.lean::safeSegment_iff  reproduces  Basic.lean::round_iff: 75/102 = 74%
   Basic.lean::endpoint_not_mem  reproduces  Basic.lean::Cfg.SameOutside.keep_blank: 97/132 = 73%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::Cfg.ofWords_copy_endpoint: 169/230 = 73%
   Catalog.lean::incrementTM_run_overflow  reproduces  Catalog.lean::Cfg.ofWords_copy_endpoint: 169/230 = 73%
   Catalog.lean::f2_loop_find_run  reproduces  Catalog.lean::a2_loop_halted_run: 484/659 = 73%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmit_step  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilent_step: 315/429 = 73%
   Simulation.lean::bufferedSecondCfg_run  reproduces  Catalog.lean::a2_mapVirtual_run: 190/259 = 73%
   Catalog.lean::f2_loopFrame  reproduces  Catalog.lean::f2_loopControlAction: 110/150 = 73%
   Catalog.lean::f2_incFixedTM  reproduces  Catalog.lean::f2_pairDupTM: 283/386 = 73%
   Configuration.lean::moveInputPos_pos_of_ne_right  reproduces  Configuration.lean::moveInputPos_neg_of_ne_left: 85/116 = 73%
   Catalog.lean::a2_fuel_heads  reproduces  Catalog.lean::a2_call_heads: 515/703 = 73%
   CounterLoop.lean::counterLoopTMVia_done_witness  reproduces  CounterLoop.lean::counterLoopTMVia_escape_witness: 738/1008 = 73%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmitTM_visitedByTapeHead_frame: 204/279 = 73%
   RecordTable.lean::rt_copyState_fintype  reproduces  RecordTable.lean::rt_copyState: 76/104 = 73%
   RecordTable.lean::rt_copyState_decidableEq  reproduces  RecordTable.lean::rt_copyState: 76/104 = 73%
   CfgRecord.lean::recordStep_map_snapshot  reproduces  CfgRecord.lean::recordStep_clear_snapshot: 875/1198 = 73%
   Catalog.lean::f2_counterTape_read  reproduces  Catalog.lean::f2_loopBuffer_read: 65/89 = 73%
   Simulation.lean::bufferedFirstCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 235/322 = 73%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Catalog.lean::f2_catalogPoly_emit: 384/527 = 73%
   Basic.lean::ReturnContract  reproduces  Basic.lean::RoundContract: 412/566 = 73%
   Simulation.lean::bufferedFirstCfg_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Catalog.lean::a2_mapSetup_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::f2_loopBody_capture: 270/372 = 73%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_frame: 82/113 = 73%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_spaceUsedByTape_le_max  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_spaceUsedByTape_le_add: 92/127 = 72%
   Catalog.lean::f2_loopBuffer_write  reproduces  Catalog.lean::f2_counterTape_write: 311/432 = 72%
   Simulation.lean::rightAction  reproduces  Simulation.lean::leftAction: 69/96 = 72%
   Simulation.lean::leftAction  reproduces  Simulation.lean::rightAction: 69/96 = 72%
   Catalog.lean::f2_splitRestoreScan  reproduces  Catalog.lean::f2_splitPrepareScan: 74/103 = 72%
   Basic.lean::locate  reproduces  Basic.lean::cut: 219/305 = 72%
   Catalog.lean::f2_splitRestore_append  reproduces  Catalog.lean::f2_splitPrepare_extra: 338/472 = 72%
   CounterLoop.lean::counterLoopTM_run_done  reproduces  CounterLoop.lean::counterLoopTM_run_escape: 393/549 = 72%
   Catalog.lean::f2_splitCount_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left: 120/168 = 71%
   Catalog.lean::a2_loop_halted_run  reproduces  Catalog.lean::f2_loop_find_run: 484/678 = 71%
   Catalog.lean::f2_loopHost_borrow  reproduces  Catalog.lean::f2_loopBorrow_correct: 261/367 = 71%
   Catalog.lean::a2_map_setup  reproduces  Catalog.lean::a2_map_move: 257/362 = 71%
   RecordTable.lean::rt_copyState_decidableEq  reproduces  RecordTable.lean::rt_copyState_fintype: 92/130 = 71%
   Catalog.lean::f2_rawStripTM  reproduces  Catalog.lean::f2_loopReplayTM: 92/130 = 71%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::leftCfg_apply: 133/188 = 71%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmitTM_visitedByTapeHead: 171/242 = 71%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_firstReturn  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_run: 151/214 = 71%
   CounterLoop.lean::decrementTM_run_underflow_ofCfg  reproduces  CounterLoop.lean::counter_complement_twice: 62/88 = 70%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::rightCfg_apply: 135/192 = 70%
   Simulation.lean::rightCfg_run  reproduces  Simulation.lean::leftCfg_run: 71/101 = 70%
   Catalog.lean::Cfg.ofWords_transfer_endpoint  reproduces  Catalog.lean::transferTM_run: 478/680 = 70%
   Catalog.lean::f2_cond_ledger  reproduces  Catalog.lean::f2_timed_start: 754/1073 = 70%
   Catalog.lean::f2_splitRestoreTM  reproduces  Catalog.lean::f2_splitPrepareTM: 280/399 = 70%
   Basic.lean::traj_iff  reproduces  Basic.lean::endpoint_not_mem: 80/114 = 70%
   Basic.lean::Frames.trans  reproduces  Basic.lean::endpoint_not_mem: 80/114 = 70%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_visitedByTapeHead: 188/268 = 70%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::clearTM_run: 270/385 = 70%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 215/307 = 70%
   CfgRecord.lean::recordStep_halt_run  reproduces  CfgRecord.lean::recordStep_reject_run: 383/547 = 70%
   Catalog.lean::a2_heads_halted  reproduces  Catalog.lean::a2_heads_join: 72/103 = 70%
   Catalog.lean::f2_loopBody_step  reproduces  Catalog.lean::f2_loopBody_stop: 245/352 = 70%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   Simulation.lean::bufferedFirstCfg_rewind  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   Catalog.lean::f2_lenParse_block  reproduces  Catalog.lean::f2_lenParse_first: 222/320 = 69%
   Catalog.lean::incrementTM_run_overflow  reproduces  Catalog.lean::copyTM_run: 280/404 = 69%
   Catalog.lean::catalogIncR  reproduces  Catalog.lean::catalogCompareR: 63/91 = 69%
   Catalog.lean::a2_mapVirtual  reproduces  Catalog.lean::a2_mapCfg: 92/133 = 69%
   CfgRecord.lean::recordStep_probe_run  reproduces  CfgRecord.lean::recordStep_read_run: 103/149 = 69%
   Catalog.lean::catalogIncF  reproduces  Catalog.lean::catalogIncR: 152/220 = 69%
   Catalog.lean::copyTM_run_ofCfg  reproduces  Catalog.lean::transferTM_run_ofCfg: 89/129 = 69%
   Simulation.lean::leftCfg_run  reproduces  Simulation.lean::rightCfg_run: 71/103 = 69%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::seekStartTM: 173/251 = 69%
   Catalog.lean::f2_splitEmbed_cut  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr: 93/135 = 69%
   Catalog.lean::f2_splitEmbed_cut  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right: 93/135 = 69%
   Deterministic.lean::ComputesInTimeAndSpace  reproduces  Deterministic.lean::haltsAtStep: 64/93 = 69%
   Catalog.lean::computesFunInTime_incFixed_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 74/108 = 69%
   CfgRecord.lean::recordStep_restore_native  reproduces  CfgRecord.lean::recordStep_empty_run: 370/541 = 68%
   TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::RoundContract.release  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::ReturnContract.release: 774/1135 = 68%
   Catalog.lean::f2_counter_heads  reproduces  Catalog.lean::f2_counter_computes: 666/977 = 68%
   Catalog.lean::f2_counterInc_bits  reproduces  Catalog.lean::f2_loopValue_bits: 96/141 = 68%
   RecordTable.lean::rt_find_scan_phase  reproduces  RecordTable.lean::rt_find_skip_phase: 344/508 = 68%
   CounterLoop.lean::RoundContract.counterLoopDone  reproduces  CounterLoop.lean::RoundContract.counterLoopEscape: 1180/1750 = 67%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::f2_loopHost_halt_return: 342/508 = 67%
   Catalog.lean::computesFunInTime_pairDup_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 74/110 = 67%
   Catalog.lean::catalog_transferMap_trace  reproduces  Catalog.lean::catalog_clear_trace: 1086/1617 = 67%
   Catalog.lean::f2_rawStrip_replay  reproduces  Catalog.lean::f2_extract_replay_finish: 206/307 = 67%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 276/412 = 67%
   Catalog.lean::f2_rawStrip_replay  reproduces  Catalog.lean::f2_extract_replay: 393/587 = 67%
   Catalog.lean::a2_mapVirtual_run  reproduces  Simulation.lean::bufferedSecondCfg_run: 190/284 = 67%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_visitedByTapeHead_frame: 204/305 = 67%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 872/1306 = 67%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::f2_lenParse_run: 1137/1703 = 67%
   Catalog.lean::catalogIncR  reproduces  Catalog.lean::catalogIncF: 152/228 = 67%
   RecordTable.lean::rt_copyState_fintype  reproduces  RecordTable.lean::rt_copyState_decidableEq: 92/138 = 67%
   Catalog.lean::scanResult_fold  reproduces  Catalog.lean::scanResult_map: 92/138 = 67%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::copyTM_run: 269/404 = 67%
   ConfigCount.lean::ComputesInTime.of_spaceUsed_le  reproduces  WindowClock.lean::FinTM.inWindow_of_spaceUsed_le: 336/505 = 67%
   CounterLoop.lean::counterLoopTMVia_escape_segment  reproduces  CounterLoop.lean::counterLoopTMVia_done_segment: 332/499 = 67%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 874/1314 = 67%
   Simulation.lean::timed_rewind  reproduces  Simulation.lean::rewind_heads: 395/594 = 66%
   Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::rewind_heads: 395/594 = 66%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Catalog.lean::f2_scanStep_right: 109/164 = 66%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilent_apply  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmit_apply: 168/253 = 66%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_first: 232/351 = 66%
   Catalog.lean::f2_splitPrepareScan  reproduces  Catalog.lean::f2_splitRestoreScan: 74/112 = 66%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::leftCfg_apply: 124/188 = 66%
   Catalog.lean::f2_incFixedTM  reproduces  Catalog.lean::f2_splitRewindTM: 122/185 = 66%
   StepClock.lean::sc_clockTM  reproduces  CounterLoop.lean::counterLoopTMVia: 205/311 = 66%
   Configuration.lean::moveInputPos_rightBoundary  reproduces  Configuration.lean::moveInputPos_pos_of_ne_right: 71/108 = 66%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::rightCfg_apply: 126/192 = 66%
   CfgRecord.lean::recordStep_halt_run  reproduces  CfgRecord.lean::recordStep_empty_run: 355/541 = 66%
   RecordTable.lean::rt_tailState_decidableEq  reproduces  RecordTable.lean::rt_tailState_fintype: 64/98 = 65%
   Catalog.lean::f2_loopReady_call  reproduces  Catalog.lean::f2_loopCall_frame: 344/527 = 65%
   CfgRecord.lean::recordStep_position_run  reproduces  CfgRecord.lean::recordStep_empty_run: 353/541 = 65%
   Catalog.lean::f2_poly_space  reproduces  Catalog.lean::f2_space_radius: 239/367 = 65%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr  reproduces  Catalog.lean::f2_splitEmbed_run: 122/188 = 65%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right  reproduces  Catalog.lean::f2_splitEmbed_run: 122/188 = 65%
   Simulation.lean::rightCfg  reproduces  Simulation.lean::leftCfg: 84/130 = 65%
   Simulation.lean::leftCfg  reproduces  Simulation.lean::rightCfg: 84/130 = 65%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::seekStartTM: 162/251 = 65%
   Catalog.lean::clearTM  reproduces  Catalog.lean::transferMapTM: 344/533 = 65%
   Catalog.lean::f2_timed_read  reproduces  Catalog.lean::f2_control_heads: 109/169 = 64%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_left  reproduces  Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_rewind: 473/735 = 64%
   CounterLoop.lean::RoundContract.counterLoopDone_traj  reproduces  CounterLoop.lean::RoundContract.counterLoopEscape_traj: 343/533 = 64%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Catalog.lean::f2_catalogPoly_setup: 384/598 = 64%
   Catalog.lean::f2_counter_rewind  reproduces  Catalog.lean::f2_counter_emit_run: 431/672 = 64%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmitTM_visitedByTapeHead  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_visitedByTapeHead: 171/268 = 64%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_firstReturn: 151/237 = 64%
   Catalog.lean::f2_extract_suffix  reproduces  Catalog.lean::f2_scanCopy_suffix: 553/868 = 64%
   Catalog.lean::f2_splitBody_rewind  reproduces  Catalog.lean::f2_splitBody_restore: 333/523 = 64%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 460/725 = 63%
   Catalog.lean::scanResult_map  reproduces  Catalog.lean::scanResult_fold: 92/145 = 63%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_loopReplayTM: 82/130 = 63%
   Catalog.lean::f2_read_heads  reproduces  Catalog.lean::f2_control_heads: 106/169 = 63%
   Catalog.lean::f2_pairDupTM  reproduces  Catalog.lean::f2_splitRewindTM: 116/185 = 63%
   Catalog.lean::incrementTM  reproduces  Catalog.lean::compareTM: 408/651 = 63%
   CounterLoop.lean::counterWord_value  reproduces  CounterLoop.lean::counter_word_decrement: 94/150 = 63%
   Catalog.lean::skipTM  reproduces  Catalog.lean::seekEndTM: 129/206 = 63%
   Catalog.lean::f2_pairDup_double  reproduces  Catalog.lean::f2_scanCopy_run: 311/497 = 63%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 453/725 = 62%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 257/412 = 62%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 191/307 = 62%
   Basic.lean::RoundContract  reproduces  Basic.lean::Contract: 302/487 = 62%
   Catalog.lean::f2_counterInc_length  reproduces  Catalog.lean::f2_counterInc_potential: 106/171 = 62%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_frame: 70/113 = 62%
   Catalog.lean::f2_branch_space  reproduces  StateRenaming.lean::MultiTapeTM.relabelState_spaceUsed: 70/113 = 62%
   Catalog.lean::f2_lenSuffix_run  reproduces  Catalog.lean::f2_anyTrue_run: 512/828 = 62%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_rawStripTM: 285/461 = 62%
   Catalog.lean::f2_loopCall_frame  reproduces  Catalog.lean::f2_loopCall_reframe: 500/809 = 62%
   CounterLoop.lean::RoundContract.counterLoopEscape_traj  reproduces  CounterLoop.lean::RoundContract.counterLoopDone_traj: 343/555 = 62%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 199/322 = 62%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_visitedByTapeHead_frame: 188/305 = 62%
   Deterministic.lean::timed_input_bound  reproduces  Catalog.lean::f2_loop_input_run_le: 224/364 = 62%
   Catalog.lean::f2_loopReplay_step  reproduces  Catalog.lean::f2_loopBorrow_step: 258/421 = 61%
   Simulation.lean::bufferedSecondCfg  reproduces  Catalog.lean::a2_mapVirtual: 123/201 = 61%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmitCfg  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentCfg: 165/270 = 61%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_left: 132/216 = 61%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_left: 132/216 = 61%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Catalog.lean::f2_splitRestore_scan: 526/861 = 61%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 442/725 = 61%
   Catalog.lean::clearTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 299/491 = 61%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::skipBackTM: 123/202 = 61%
   Basic.lean::traj_iff  reproduces  Basic.lean::Cfg.SameOutside.keep_blank: 80/132 = 61%
   Basic.lean::Frames.trans  reproduces  Basic.lean::Cfg.SameOutside.keep_blank: 80/132 = 61%
   Simulation.lean::bufferedSecondCfg  reproduces  Simulation.lean::bufferedScanCfg: 83/137 = 61%
   Catalog.lean::f2_loopFuel_init  reproduces  Simulation.lean::bufferedFirstCfg_init: 195/322 = 61%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_extract_rewind: 464/767 = 60%
   WindowRun.lean::windowRun_spec  reproduces  WindowRun.lean::windowRun_tag: 209/346 = 60%
   RecordTable.lean::rt_tailState_fintype  reproduces  RecordTable.lean::rt_tailState_decidableEq: 64/106 = 60%
   Catalog.lean::f2_splitEmitCfg  reproduces  Catalog.lean::f2_splitPrepareScan: 62/103 = 60%
   RecordTable.lean::rt_find_skip_phase  reproduces  RecordTable.lean::rt_find_scan_phase: 344/572 = 60%
   Catalog.lean::f2_counter_emit_run  reproduces  Catalog.lean::f2_counter_emit: 378/630 = 60%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 464/776 = 60%
   CounterLoop.lean::decrementTM_run_succ_ofCfg  reproduces  CounterLoop.lean::decrementTM_run_underflow_ofCfg: 448/750 = 60%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::seekEndTM: 123/206 = 60%
   Catalog.lean::f2_pairDupTM  reproduces  Catalog.lean::f2_incFixedTM: 283/474 = 60%
   CfgRecord.lean::recordStep_copyback_run  reproduces  CfgRecord.lean::recordStep_clear_heads: 124/208 = 60%
   Catalog.lean::a2_loop_prepare  reproduces  Catalog.lean::f2_loopHost_input_rewind: 146/245 = 60%
   Catalog.lean::f2_lenParse_run  reproduces  Catalog.lean::f2_extract_run: 1137/1908 = 60%
   Catalog.lean::f2_splitBody_restore  reproduces  Catalog.lean::f2_splitBody_rewind: 333/559 = 60%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Catalog.lean::f2_scanCopy_finish: 160/269 = 59%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 258/434 = 59%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 258/434 = 59%
   CfgRecord.lean::recordStep_read_prefix  reproduces  CfgRecord.lean::recordStep_clear_snapshot: 712/1198 = 59%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 454/764 = 59%
   RecordTable.lean::rt_position_run  reproduces  RecordTable.lean::rt_moveWord_run: 954/1606 = 59%
   Catalog.lean::a2_mapVirtual_step  reproduces  Catalog.lean::a2_map_move: 215/362 = 59%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 453/764 = 59%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 460/776 = 59%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_extract_rewind: 454/767 = 59%
   RecordTable.lean::rt_initRestTM  reproduces  RecordTable.lean::rt_tailTM: 113/191 = 59%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_splitPrepare_scan: 394/666 = 59%
   CfgRecord.lean::recordStep_restore_digits  reproduces  CfgRecord.lean::recordStep_clear_heads: 123/208 = 59%
   CfgRecord.lean::recordStep_prepare_native  reproduces  CfgRecord.lean::recordStep_clear_heads: 123/208 = 59%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 772/1306 = 59%
   Catalog.lean::f2_catalogFirstEntry  reproduces  Catalog.lean::f2_splitCount_firstHalt: 198/337 = 59%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 772/1314 = 59%
   Catalog.lean::f2_loopBorrow_correct  reproduces  Catalog.lean::f2_loopHost_borrow: 261/445 = 59%
   Configuration.lean::moveInputPos_rightBoundary  reproduces  Configuration.lean::moveInputPos_neg_of_ne_left: 68/116 = 59%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitCount_over: 82/140 = 59%
   CounterLoop.lean::counter_work_step  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr: 79/135 = 59%
   CounterLoop.lean::counter_work_step  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right: 79/135 = 59%
   Catalog.lean::f2_splitPrepareScan  reproduces  Catalog.lean::f2_splitEmitCfg: 62/106 = 58%
   Catalog.lean::f2_splitPrepareReady  reproduces  Catalog.lean::f2_splitEmitCfg: 62/106 = 58%
   RecordTable.lean::rt_copyState  reproduces  RecordTable.lean::rt_copyState_fintype: 76/130 = 58%
   Catalog.lean::f2_loopBody_capture  reproduces  Catalog.lean::a2_call_run: 184/315 = 58%
   Catalog.lean::f2_pairValid_run  reproduces  Catalog.lean::f2_anyTrue_run: 483/828 = 58%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM: 148/254 = 58%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 240/412 = 58%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_extract_rewind: 446/767 = 58%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 772/1329 = 58%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 772/1329 = 58%
   Catalog.lean::clearTM  reproduces  Catalog.lean::incrementTM: 305/526 = 58%
   TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::ReturnContract.release  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::RoundContract.release: 774/1336 = 58%
   Catalog.lean::computesFunInTime_pairLenCheck_spaceUsed  reproduces  Catalog.lean::computesFunInTime_stripLast_spaceUsed: 298/515 = 58%
   WindowRun.lean::windowRun_spec  reproduces  WindowRun.lean::windowRun_exhausted_of_live: 313/541 = 58%
   CfgRecord.lean::recordStep_copyback_run  reproduces  CfgRecord.lean::recordStep_empty_run: 313/541 = 58%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentRetTM_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_runFrom: 68/118 = 58%
   CfgRecord.lean::recordStep_clear_snapshot  reproduces  CfgRecord.lean::recordStep_map_snapshot: 875/1525 = 57%
   Catalog.lean::f2_catalogPoly_unary_computes  reproduces  Catalog.lean::f2_splitPoly_loop_end: 423/739 = 57%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_copy: 874/1527 = 57%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_splitEmit_separator: 460/804 = 57%
   Basic.lean::time_envelope  reproduces  Basic.lean::time_box: 123/215 = 57%
   Catalog.lean::Cfg.ofWords_copy_endpoint  reproduces  Catalog.lean::clearTM_run: 220/385 = 57%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_copy: 872/1527 = 57%
   Catalog.lean::f2_loop_input_run_le  reproduces  Catalog.lean::f2_loop_output_length_le: 145/254 = 57%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::transferTM_run: 388/680 = 57%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 280/491 = 57%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmitTM_visitedByTapeHead: 138/242 = 57%
   Simulation.lean::runFrom_eq_of_agreeOn  reproduces  ConfigCount.lean::core_runFrom: 62/109 = 57%
   CfgRecord.lean::recordStep_position_run  reproduces  CfgRecord.lean::recordStep_copyback_run: 1173/2070 = 57%
   CfgRecord.lean::RecordEqIndex  reproduces  CfgRecord.lean::RecordTestIndex: 73/129 = 57%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentRetTM_visitedByTapeHead  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmitRetTM_visitedByTapeHead: 65/115 = 57%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_block: 540/956 = 56%
   Catalog.lean::computesFunInTime_prepend_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_pairValid_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_const_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::Cfg.ofWords_copy_endpoint  reproduces  Catalog.lean::copyTM_run: 228/404 = 56%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Simulation.lean::timed_rewind: 245/435 = 56%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Catalog.lean::f2_catalogRewind: 245/435 = 56%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_rawStrip_replay: 232/412 = 56%
   Finite.lean::step_output_prepend  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr: 76/135 = 56%
   Finite.lean::step_output_prepend  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right: 76/135 = 56%
   Catalog.lean::f2_counter_emit  reproduces  Catalog.lean::f2_counter_emit_run: 378/672 = 56%
   Catalog.lean::compareTM  reproduces  Catalog.lean::clearTM: 230/409 = 56%
   Catalog.lean::incrementTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 244/434 = 56%
   Catalog.lean::a2_mapSetup_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 128/228 = 56%
   ConfigCount.lean::ComputesInTime.spaceUsed_le_of_halt  reproduces  ConfigCount.lean::visitedByTapeHead_mono: 64/114 = 56%
   Catalog.lean::f2_splitRestore_first  reproduces  Catalog.lean::f2_splitPrepare_first: 151/269 = 56%
   RecordTable.lean::joinFields_cfgRecord_length  reproduces  RecordTable.lean::cfgRecord_init: 111/198 = 56%
   StateRenaming.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_left: 121/216 = 56%
   Catalog.lean::f2_splitEmbed_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_left: 121/216 = 56%
   RecordTable.lean::rt_richWindow_run  reproduces  RecordTable.lean::rt_moveWord_run: 897/1606 = 56%
   Catalog.lean::a2_heads_join  reproduces  Catalog.lean::a2_heads_halted: 72/129 = 56%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 274/491 = 56%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_frame: 63/113 = 56%
   Catalog.lean::Cfg.ofWords_transfer_endpoint  reproduces  Catalog.lean::copyTM_run: 225/404 = 56%
   CounterLoop.lean::counterLoopTMVia  reproduces  StepClock.lean::sc_clockTM: 205/369 = 56%
   Catalog.lean::computesFunInTime_prepend_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_pairValid_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_const_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::f2_pairValid_run: 679/1231 = 55%
   Catalog.lean::catalog_increment_trace  reproduces  Catalog.lean::step_of_tapeAction_write: 92/167 = 55%
   Catalog.lean::catalog_increment_trace  reproduces  Catalog.lean::step_of_tapeAction_move: 92/167 = 55%
   RecordTable.lean::rt_copyState  reproduces  RecordTable.lean::rt_copyState_decidableEq: 76/138 = 55%
   Catalog.lean::f2_scanCopy_run  reproduces  Catalog.lean::f2_scanCopy_finish: 148/269 = 55%
   Simulation.lean::rewind_from_any  reproduces  Simulation.lean::timed_rewind: 239/435 = 55%
   Simulation.lean::rewind_from_any  reproduces  Catalog.lean::f2_catalogRewind: 239/435 = 55%
   Catalog.lean::a2_call_run  reproduces  Catalog.lean::f2_loopHost_halt_return: 279/508 = 55%
   CfgRecord.lean::RecordTestIndex  reproduces  CfgRecord.lean::RecordEqIndex: 73/133 = 55%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 446/814 = 55%
   Catalog.lean::f2_splitBody_prepare  reproduces  Catalog.lean::f2_splitBody_restore: 285/523 = 54%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::a2_map_parse: 1035/1903 = 54%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 442/814 = 54%
   Catalog.lean::f2_lenParse_run  reproduces  Catalog.lean::f2_pairValid_run: 668/1231 = 54%
   Catalog.lean::computesFunInTime_pairMapSnd_spaceUsed  reproduces  Catalog.lean::a2_heads_halted: 70/129 = 54%
   Catalog.lean::a2_map_parse  reproduces  Catalog.lean::f2_extract_run: 1035/1908 = 54%
   Simulation.lean::bufferTape_append  reproduces  Catalog.lean::f2_catalogBuffer_erase: 64/118 = 54%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_pairDup_double: 656/1212 = 54%
   Catalog.lean::f2_splitCount_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 123/228 = 54%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_fuel_return: 736/1366 = 54%
   Deterministic.lean::haltsAtStep  reproduces  Deterministic.lean::ComputesInTimeAndSpace: 64/119 = 54%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Catalog.lean::a2_mapSetup_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left  reproduces  Simulation.lean::bufferedFirstCfg_run: 122/228 = 54%
   ConfigCount.lean::ComputesInTime.of_spaceUsed_le  reproduces  ConfigCount.lean::visitedByTapeHead_mono: 61/114 = 54%
   Catalog.lean::f2_loopCall_heads  reproduces  Catalog.lean::a2_fuel_heads: 329/615 = 53%
   Simulation.lean::ComputesInTime.spaceUsed_le  reproduces  Catalog.lean::a2_heads_halted: 69/129 = 53%
   Catalog.lean::f2_space_of_time  reproduces  Catalog.lean::a2_heads_halted: 69/129 = 53%
   Catalog.lean::a2_segments  reproduces  Catalog.lean::a2_heads_halted: 69/129 = 53%
   Catalog.lean::f2_splitPrepare_extra  reproduces  Catalog.lean::f2_splitPrepare_scan: 356/666 = 53%
   TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::Traj.seq  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::Frames.seq: 163/305 = 53%
   Basic.lean::Contract  reproduces  Basic.lean::RoundContract: 302/566 = 53%
   Simulation.lean::bufferedScanCfg_run  reproduces  Catalog.lean::f2_splitPrepare_rewind: 414/776 = 53%
   Catalog.lean::f2_splitEmit_suffix  reproduces  Catalog.lean::f2_loopReplay_run: 187/351 = 53%
   Catalog.lean::a2_mapVirtual  reproduces  Simulation.lean::bufferedSecondCfg: 123/232 = 53%
   Catalog.lean::f2_pairValid_computes  reproduces  Catalog.lean::f2_anyTrue_computes: 140/265 = 53%
   Catalog.lean::f2_splitCount_firstHalt  reproduces  Catalog.lean::f2_catalogFirstEntry: 198/375 = 53%
   Deterministic.lean::mem_visitedByTapeHead_iff  reproduces  ConfigCount.lean::visitedByTapeHead_mono: 60/114 = 53%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_visitedByTapeHead: 141/268 = 53%
   Catalog.lean::a2_map_block  reproduces  Catalog.lean::f2_extract_block: 355/675 = 53%
   Catalog.lean::f2_pairDup_computes  reproduces  Catalog.lean::f2_scanStep_right: 86/164 = 52%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_heads  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_timed_control_init  reproduces  Catalog.lean::f2_control_heads: 88/169 = 52%
   RecordTable.lean::rt_tail_run  reproduces  RecordTable.lean::rt_moveWord_run: 836/1606 = 52%
   Catalog.lean::f2_loopReady_call  reproduces  Catalog.lean::f2_loopCall_reframe: 421/809 = 52%
   Catalog.lean::f2_rawStrip_copy  reproduces  Catalog.lean::f2_rawStrip_replay: 214/412 = 52%
   Simulation.lean::bufferedScanCfg  reproduces  Catalog.lean::a2_mapCfg: 69/133 = 52%
   Catalog.lean::f2_poly_step  reproduces  Catalog.lean::a2_mapSetup_step: 113/218 = 52%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 159/307 = 52%
   Catalog.lean::a2_map_move  reproduces  Simulation.lean::leftCfg_apply: 97/188 = 52%
   CfgRecord.lean::recordStep_restore_native  reproduces  CfgRecord.lean::recordStep_reject_run: 282/547 = 52%
   Catalog.lean::Cfg.ofWords_transfer_endpoint  reproduces  Catalog.lean::clearTM_run: 198/385 = 51%
   Catalog.lean::f2_loopFuelCaptured_frame  reproduces  Catalog.lean::f2_loopControl_payload: 128/249 = 51%
   Simulation.lean::timed_rewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   Catalog.lean::exists_loopTM_spaceUsed  reproduces  Catalog.lean::f2_exists_loopFind_space: 939/1831 = 51%
   Catalog.lean::a2_mapVirtual_step  reproduces  Simulation.lean::bufferedSecondCfg_step: 742/1449 = 51%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Catalog.lean::a2_mapVirtual_step: 742/1452 = 51%
   Catalog.lean::f2_loopHost_release  reproduces  Catalog.lean::f2_loopCall_frame: 269/527 = 51%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitPrepare_extra: 240/472 = 51%
   CfgRecord.lean::recordStep_read_fields  reproduces  CfgRecord.lean::recordStep_write_back: 1389/2734 = 51%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 388/764 = 51%
   TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::branch  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::seq: 1194/2353 = 51%
   Catalog.lean::f2_counter_rewind  reproduces  Catalog.lean::catalog_redirect_loop: 71/140 = 51%
   Catalog.lean::a2_map_setup  reproduces  Catalog.lean::f2_loopFuel_init: 214/422 = 51%
   Catalog.lean::a2_map_move  reproduces  Simulation.lean::rightCfg_apply: 97/192 = 51%
   Catalog.lean::skipTM  reproduces  Catalog.lean::skipBackTM: 102/202 = 50%
   Catalog.lean::a2_map_reject  reproduces  Catalog.lean::a2_map_launch: 374/741 = 50%
   Catalog.lean::a2_mapCfg  reproduces  Simulation.lean::bufferedScanCfg: 69/137 = 50%
   Catalog.lean::compareTM_run_stop_ofCfg  reproduces  Catalog.lean::compareTM_run: 193/384 = 50%
   Catalog.lean::f2_loopHost_frame_replay  reproduces  Catalog.lean::f2_loopControl_payload: 125/249 = 50%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::f2_idTM_run: 388/773 = 50%
   Catalog.lean::computesFunInTime_polyUnary_spaceUsed  reproduces  Catalog.lean::f2_unary_sharp: 176/351 = 50%
   Catalog.lean::a2_loop_round  reproduces  Catalog.lean::f2_loopHost_round: 1059/2114 = 50%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_spaceUsedByTape: 319/637 = 50%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_spaceUsedByTape: 319/637 = 50%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 388/776 = 50%
   Catalog.lean::a2_fuel_heads  reproduces  Catalog.lean::f2_loopCall_heads: 329/658 = 50%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_loopDebitTM: 219/438 = 50%
   Catalog.lean::f2_extract_replay_finish  reproduces  Catalog.lean::f2_rawStrip_replay: 206/412 = 50%
   WindowRun.lean::wl_Ctrl_fintype  reproduces  WindowRun.lean::wl_Ctrl_decidableEq: 82/164 = 50%
   Catalog.lean::catalog_transferMap_trace  reproduces  Catalog.lean::catalog_write_take: 62/124 = 50%
```

### Complete after output

```text
declarations screened: 1048; copy pairs (target reproduces >= half of source): 510; reproduced text: 147,693 chars
   Simulation.lean::ComputesInTime.spaceUsed_le  reproduces  Catalog.lean::f2_space_of_time: 713/713 = 100%
   Catalog.lean::f2_space_of_time  reproduces  Simulation.lean::ComputesInTime.spaceUsed_le: 713/713 = 100%
   Simulation.lean::timed_rewind  reproduces  Catalog.lean::f2_catalogRewind: 435/435 = 100%
   Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::timed_rewind: 435/435 = 100%
   Catalog.lean::f2_finSumEquiv  reproduces  Catalog.lean::a2_mapSumEquiv: 362/362 = 100%
   Catalog.lean::a2_mapSumEquiv  reproduces  Catalog.lean::f2_finSumEquiv: 362/362 = 100%
   CfgRecord.lean::recordRun_trans  reproduces  Basic.lean::Turing.Segment.trans: 291/291 = 100%
   Catalog.lean::step_of_tapeAction_write  reproduces  Catalog.lean::step_of_tapeAction_move: 167/167 = 100%
   Catalog.lean::step_of_tapeAction_move  reproduces  Catalog.lean::step_of_tapeAction_write: 167/167 = 100%
   Finite.lean::runFrom_state_ne_none_of_le  reproduces  Catalog.lean::f2_loop_live_prefix: 156/156 = 100%
   Catalog.lean::f2_loop_live_prefix  reproduces  Finite.lean::runFrom_state_ne_none_of_le: 156/156 = 100%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right: 135/135 = 100%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr: 135/135 = 100%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::skipTM: 129/129 = 100%
   ConfigGraph.lean::outSummary_eq_empty_iff  reproduces  ConfigGraph.lean::outSummary_eq_accept_iff: 77/77 = 100%
   ConfigGraph.lean::outSummary_eq_accept_iff  reproduces  ConfigGraph.lean::outSummary_eq_empty_iff: 77/77 = 100%
   CfgRecord.lean::Turing.{k#2  reproduces  CfgRecord.lean::Turing.{k#1: 66/66 = 100%
   CfgRecord.lean::Turing.{k#1  reproduces  CfgRecord.lean::Turing.{k#2: 66/66 = 100%
   TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::branch_positive  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::seq_positive: 62/62 = 100%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 1304/1306 = 100%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Simulation.lean::rewind_from_any: 465/466 = 100%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::Cfg.ofWords_transfer_endpoint: 478/480 = 100%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 1304/1314 = 99%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::Cfg.ofWords_copy_endpoint: 228/230 = 99%
   Basic.lean::Turing.Segment.trans  reproduces  CfgRecord.lean::recordRun_trans: 291/294 = 99%
   Catalog.lean::Cfg.ofWords_transfer_endpoint  reproduces  Catalog.lean::Cfg.ofWords_copy_endpoint: 227/230 = 99%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentRetTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmitRetTM: 215/219 = 98%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::Cfg.ofWords_copy_endpoint: 225/230 = 98%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_left  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr: 132/135 = 98%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_left  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right: 132/135 = 98%
   Catalog.lean::f2_lenSuffix_run  reproduces  Catalog.lean::f2_lenParse_first: 312/320 = 98%
   Configuration.lean::moveInputPos_pos_of_ne_right  reproduces  Configuration.lean::moveInputPos_rightBoundary: 71/73 = 97%
   Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairConcat_spaceUsed: 305/314 = 97%
   Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairConcat_spaceUsed: 305/314 = 97%
   Catalog.lean::f2_scanTrues_run  reproduces  Catalog.lean::f2_scanStep_right: 159/164 = 97%
   Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairSnd_spaceUsed: 305/317 = 96%
   Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairFst_spaceUsed: 305/317 = 96%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::copyTM_run: 388/404 = 96%
   Catalog.lean::transferMapTM  reproduces  Catalog.lean::copyMapTM: 478/498 = 96%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmitRetTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentRetTM: 215/224 = 96%
   Catalog.lean::clearTM_run  reproduces  Catalog.lean::Cfg.ofWords_copy_endpoint: 220/230 = 96%
   Catalog.lean::f2_extract_replay  reproduces  Catalog.lean::f2_rawStrip_replay: 393/412 = 95%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::a2_call_run: 299/315 = 95%
   Catalog.lean::f2_loopCall_reframe  reproduces  Catalog.lean::f2_loopCall_frame: 500/527 = 95%
   Basic.lean::RoundContract  reproduces  Basic.lean::ReturnContract: 412/436 = 94%
   Catalog.lean::f2_incFixed_computes  reproduces  Catalog.lean::f2_scanStep_right: 154/164 = 94%
   Configuration.lean::moveInputPos_neg_of_ne_left  reproduces  Configuration.lean::moveInputPos_rightBoundary: 68/73 = 93%
   Catalog.lean::f2_pairDup_double  reproduces  Catalog.lean::f2_scanStep_right: 152/164 = 93%
   Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairFst_spaceUsed: 293/317 = 92%
   Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairSnd_spaceUsed: 293/317 = 92%
   Catalog.lean::f2_branch_space  reproduces  Catalog.lean::catalog_space_one: 115/125 = 92%
   Catalog.lean::a2_map_block  reproduces  Catalog.lean::a2_map_move: 331/362 = 91%
   CounterLoop.lean::counterLoopTMVia  reproduces  CounterLoop.lean::counterLoopTM: 261/287 = 91%
   Simulation.lean::rewind_heads  reproduces  Simulation.lean::timed_rewind: 395/435 = 91%
   Simulation.lean::rewind_heads  reproduces  Catalog.lean::f2_catalogRewind: 395/435 = 91%
   Simulation.lean::rewind_from_any  reproduces  Catalog.lean::f2_loop_rewind_bounded: 465/514 = 90%
   Catalog.lean::f2_splitEmbed_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr: 122/135 = 90%
   Catalog.lean::f2_splitEmbed_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right: 122/135 = 90%
   Catalog.lean::copyMapTM  reproduces  Catalog.lean::clearTM: 369/409 = 90%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_move: 326/362 = 90%
   Catalog.lean::incrementTM_run_succ_ofCfg  reproduces  Catalog.lean::incrementTM_run_overflow_ofCfg: 617/686 = 90%
   Catalog.lean::copyMapTM  reproduces  Catalog.lean::transferMapTM: 478/533 = 90%
   StateRenaming.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr: 121/135 = 90%
   StateRenaming.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right: 121/135 = 90%
   Catalog.lean::f2_loopHost_halt_return  reproduces  Catalog.lean::a2_call_run: 279/315 = 89%
   Deterministic.lean::step  reproduces  Deterministic.lean::outputSymbol: 76/86 = 88%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::transferTM_spaceUsedByTape: 625/713 = 88%
   Deterministic.lean::outputSymbol  reproduces  Deterministic.lean::step: 76/87 = 87%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::clearTM_run: 336/385 = 87%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 632/725 = 87%
   Catalog.lean::f2_loopHost_borrow_run  reproduces  Catalog.lean::f2_loopBorrow_run: 414/476 = 87%
   Catalog.lean::a2_map_backB  reproduces  Catalog.lean::a2_map_backA: 806/927 = 87%
   Catalog.lean::f2_loopHost_body_capture  reproduces  Catalog.lean::f2_loopHost_fuel_capture: 96/111 = 86%
   CfgRecord.lean::recordStep_reject_run  reproduces  CfgRecord.lean::recordStep_empty_run: 467/541 = 86%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::copyTM_spaceUsedByTape: 625/727 = 86%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentCfg  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmitCfg: 165/192 = 86%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 664/776 = 86%
   CfgRecord.lean::recordStep_empty_run  reproduces  CfgRecord.lean::recordStep_reject_run: 467/547 = 85%
   Basic.lean::Cfg.SameOutside.keep_blank  reproduces  Basic.lean::endpoint_not_mem: 97/114 = 85%
   TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::seq_positive  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::branch_positive: 62/73 = 85%
   Basic.lean::safeSegment_iff  reproduces  Basic.lean::segment_iff: 84/99 = 85%
   Basic.lean::time_box  reproduces  Basic.lean::time_envelope: 123/146 = 84%
   Catalog.lean::transferMapTM  reproduces  Catalog.lean::clearTM: 344/409 = 84%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::seekEndTM: 173/206 = 84%
   CounterLoop.lean::counterLoopTM  reproduces  CounterLoop.lean::counterLoopTMVia: 261/311 = 84%
   Catalog.lean::a2_call_heads  reproduces  Catalog.lean::a2_fuel_heads: 515/615 = 84%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 1092/1306 = 84%
   CounterLoop.lean::counterLoopTM_run_escape  reproduces  CounterLoop.lean::counterLoopTM_run_done: 393/471 = 83%
   Catalog.lean::clearTM_run  reproduces  Catalog.lean::copyTM_run: 336/404 = 83%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 1092/1314 = 83%
   WindowRun.lean::wl_Ctrl_decidableEq  reproduces  WindowRun.lean::wr_Ctrl_decidableEq: 63/76 = 83%
   Catalog.lean::a2_map_backA  reproduces  Catalog.lean::a2_map_backB: 806/975 = 83%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_extract_rewind: 632/767 = 82%
   Catalog.lean::f2_loopHost_fuel_capture  reproduces  Catalog.lean::f2_loopHost_body_capture: 96/117 = 82%
   Basic.lean::hullLo  reproduces  Basic.lean::hullHi: 114/139 = 82%
   Basic.lean::hullHi  reproduces  Basic.lean::hullLo: 114/139 = 82%
   CfgRecord.lean::recordStep_copyback_run  reproduces  CfgRecord.lean::recordStep_reject_run: 448/547 = 82%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 664/814 = 82%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::clearTM_run: 314/385 = 82%
   StateRenaming.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Catalog.lean::f2_splitEmbed_run: 153/188 = 81%
   Catalog.lean::f2_sum_add  reproduces  Catalog.lean::a2_map_sum: 153/188 = 81%
   Catalog.lean::a2_map_sum  reproduces  Catalog.lean::f2_sum_add: 153/188 = 81%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 1077/1329 = 81%
   Simulation.lean::rightCfg_step  reproduces  Simulation.lean::leftCfg_step: 306/378 = 81%
   Catalog.lean::step_of_tapeAction_write  reproduces  Catalog.lean::step_of_inputMoveAction: 68/84 = 81%
   Catalog.lean::step_of_tapeAction_move  reproduces  Catalog.lean::step_of_inputMoveAction: 68/84 = 81%
   Catalog.lean::f2_counter_count_space  reproduces  Catalog.lean::f2_counter_count: 363/452 = 80%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::skipBackTM: 162/202 = 80%
   CounterLoop.lean::counterLoopTMVia_done_segment  reproduces  CounterLoop.lean::counterLoopTMVia_escape_segment: 332/414 = 80%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilent_step  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmit_step: 315/393 = 80%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1092/1366 = 80%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1092/1366 = 80%
   Simulation.lean::leftCfg_step  reproduces  Simulation.lean::rightCfg_step: 306/384 = 80%
   Catalog.lean::f2_extract_suffix  reproduces  Catalog.lean::f2_extract_first: 238/300 = 79%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentRet_step  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentRetTM_visitedByTapeHead: 106/134 = 79%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::skipTM: 102/129 = 79%
   Catalog.lean::a2_call_heads  reproduces  Catalog.lean::f2_loopCall_heads: 520/658 = 79%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitPrepare_scan: 526/666 = 79%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1077/1366 = 79%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::branchTM_computes: 632/802 = 79%
   Catalog.lean::transferTM_run_ofCfg  reproduces  Catalog.lean::copyTM_run_ofCfg: 89/113 = 79%
   Configuration.lean::moveInputPos_neg_of_ne_left  reproduces  Configuration.lean::moveInputPos_pos_of_ne_right: 85/108 = 79%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::a2_mapSetup_run: 128/163 = 79%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::skipTM: 101/129 = 78%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::incrementTM_run_overflow: 383/491 = 78%
   CfgRecord.lean::recordStep_position_run  reproduces  CfgRecord.lean::recordStep_reject_run: 426/547 = 78%
   Catalog.lean::a2_loop_prepare  reproduces  Catalog.lean::f2_loopHost_prepare: 1165/1499 = 78%
   Basic.lean::endpoint_not_mem  reproduces  Basic.lean::traj_iff: 80/103 = 78%
   Basic.lean::Frames.trans  reproduces  Basic.lean::traj_iff: 80/103 = 78%
   Basic.lean::Cfg.SameOutside.keep_blank  reproduces  Basic.lean::traj_iff: 80/103 = 78%
   Catalog.lean::incrementTM_run_overflow  reproduces  Catalog.lean::clearTM_run: 299/385 = 78%
   Catalog.lean::compareTM  reproduces  Catalog.lean::incrementTM: 408/526 = 78%
   Catalog.lean::f2_counterTape_write  reproduces  Catalog.lean::f2_loopBuffer_write: 311/408 = 76%
   Catalog.lean::f2_scanCopy_run  reproduces  Catalog.lean::f2_scanStep_right: 125/164 = 76%
   CounterLoop.lean::counterLoopTMVia_escape_witness  reproduces  CounterLoop.lean::counterLoopTMVia_done_witness: 738/969 = 76%
   CounterLoop.lean::decrementTM_run_succ_ofCfg  reproduces  CounterLoop.lean::counter_complement_twice: 67/88 = 76%
   Catalog.lean::f2_loopBorrow_run  reproduces  Catalog.lean::f2_loopHost_borrow_run: 414/544 = 76%
   ConfigCount.lean::visitedByTapeHead_mono  reproduces  Deterministic.lean::mem_visitedByTapeHead_iff: 60/79 = 76%
   ConfigCount.lean::ComputesInTime.of_spaceUsed_le  reproduces  Deterministic.lean::mem_visitedByTapeHead_iff: 60/79 = 76%
   Basic.lean::round_iff  reproduces  Basic.lean::segment_iff: 75/99 = 76%
   Catalog.lean::f2_loopBorrow_step  reproduces  Catalog.lean::f2_loopReplay_step: 258/341 = 76%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmitRet_step  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmitRetTM_visitedByTapeHead: 87/115 = 76%
   Simulation.lean::rightCfg_apply  reproduces  Simulation.lean::leftCfg_apply: 142/188 = 76%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM: 148/196 = 76%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::a2_mapSetup_run: 123/163 = 75%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Catalog.lean::f2_splitPrepare_extra: 356/472 = 75%
   CounterLoop.lean::RoundContract.counterLoopEscape  reproduces  CounterLoop.lean::RoundContract.counterLoopDone: 1154/1540 = 75%
   Catalog.lean::f2_extract_replay  reproduces  Catalog.lean::f2_extract_replay_finish: 230/307 = 75%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::a2_mapSetup_run: 122/163 = 75%
   Catalog.lean::incrementTM  reproduces  Catalog.lean::clearTM: 305/409 = 75%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::catalog_redirect_loop  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::a2_mapSetup_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::compareTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_run: 286/384 = 74%
   Catalog.lean::f2_counterInc_potential  reproduces  Catalog.lean::f2_counterInc_length: 106/143 = 74%
   Catalog.lean::clearTM  reproduces  Catalog.lean::copyMapTM: 369/498 = 74%
   Catalog.lean::f2_extract_block  reproduces  Catalog.lean::f2_extract_first: 222/300 = 74%
   Catalog.lean::f2_loopCall_heads  reproduces  Catalog.lean::a2_call_heads: 520/703 = 74%
   Simulation.lean::leftCfg_apply  reproduces  Simulation.lean::rightCfg_apply: 142/192 = 74%
   Catalog.lean::incrementTM_run_overflow_ofCfg  reproduces  Catalog.lean::incrementTM_run_succ_ofCfg: 617/839 = 74%
   Basic.lean::segment_iff  reproduces  Basic.lean::round_iff: 75/102 = 74%
   Basic.lean::safeSegment_iff  reproduces  Basic.lean::round_iff: 75/102 = 74%
   Basic.lean::endpoint_not_mem  reproduces  Basic.lean::Cfg.SameOutside.keep_blank: 97/132 = 73%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::Cfg.ofWords_copy_endpoint: 169/230 = 73%
   Catalog.lean::incrementTM_run_overflow  reproduces  Catalog.lean::Cfg.ofWords_copy_endpoint: 169/230 = 73%
   Catalog.lean::f2_loop_find_run  reproduces  Catalog.lean::a2_loop_halted_run: 484/659 = 73%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmit_step  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilent_step: 315/429 = 73%
   Simulation.lean::bufferedSecondCfg_run  reproduces  Catalog.lean::a2_mapVirtual_run: 190/259 = 73%
   Catalog.lean::f2_loopFrame  reproduces  Catalog.lean::f2_loopControlAction: 110/150 = 73%
   Catalog.lean::f2_incFixedTM  reproduces  Catalog.lean::f2_pairDupTM: 283/386 = 73%
   Configuration.lean::moveInputPos_pos_of_ne_right  reproduces  Configuration.lean::moveInputPos_neg_of_ne_left: 85/116 = 73%
   Catalog.lean::a2_fuel_heads  reproduces  Catalog.lean::a2_call_heads: 515/703 = 73%
   CounterLoop.lean::counterLoopTMVia_done_witness  reproduces  CounterLoop.lean::counterLoopTMVia_escape_witness: 738/1008 = 73%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmitTM_visitedByTapeHead_frame: 204/279 = 73%
   RecordTable.lean::rt_copyState_fintype  reproduces  RecordTable.lean::rt_copyState: 76/104 = 73%
   RecordTable.lean::rt_copyState_decidableEq  reproduces  RecordTable.lean::rt_copyState: 76/104 = 73%
   CfgRecord.lean::recordStep_map_snapshot  reproduces  CfgRecord.lean::recordStep_clear_snapshot: 875/1198 = 73%
   Catalog.lean::f2_counterTape_read  reproduces  Catalog.lean::f2_loopBuffer_read: 65/89 = 73%
   Simulation.lean::bufferedFirstCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 235/322 = 73%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Catalog.lean::f2_catalogPoly_emit: 384/527 = 73%
   Basic.lean::ReturnContract  reproduces  Basic.lean::RoundContract: 412/566 = 73%
   Simulation.lean::bufferedFirstCfg_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Catalog.lean::a2_mapSetup_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::f2_loopBody_capture: 270/372 = 73%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_frame: 82/113 = 73%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_spaceUsedByTape_le_max  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_spaceUsedByTape_le_add: 92/127 = 72%
   Catalog.lean::f2_loopBuffer_write  reproduces  Catalog.lean::f2_counterTape_write: 311/432 = 72%
   Simulation.lean::rightAction  reproduces  Simulation.lean::leftAction: 69/96 = 72%
   Simulation.lean::leftAction  reproduces  Simulation.lean::rightAction: 69/96 = 72%
   Catalog.lean::f2_splitRestoreScan  reproduces  Catalog.lean::f2_splitPrepareScan: 74/103 = 72%
   Basic.lean::locate  reproduces  Basic.lean::cut: 219/305 = 72%
   Catalog.lean::f2_splitRestore_append  reproduces  Catalog.lean::f2_splitPrepare_extra: 338/472 = 72%
   CounterLoop.lean::counterLoopTM_run_done  reproduces  CounterLoop.lean::counterLoopTM_run_escape: 393/549 = 72%
   Catalog.lean::f2_splitCount_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left: 120/168 = 71%
   Catalog.lean::a2_loop_halted_run  reproduces  Catalog.lean::f2_loop_find_run: 484/678 = 71%
   Catalog.lean::f2_loopHost_borrow  reproduces  Catalog.lean::f2_loopBorrow_correct: 261/367 = 71%
   Catalog.lean::a2_map_setup  reproduces  Catalog.lean::a2_map_move: 257/362 = 71%
   RecordTable.lean::rt_copyState_decidableEq  reproduces  RecordTable.lean::rt_copyState_fintype: 92/130 = 71%
   Catalog.lean::f2_rawStripTM  reproduces  Catalog.lean::f2_loopReplayTM: 92/130 = 71%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::leftCfg_apply: 133/188 = 71%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmitTM_visitedByTapeHead: 171/242 = 71%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_firstReturn  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_run: 151/214 = 71%
   CounterLoop.lean::decrementTM_run_underflow_ofCfg  reproduces  CounterLoop.lean::counter_complement_twice: 62/88 = 70%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::rightCfg_apply: 135/192 = 70%
   Simulation.lean::rightCfg_run  reproduces  Simulation.lean::leftCfg_run: 71/101 = 70%
   Catalog.lean::Cfg.ofWords_transfer_endpoint  reproduces  Catalog.lean::transferTM_run: 478/680 = 70%
   Catalog.lean::f2_cond_ledger  reproduces  Catalog.lean::f2_timed_start: 754/1073 = 70%
   Catalog.lean::f2_splitRestoreTM  reproduces  Catalog.lean::f2_splitPrepareTM: 280/399 = 70%
   Basic.lean::traj_iff  reproduces  Basic.lean::endpoint_not_mem: 80/114 = 70%
   Basic.lean::Frames.trans  reproduces  Basic.lean::endpoint_not_mem: 80/114 = 70%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_visitedByTapeHead: 188/268 = 70%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::clearTM_run: 270/385 = 70%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 215/307 = 70%
   CfgRecord.lean::recordStep_halt_run  reproduces  CfgRecord.lean::recordStep_reject_run: 383/547 = 70%
   Catalog.lean::a2_heads_halted  reproduces  Catalog.lean::a2_heads_join: 72/103 = 70%
   Catalog.lean::f2_loopBody_step  reproduces  Catalog.lean::f2_loopBody_stop: 245/352 = 70%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   Simulation.lean::bufferedFirstCfg_rewind  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   Catalog.lean::f2_lenParse_block  reproduces  Catalog.lean::f2_lenParse_first: 222/320 = 69%
   Catalog.lean::incrementTM_run_overflow  reproduces  Catalog.lean::copyTM_run: 280/404 = 69%
   Catalog.lean::catalogIncR  reproduces  Catalog.lean::catalogCompareR: 63/91 = 69%
   Catalog.lean::a2_mapVirtual  reproduces  Catalog.lean::a2_mapCfg: 92/133 = 69%
   CfgRecord.lean::recordStep_probe_run  reproduces  CfgRecord.lean::recordStep_read_run: 103/149 = 69%
   Catalog.lean::catalogIncF  reproduces  Catalog.lean::catalogIncR: 152/220 = 69%
   Catalog.lean::copyTM_run_ofCfg  reproduces  Catalog.lean::transferTM_run_ofCfg: 89/129 = 69%
   Simulation.lean::leftCfg_run  reproduces  Simulation.lean::rightCfg_run: 71/103 = 69%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::seekStartTM: 173/251 = 69%
   Catalog.lean::f2_splitEmbed_cut  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr: 93/135 = 69%
   Catalog.lean::f2_splitEmbed_cut  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right: 93/135 = 69%
   Deterministic.lean::ComputesInTimeAndSpace  reproduces  Deterministic.lean::haltsAtStep: 64/93 = 69%
   Catalog.lean::computesFunInTime_incFixed_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 74/108 = 69%
   CfgRecord.lean::recordStep_restore_native  reproduces  CfgRecord.lean::recordStep_empty_run: 370/541 = 68%
   TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::RoundContract.release  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::ReturnContract.release: 774/1135 = 68%
   Catalog.lean::f2_counter_heads  reproduces  Catalog.lean::f2_counter_computes: 666/977 = 68%
   Catalog.lean::f2_counterInc_bits  reproduces  Catalog.lean::f2_loopValue_bits: 96/141 = 68%
   RecordTable.lean::rt_find_scan_phase  reproduces  RecordTable.lean::rt_find_skip_phase: 344/508 = 68%
   CounterLoop.lean::RoundContract.counterLoopDone  reproduces  CounterLoop.lean::RoundContract.counterLoopEscape: 1180/1750 = 67%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::f2_loopHost_halt_return: 342/508 = 67%
   Catalog.lean::computesFunInTime_pairDup_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 74/110 = 67%
   Catalog.lean::catalog_transferMap_trace  reproduces  Catalog.lean::catalog_clear_trace: 1086/1617 = 67%
   Catalog.lean::f2_rawStrip_replay  reproduces  Catalog.lean::f2_extract_replay_finish: 206/307 = 67%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 276/412 = 67%
   Catalog.lean::f2_rawStrip_replay  reproduces  Catalog.lean::f2_extract_replay: 393/587 = 67%
   Catalog.lean::a2_mapVirtual_run  reproduces  Simulation.lean::bufferedSecondCfg_run: 190/284 = 67%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_visitedByTapeHead_frame: 204/305 = 67%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 872/1306 = 67%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::f2_lenParse_run: 1137/1703 = 67%
   Catalog.lean::catalogIncR  reproduces  Catalog.lean::catalogIncF: 152/228 = 67%
   RecordTable.lean::rt_copyState_fintype  reproduces  RecordTable.lean::rt_copyState_decidableEq: 92/138 = 67%
   Catalog.lean::scanResult_fold  reproduces  Catalog.lean::scanResult_map: 92/138 = 67%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::copyTM_run: 269/404 = 67%
   ConfigCount.lean::ComputesInTime.of_spaceUsed_le  reproduces  WindowClock.lean::FinTM.inWindow_of_spaceUsed_le: 336/505 = 67%
   CounterLoop.lean::counterLoopTMVia_escape_segment  reproduces  CounterLoop.lean::counterLoopTMVia_done_segment: 332/499 = 67%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 874/1314 = 67%
   Simulation.lean::timed_rewind  reproduces  Simulation.lean::rewind_heads: 395/594 = 66%
   Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::rewind_heads: 395/594 = 66%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Catalog.lean::f2_scanStep_right: 109/164 = 66%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilent_apply  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmit_apply: 168/253 = 66%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_first: 232/351 = 66%
   Catalog.lean::f2_splitPrepareScan  reproduces  Catalog.lean::f2_splitRestoreScan: 74/112 = 66%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::leftCfg_apply: 124/188 = 66%
   Catalog.lean::f2_incFixedTM  reproduces  Catalog.lean::f2_splitRewindTM: 122/185 = 66%
   StepClock.lean::sc_clockTM  reproduces  CounterLoop.lean::counterLoopTMVia: 205/311 = 66%
   Configuration.lean::moveInputPos_rightBoundary  reproduces  Configuration.lean::moveInputPos_pos_of_ne_right: 71/108 = 66%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::rightCfg_apply: 126/192 = 66%
   CfgRecord.lean::recordStep_halt_run  reproduces  CfgRecord.lean::recordStep_empty_run: 355/541 = 66%
   RecordTable.lean::rt_tailState_decidableEq  reproduces  RecordTable.lean::rt_tailState_fintype: 64/98 = 65%
   Catalog.lean::f2_loopReady_call  reproduces  Catalog.lean::f2_loopCall_frame: 344/527 = 65%
   CfgRecord.lean::recordStep_position_run  reproduces  CfgRecord.lean::recordStep_empty_run: 353/541 = 65%
   Catalog.lean::f2_poly_space  reproduces  Catalog.lean::f2_space_radius: 239/367 = 65%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr  reproduces  Catalog.lean::f2_splitEmbed_run: 122/188 = 65%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right  reproduces  Catalog.lean::f2_splitEmbed_run: 122/188 = 65%
   Simulation.lean::rightCfg  reproduces  Simulation.lean::leftCfg: 84/130 = 65%
   Simulation.lean::leftCfg  reproduces  Simulation.lean::rightCfg: 84/130 = 65%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::seekStartTM: 162/251 = 65%
   Catalog.lean::clearTM  reproduces  Catalog.lean::transferMapTM: 344/533 = 65%
   Catalog.lean::f2_timed_read  reproduces  Catalog.lean::f2_control_heads: 109/169 = 64%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_left  reproduces  Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_rewind: 473/735 = 64%
   CounterLoop.lean::RoundContract.counterLoopDone_traj  reproduces  CounterLoop.lean::RoundContract.counterLoopEscape_traj: 343/533 = 64%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Catalog.lean::f2_catalogPoly_setup: 384/598 = 64%
   Catalog.lean::f2_counter_rewind  reproduces  Catalog.lean::f2_counter_emit_run: 431/672 = 64%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmitTM_visitedByTapeHead  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_visitedByTapeHead: 171/268 = 64%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_firstReturn: 151/237 = 64%
   Catalog.lean::f2_extract_suffix  reproduces  Catalog.lean::f2_scanCopy_suffix: 553/868 = 64%
   Catalog.lean::f2_splitBody_rewind  reproduces  Catalog.lean::f2_splitBody_restore: 333/523 = 64%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 460/725 = 63%
   Catalog.lean::scanResult_map  reproduces  Catalog.lean::scanResult_fold: 92/145 = 63%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_loopReplayTM: 82/130 = 63%
   Catalog.lean::f2_read_heads  reproduces  Catalog.lean::f2_control_heads: 106/169 = 63%
   Catalog.lean::f2_pairDupTM  reproduces  Catalog.lean::f2_splitRewindTM: 116/185 = 63%
   Catalog.lean::incrementTM  reproduces  Catalog.lean::compareTM: 408/651 = 63%
   CounterLoop.lean::counterWord_value  reproduces  CounterLoop.lean::counter_word_decrement: 94/150 = 63%
   Catalog.lean::skipTM  reproduces  Catalog.lean::seekEndTM: 129/206 = 63%
   Catalog.lean::f2_pairDup_double  reproduces  Catalog.lean::f2_scanCopy_run: 311/497 = 63%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 453/725 = 62%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 257/412 = 62%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 191/307 = 62%
   Basic.lean::RoundContract  reproduces  Basic.lean::Contract: 302/487 = 62%
   Catalog.lean::f2_counterInc_length  reproduces  Catalog.lean::f2_counterInc_potential: 106/171 = 62%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_frame: 70/113 = 62%
   Catalog.lean::f2_branch_space  reproduces  StateRenaming.lean::MultiTapeTM.relabelState_spaceUsed: 70/113 = 62%
   Catalog.lean::f2_lenSuffix_run  reproduces  Catalog.lean::f2_anyTrue_run: 512/828 = 62%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_rawStripTM: 285/461 = 62%
   Catalog.lean::f2_loopCall_frame  reproduces  Catalog.lean::f2_loopCall_reframe: 500/809 = 62%
   CounterLoop.lean::RoundContract.counterLoopEscape_traj  reproduces  CounterLoop.lean::RoundContract.counterLoopDone_traj: 343/555 = 62%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 199/322 = 62%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_visitedByTapeHead_frame: 188/305 = 62%
   Deterministic.lean::timed_input_bound  reproduces  Catalog.lean::f2_loop_input_run_le: 224/364 = 62%
   Catalog.lean::f2_loopReplay_step  reproduces  Catalog.lean::f2_loopBorrow_step: 258/421 = 61%
   Simulation.lean::bufferedSecondCfg  reproduces  Catalog.lean::a2_mapVirtual: 123/201 = 61%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmitCfg  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentCfg: 165/270 = 61%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_left: 132/216 = 61%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_left: 132/216 = 61%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Catalog.lean::f2_splitRestore_scan: 526/861 = 61%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 442/725 = 61%
   Catalog.lean::clearTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 299/491 = 61%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::skipBackTM: 123/202 = 61%
   Basic.lean::traj_iff  reproduces  Basic.lean::Cfg.SameOutside.keep_blank: 80/132 = 61%
   Basic.lean::Frames.trans  reproduces  Basic.lean::Cfg.SameOutside.keep_blank: 80/132 = 61%
   Simulation.lean::bufferedSecondCfg  reproduces  Simulation.lean::bufferedScanCfg: 83/137 = 61%
   Catalog.lean::f2_loopFuel_init  reproduces  Simulation.lean::bufferedFirstCfg_init: 195/322 = 61%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_extract_rewind: 464/767 = 60%
   WindowRun.lean::windowRun_spec  reproduces  WindowRun.lean::windowRun_tag: 209/346 = 60%
   RecordTable.lean::rt_tailState_fintype  reproduces  RecordTable.lean::rt_tailState_decidableEq: 64/106 = 60%
   Catalog.lean::f2_splitEmitCfg  reproduces  Catalog.lean::f2_splitPrepareScan: 62/103 = 60%
   RecordTable.lean::rt_find_skip_phase  reproduces  RecordTable.lean::rt_find_scan_phase: 344/572 = 60%
   Catalog.lean::f2_counter_emit_run  reproduces  Catalog.lean::f2_counter_emit: 378/630 = 60%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 464/776 = 60%
   CounterLoop.lean::decrementTM_run_succ_ofCfg  reproduces  CounterLoop.lean::decrementTM_run_underflow_ofCfg: 448/750 = 60%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::seekEndTM: 123/206 = 60%
   Catalog.lean::f2_pairDupTM  reproduces  Catalog.lean::f2_incFixedTM: 283/474 = 60%
   CfgRecord.lean::recordStep_copyback_run  reproduces  CfgRecord.lean::recordStep_clear_heads: 124/208 = 60%
   Catalog.lean::a2_loop_prepare  reproduces  Catalog.lean::f2_loopHost_input_rewind: 146/245 = 60%
   Catalog.lean::f2_lenParse_run  reproduces  Catalog.lean::f2_extract_run: 1137/1908 = 60%
   Catalog.lean::f2_splitBody_restore  reproduces  Catalog.lean::f2_splitBody_rewind: 333/559 = 60%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Catalog.lean::f2_scanCopy_finish: 160/269 = 59%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 258/434 = 59%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 258/434 = 59%
   CfgRecord.lean::recordStep_read_prefix  reproduces  CfgRecord.lean::recordStep_clear_snapshot: 712/1198 = 59%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 454/764 = 59%
   RecordTable.lean::rt_position_run  reproduces  RecordTable.lean::rt_moveWord_run: 954/1606 = 59%
   Catalog.lean::a2_mapVirtual_step  reproduces  Catalog.lean::a2_map_move: 215/362 = 59%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 453/764 = 59%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 460/776 = 59%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_extract_rewind: 454/767 = 59%
   RecordTable.lean::rt_initRestTM  reproduces  RecordTable.lean::rt_tailTM: 113/191 = 59%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_splitPrepare_scan: 394/666 = 59%
   CfgRecord.lean::recordStep_restore_digits  reproduces  CfgRecord.lean::recordStep_clear_heads: 123/208 = 59%
   CfgRecord.lean::recordStep_prepare_native  reproduces  CfgRecord.lean::recordStep_clear_heads: 123/208 = 59%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 772/1306 = 59%
   Catalog.lean::f2_catalogFirstEntry  reproduces  Catalog.lean::f2_splitCount_firstHalt: 198/337 = 59%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 772/1314 = 59%
   Catalog.lean::f2_loopBorrow_correct  reproduces  Catalog.lean::f2_loopHost_borrow: 261/445 = 59%
   Configuration.lean::moveInputPos_rightBoundary  reproduces  Configuration.lean::moveInputPos_neg_of_ne_left: 68/116 = 59%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitCount_over: 82/140 = 59%
   CounterLoop.lean::counter_work_step  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr: 79/135 = 59%
   CounterLoop.lean::counter_work_step  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right: 79/135 = 59%
   Catalog.lean::f2_splitPrepareScan  reproduces  Catalog.lean::f2_splitEmitCfg: 62/106 = 58%
   Catalog.lean::f2_splitPrepareReady  reproduces  Catalog.lean::f2_splitEmitCfg: 62/106 = 58%
   RecordTable.lean::rt_copyState  reproduces  RecordTable.lean::rt_copyState_fintype: 76/130 = 58%
   Catalog.lean::f2_loopBody_capture  reproduces  Catalog.lean::a2_call_run: 184/315 = 58%
   Catalog.lean::f2_pairValid_run  reproduces  Catalog.lean::f2_anyTrue_run: 483/828 = 58%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM: 148/254 = 58%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 240/412 = 58%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_extract_rewind: 446/767 = 58%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 772/1329 = 58%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 772/1329 = 58%
   Catalog.lean::clearTM  reproduces  Catalog.lean::incrementTM: 305/526 = 58%
   TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::ReturnContract.release  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::RoundContract.release: 774/1336 = 58%
   Catalog.lean::computesFunInTime_pairLenCheck_spaceUsed  reproduces  Catalog.lean::computesFunInTime_stripLast_spaceUsed: 298/515 = 58%
   WindowRun.lean::windowRun_spec  reproduces  WindowRun.lean::windowRun_exhausted_of_live: 313/541 = 58%
   CfgRecord.lean::recordStep_copyback_run  reproduces  CfgRecord.lean::recordStep_empty_run: 313/541 = 58%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentRetTM_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_runFrom: 68/118 = 58%
   CfgRecord.lean::recordStep_clear_snapshot  reproduces  CfgRecord.lean::recordStep_map_snapshot: 875/1525 = 57%
   Catalog.lean::f2_catalogPoly_unary_computes  reproduces  Catalog.lean::f2_splitPoly_loop_end: 423/739 = 57%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_copy: 874/1527 = 57%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_splitEmit_separator: 460/804 = 57%
   Basic.lean::time_envelope  reproduces  Basic.lean::time_box: 123/215 = 57%
   Catalog.lean::Cfg.ofWords_copy_endpoint  reproduces  Catalog.lean::clearTM_run: 220/385 = 57%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_copy: 872/1527 = 57%
   Catalog.lean::f2_loop_input_run_le  reproduces  Catalog.lean::f2_loop_output_length_le: 145/254 = 57%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::transferTM_run: 388/680 = 57%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 280/491 = 57%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmitTM_visitedByTapeHead: 138/242 = 57%
   Simulation.lean::runFrom_eq_of_agreeOn  reproduces  ConfigCount.lean::core_runFrom: 62/109 = 57%
   CfgRecord.lean::recordStep_position_run  reproduces  CfgRecord.lean::recordStep_copyback_run: 1173/2070 = 57%
   CfgRecord.lean::RecordEqIndex  reproduces  CfgRecord.lean::RecordTestIndex: 73/129 = 57%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentRetTM_visitedByTapeHead  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmitRetTM_visitedByTapeHead: 65/115 = 57%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_block: 540/956 = 56%
   Catalog.lean::computesFunInTime_prepend_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_pairValid_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_const_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::Cfg.ofWords_copy_endpoint  reproduces  Catalog.lean::copyTM_run: 228/404 = 56%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Simulation.lean::timed_rewind: 245/435 = 56%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Catalog.lean::f2_catalogRewind: 245/435 = 56%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_rawStrip_replay: 232/412 = 56%
   Finite.lean::step_output_prepend  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr: 76/135 = 56%
   Finite.lean::step_output_prepend  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right: 76/135 = 56%
   Catalog.lean::f2_counter_emit  reproduces  Catalog.lean::f2_counter_emit_run: 378/672 = 56%
   Catalog.lean::compareTM  reproduces  Catalog.lean::clearTM: 230/409 = 56%
   Catalog.lean::incrementTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 244/434 = 56%
   Catalog.lean::a2_mapSetup_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 128/228 = 56%
   ConfigCount.lean::ComputesInTime.spaceUsed_le_of_halt  reproduces  ConfigCount.lean::visitedByTapeHead_mono: 64/114 = 56%
   Catalog.lean::f2_splitRestore_first  reproduces  Catalog.lean::f2_splitPrepare_first: 151/269 = 56%
   RecordTable.lean::joinFields_cfgRecord_length  reproduces  RecordTable.lean::cfgRecord_init: 111/198 = 56%
   StateRenaming.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_left: 121/216 = 56%
   Catalog.lean::f2_splitEmbed_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_left: 121/216 = 56%
   RecordTable.lean::rt_richWindow_run  reproduces  RecordTable.lean::rt_moveWord_run: 897/1606 = 56%
   Catalog.lean::a2_heads_join  reproduces  Catalog.lean::a2_heads_halted: 72/129 = 56%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 274/491 = 56%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_frame: 63/113 = 56%
   Catalog.lean::Cfg.ofWords_transfer_endpoint  reproduces  Catalog.lean::copyTM_run: 225/404 = 56%
   CounterLoop.lean::counterLoopTMVia  reproduces  StepClock.lean::sc_clockTM: 205/369 = 56%
   Catalog.lean::computesFunInTime_prepend_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_pairValid_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_const_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::f2_pairValid_run: 679/1231 = 55%
   Catalog.lean::catalog_increment_trace  reproduces  Catalog.lean::step_of_tapeAction_write: 92/167 = 55%
   Catalog.lean::catalog_increment_trace  reproduces  Catalog.lean::step_of_tapeAction_move: 92/167 = 55%
   RecordTable.lean::rt_copyState  reproduces  RecordTable.lean::rt_copyState_decidableEq: 76/138 = 55%
   Catalog.lean::f2_scanCopy_run  reproduces  Catalog.lean::f2_scanCopy_finish: 148/269 = 55%
   Simulation.lean::rewind_from_any  reproduces  Simulation.lean::timed_rewind: 239/435 = 55%
   Simulation.lean::rewind_from_any  reproduces  Catalog.lean::f2_catalogRewind: 239/435 = 55%
   Catalog.lean::a2_call_run  reproduces  Catalog.lean::f2_loopHost_halt_return: 279/508 = 55%
   CfgRecord.lean::RecordTestIndex  reproduces  CfgRecord.lean::RecordEqIndex: 73/133 = 55%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 446/814 = 55%
   Catalog.lean::f2_splitBody_prepare  reproduces  Catalog.lean::f2_splitBody_restore: 285/523 = 54%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::a2_map_parse: 1035/1903 = 54%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 442/814 = 54%
   Catalog.lean::f2_lenParse_run  reproduces  Catalog.lean::f2_pairValid_run: 668/1231 = 54%
   Catalog.lean::computesFunInTime_pairMapSnd_spaceUsed  reproduces  Catalog.lean::a2_heads_halted: 70/129 = 54%
   Catalog.lean::a2_map_parse  reproduces  Catalog.lean::f2_extract_run: 1035/1908 = 54%
   Simulation.lean::bufferTape_append  reproduces  Catalog.lean::f2_catalogBuffer_erase: 64/118 = 54%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_pairDup_double: 656/1212 = 54%
   Catalog.lean::f2_splitCount_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 123/228 = 54%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_fuel_return: 736/1366 = 54%
   Deterministic.lean::haltsAtStep  reproduces  Deterministic.lean::ComputesInTimeAndSpace: 64/119 = 54%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Catalog.lean::a2_mapSetup_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left  reproduces  Simulation.lean::bufferedFirstCfg_run: 122/228 = 54%
   ConfigCount.lean::ComputesInTime.of_spaceUsed_le  reproduces  ConfigCount.lean::visitedByTapeHead_mono: 61/114 = 54%
   Catalog.lean::f2_loopCall_heads  reproduces  Catalog.lean::a2_fuel_heads: 329/615 = 53%
   Simulation.lean::ComputesInTime.spaceUsed_le  reproduces  Catalog.lean::a2_heads_halted: 69/129 = 53%
   Catalog.lean::f2_space_of_time  reproduces  Catalog.lean::a2_heads_halted: 69/129 = 53%
   Catalog.lean::a2_segments  reproduces  Catalog.lean::a2_heads_halted: 69/129 = 53%
   Catalog.lean::f2_splitPrepare_extra  reproduces  Catalog.lean::f2_splitPrepare_scan: 356/666 = 53%
   TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::Traj.seq  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::Frames.seq: 163/305 = 53%
   Basic.lean::Contract  reproduces  Basic.lean::RoundContract: 302/566 = 53%
   Simulation.lean::bufferedScanCfg_run  reproduces  Catalog.lean::f2_splitPrepare_rewind: 414/776 = 53%
   Catalog.lean::f2_splitEmit_suffix  reproduces  Catalog.lean::f2_loopReplay_run: 187/351 = 53%
   Catalog.lean::a2_mapVirtual  reproduces  Simulation.lean::bufferedSecondCfg: 123/232 = 53%
   Catalog.lean::f2_pairValid_computes  reproduces  Catalog.lean::f2_anyTrue_computes: 140/265 = 53%
   Catalog.lean::f2_splitCount_firstHalt  reproduces  Catalog.lean::f2_catalogFirstEntry: 198/375 = 53%
   Deterministic.lean::mem_visitedByTapeHead_iff  reproduces  ConfigCount.lean::visitedByTapeHead_mono: 60/114 = 53%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_visitedByTapeHead: 141/268 = 53%
   Catalog.lean::a2_map_block  reproduces  Catalog.lean::f2_extract_block: 355/675 = 53%
   Catalog.lean::f2_pairDup_computes  reproduces  Catalog.lean::f2_scanStep_right: 86/164 = 52%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_heads  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_timed_control_init  reproduces  Catalog.lean::f2_control_heads: 88/169 = 52%
   RecordTable.lean::rt_tail_run  reproduces  RecordTable.lean::rt_moveWord_run: 836/1606 = 52%
   Catalog.lean::f2_loopReady_call  reproduces  Catalog.lean::f2_loopCall_reframe: 421/809 = 52%
   Catalog.lean::f2_rawStrip_copy  reproduces  Catalog.lean::f2_rawStrip_replay: 214/412 = 52%
   Simulation.lean::bufferedScanCfg  reproduces  Catalog.lean::a2_mapCfg: 69/133 = 52%
   Catalog.lean::f2_poly_step  reproduces  Catalog.lean::a2_mapSetup_step: 113/218 = 52%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 159/307 = 52%
   Catalog.lean::a2_map_move  reproduces  Simulation.lean::leftCfg_apply: 97/188 = 52%
   CfgRecord.lean::recordStep_restore_native  reproduces  CfgRecord.lean::recordStep_reject_run: 282/547 = 52%
   Catalog.lean::Cfg.ofWords_transfer_endpoint  reproduces  Catalog.lean::clearTM_run: 198/385 = 51%
   Catalog.lean::f2_loopFuelCaptured_frame  reproduces  Catalog.lean::f2_loopControl_payload: 128/249 = 51%
   Simulation.lean::timed_rewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   Catalog.lean::exists_loopTM_spaceUsed  reproduces  Catalog.lean::f2_exists_loopFind_space: 939/1831 = 51%
   Catalog.lean::a2_mapVirtual_step  reproduces  Simulation.lean::bufferedSecondCfg_step: 742/1449 = 51%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Catalog.lean::a2_mapVirtual_step: 742/1452 = 51%
   Catalog.lean::f2_loopHost_release  reproduces  Catalog.lean::f2_loopCall_frame: 269/527 = 51%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitPrepare_extra: 240/472 = 51%
   CfgRecord.lean::recordStep_read_fields  reproduces  CfgRecord.lean::recordStep_write_back: 1389/2734 = 51%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 388/764 = 51%
   TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::branch  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::seq: 1194/2353 = 51%
   Catalog.lean::f2_counter_rewind  reproduces  Catalog.lean::catalog_redirect_loop: 71/140 = 51%
   Catalog.lean::a2_map_setup  reproduces  Catalog.lean::f2_loopFuel_init: 214/422 = 51%
   Catalog.lean::a2_map_move  reproduces  Simulation.lean::rightCfg_apply: 97/192 = 51%
   Catalog.lean::skipTM  reproduces  Catalog.lean::skipBackTM: 102/202 = 50%
   Catalog.lean::a2_map_reject  reproduces  Catalog.lean::a2_map_launch: 374/741 = 50%
   Catalog.lean::a2_mapCfg  reproduces  Simulation.lean::bufferedScanCfg: 69/137 = 50%
   Catalog.lean::compareTM_run_stop_ofCfg  reproduces  Catalog.lean::compareTM_run: 193/384 = 50%
   Catalog.lean::f2_loopHost_frame_replay  reproduces  Catalog.lean::f2_loopControl_payload: 125/249 = 50%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::f2_idTM_run: 388/773 = 50%
   Catalog.lean::computesFunInTime_polyUnary_spaceUsed  reproduces  Catalog.lean::f2_unary_sharp: 176/351 = 50%
   Catalog.lean::a2_loop_round  reproduces  Catalog.lean::f2_loopHost_round: 1059/2114 = 50%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_spaceUsedByTape: 319/637 = 50%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_spaceUsedByTape: 319/637 = 50%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 388/776 = 50%
   Catalog.lean::a2_fuel_heads  reproduces  Catalog.lean::f2_loopCall_heads: 329/658 = 50%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_loopDebitTM: 219/438 = 50%
   Catalog.lean::f2_extract_replay_finish  reproduces  Catalog.lean::f2_rawStrip_replay: 206/412 = 50%
   WindowRun.lean::wl_Ctrl_fintype  reproduces  WindowRun.lean::wl_Ctrl_decidableEq: 82/164 = 50%
   Catalog.lean::catalog_transferMap_trace  reproduces  Catalog.lean::catalog_write_take: 62/124 = 50%
```

## Delivery inventory

The archive contains this report, full modified source, a single-commit format-patch
series, a bundle whose sole prerequisite is the base, bootstrap/final/axiom logs, both
screen outputs, the authorized C shim source, and `SHA256SUMS`. No compiled shim, olean,
toolchain, or other build product is included. The checksum file covers every other file.

Local delivery commit: `c887ee8988303af928793efba941c753b233114b`.

## Notation glossary

| Symbol | Meaning |
|---|---|
| `M`, `upd` | Fixed simulated machine and tag update. |
| `k`, `q` | Work-tape count and state cardinality. |
| `n`, `s`, `p` | Input length, radius, and position width. |
| `L`, `F` | Record length and field-cell total. |
| `B`, `N` | Configuration bound and certified rounds. |
| `C`, `c`, `W` | F2 coefficient, pass count, and clock width. |
| `A`, `D` | Uninstantiated writer and dispatch cost constants. |
| `Γ`, `e`, `m`, `fs` | Alphabet, constant symbol, field count, and field layout. |
| `o`, `a`, `b`, `z` | Origin, adjacent widths, and cell position. |
| `d`, `τ`, `w` | Configuration, tag, and word. |
