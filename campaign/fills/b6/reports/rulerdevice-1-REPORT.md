# B6 F5 ruler-device fill — recovery delivery


**Partial delivery: phase 1 reached, 1/3 targets proved.** The boundary test is reconstructed
and checked. The device call rows and ruler host remain open. Escalations E1 and E2 below
disclose the recovery import-placement error and the cache downloader's internal Lake command.
This is not the lost three-target implementation and is not presented as fully rule-compliant.

This report describes only the source and evidence shipped in this ZIP. A workspace reset
removed the previous checkout, all completed proof source, raw verification logs, and packaging
scripts before a ZIP was created. The retained conversation summary recorded all three targets
as proved and an unfinished final sweep at module 16/80. Those lost artifacts are not evidence
for this delivery, and no proof-completion claim here relies on them.

The resumed work recovered the original two attachments, cloned the campaign branch again,
and reconstructed a checked prefix. No claim is made that the recovered source is identical
to the lost source. No ZIP from the earlier work existed to resend.

## Pin and attachment integrity

Base: `94b986d4db7167ab2a8b20d38d4385f11e60be0e`.
The resumed clone checked out `complexity/arora-barak-ch3-4`, observed tip
`df2ef06273c2d3e6de9a4748fc1d12a8298ccf31`, and ran
`git merge-base --is-ancestor 94b986d4db7167ab2a8b20d38d4385f11e60be0e HEAD`
successfully before creating `fill/b6-rulerdevice` at exactly the base.

The recovered attachment hashes were verified:

- `b6-fill-rulerdevice.md`:
  `e181d7e2ae845b965f6b0b977d098b81ed1092f1678414c03d4173f4305a49b4`.
- `fill-environment-addendum(8).md`:
  `a25474c52b6b8e8bc1295fad48278b3356b8fed482d2e49c5874554f6d8d2928`.

The repository brief, after replacing `@ANCESTOR@` with the base, matches the attachment
byte-for-byte. The addendum at the pinned base matches the attachment byte-for-byte.
No merge, rebase, cherry-pick, push, or PR was performed.

## Imports and ownership

The first edit in the original run was recorded as the two authorized imports after original
line 7. That original working copy and its raw first-edit record were lost. During recovery,
the first source edit again added exactly these two imports, but accidentally placed them
after original line 6. This placement mistake was corrected immediately, before any Lean
check or helper insertion, to the authorized position after original line 7. This transient
recovery ordering error is disclosed as escalation E1; this report does not claim a perfect
first-edit sequence for the recovery run. The delivered diff has exactly the authorized
two imports in region (a), with the original imports in their original order.

All delivered proof helpers are private and begin `rd_`. Only the authorized first helper
home, target 1's body, and the three flagged Fill appendices are changed. Reverse reconstruction
of these edits yields the base source byte-for-byte: statements, module header, existing proved
material, and all other files remain frozen. Scratch attempts are not shipped.

## Environment

The unmodified official Lean 4.25.0 executable failed with:

```
error: failed to locate application
```

The attached environment addendum was followed: its exact `executable-path.c` was compiled
and preloaded only for Lean/Lake/checker processes. Its SHA-256 is
`985924ad83d39e108c0a2107bab07e65cdeb88641453508ab5acda115534fba7`.
The source is shipped as `evidence/runtime/executable-path.c`; the compiled `.so` and all
build products are excluded. The shim restored the pinned version:

```
Lean (version 4.25.0, x86_64-unknown-linux-gnu, commit cdd38ac5115bdeec5f609e9126cce00f51ae88b3, Release)
```

Exact scoped variables:

```sh
PATH=/workspace/scratch/177f06803258/runtime/lean-4.25.0-linux/bin:$PATH
LEAN_SYSROOT=/workspace/scratch/177f06803258/runtime/lean-4.25.0-linux
LAKE_HOME=/workspace/scratch/177f06803258/runtime/lean-4.25.0-linux
LD_PRELOAD=/workspace/scratch/177f06803258/runtime/executable-path.so
```

The official release was extracted with `TAR_OPTIONS=--no-same-owner`. Dependency restoration
used the pinned manifest and `lake exe cache get` for the 35 direct Mathlib imports of the
order list, restoring their 967-module closure. The first cache attempt failed fetching the
ProofWidgets release; repeating the authorized cache command with
`TAR_OPTIONS=--no-same-owner` succeeded. No toolchain or dependency source was patched.

No direct `lake build` command was issued. For precise provenance, the stock pinned cache
program itself invokes Lake's `build proofwidgets:release` / `build --no-build` internally
while fetching/validating that release. The stock cache code was inspected after the first
failure, before retrying the authorized cache command with the tar option. This sequence is
disclosed as escalation E2 rather than hidden behind a blanket claim that no
subprocess ever used that command. All actual proof checks used only
`scripts/lean_check_tree.sh`, including scratch probes and axiom/import probes.

The shared host was close to its 8 GiB memory limit during reconstruction. No shared cache
was relocated, no other process was stopped, no permissions or kernel settings were changed,
and no sandbox escalation was requested.


Delivery commit: `f9810ddf411ebb40b07e287398787d0db4e160f6` (sole parent is the exact base).

## Target status and continuation

| Target | Delivered status | Constant / continuation |
|---|---|---|
| `Turing.exists_rulerTestTM` | Proved, phase 1 | `C = 2`; exact time `2 * ℓ + 2` |
| `Turing.exists_rulerDeviceTM` | Open | No delivered witness or constant |
| `Turing.exists_rulerHostTM` | Open | No delivered witness, constant, or cost function |

`Turing.exists_rulerDeviceTM` — **Proof sketch.** Compose the restoring test with a one-step
read or clamped-move leaf using `phaseHostTM_run`; use the same phase argument for both modes.
Read returns blank on the left-boundary verdict and the physical input symbol otherwise,
using `inputCell_of_drop`. Suppress an outward left move; at the right blank use the native
clamp. A prospective exact total `2 * ℓ + 5` fits `C = 4` for positive `ℓ`; these are planning
figures, not a delivered proof.

`Turing.exists_rulerHostTM` — **Proof sketch.** Encode the source by `rulerHostCfg` with the
canonical boundary tag. Perform one source transition, preserving its emission and its bank.
Only a nonhalting left move from a cleared tag starts an R1-embedded restoring test on the last
tape. The intended cost is `1` otherwise and `2 * ℓ + 3` for that pause case, bounded by
`3 * (ℓ + 1)`. Use `Lockstep.runFrom`, `.cut`, and `.locate` for the iteration and frames,
then `mem_visitedByTapeHead_iff` for the space ledger. In particular, a halting left move has
no pause. No second iteration or embedding transport should be written. These costs and the
candidate `C = 3` remain an outline, not a delivered witness.

The partial stops after reconstruction of phase 1 following loss of the original working
source and evidence. No mathematical unprovability or missing public API lemma is claimed.
There are no open helper declarations and no new admissions; only the two named targets remain
open. Their original proof sketches and the flagged continuation appendices are retained.

The boundary test covers `ℓ = 1`, empty physical/payload cases allowed by its hypotheses,
and a physical head at the right blank without extra hypotheses. The later gate cases remain
obligations for the two open targets; they are not claimed checked by an absent implementation.

## New private declarations

| Declaration | Role |
|---|---|
| `rd_State` | Finite forward, return and verdict control |
| `rd_move` | Silent joint input/work-head action |
| `rd_move_apply` | One equation for that action's complete frame |
| `rd_test` | Boundary-test leaf controller |
| `rd_cfg` | Configuration at a trace offset |
| `rd_verdict` | Boolean physical-head/header equality |
| `rd_trace` | One finite forward/return trajectory |
| `rd_read_nat` | Interior unary-ruler readings via public buffer lemmas |
| `rd_cfg_step` | Shared action equation between two trace points |
| `rd_trace_step` | The four trajectory cases, including both delimiters |
| `rd_run` | The sole trajectory induction |

The leaf is necessary because the catalog moves work heads or the input head separately;
the required joint input-left/ruler-right step is not a catalog row. The call-row and host
controllers are not inserted in this partial. Every inserted helper was checked before it
was installed in the owned file. All three authorized Fill appendices are present.

**Promotion candidates:** the joint-move leaf and its frame equation. A generic host-step
plus pause lemma remains a candidate for a later phase; no such lemma is delivered here.

**Escalations:** E1 and E2 are disclosed above; workspace loss is the recovery obstruction.
No missing-lemma or false-statement escalation is claimed. Neither exceptional sequence is
silently treated as a waived rule. The final import placement is repaired, and no further cache
command was used after dependency restoration.

## Ownership and citation checks

```
PASS: reverse reconstruction equals the pinned base byte-for-byte.
PASS: exact two imports after original line 7; helpers only at home 202; target 1 body only.
PASS: three authorized flagged appendices; all other source and all statements frozen.
PASS: every new line <=100 characters; no new admission in reconstructed helpers.
Final lines: 557
New private declarations: 11
PASS: exact six R3 row-name grep has no match.
Other-file private-name lexical matches: {'S': ['TCSlib/Complexity/CircuitComplexity/CircuitSatReductionValid.lean']}
RESOLVED: S is the locally bound state type in rd_move/rd_move_apply, not a citation.
PASS: one owned source path, rd_ private prefix, no helper admissions.
PASS: every actually added diff line is at most 100 characters.
```

The added-source grep finds none of `copyTM_run`, `transferTM_run`, `clearTM_run`,
`compareTM_run`, `incrementTM_run_succ`, or `incrementTM_run_overflow`. Other-file private-name
tokens were checked, and the compiled dependency walk independently rejects any direct
external private reference. Only public declarations at the pinned base are used. The
unchanged existing proofs are not rewritten or re-proved.

The original 58-check import probe is retained byte-for-byte as a prefix of the expanded
probe. Every additional external constant in the compiled own-declaration walk and resolvable
source citations is included. Fully qualified names prevent ambiguous short-name resolution.
If the generated proof uses the deprecated aliases `Int.ofNat_mul` or `Int.ofNat_nonneg`,
their exact public names are looked up by `Lean.getConstInfo` and their types printed, avoiding
deprecated-syntax warnings without disabling any linter. All other extra names use `#check`.

External citation inventory (368 names, including implicit kernel dependencies):

```text
AddCommGroup
AddCommGroup.toAddCommMonoid
AddCommGroup.toAddGroup
AddCommGroup.toDivisionAddCommMonoid
AddGroup.toSubNegMonoid
AddGroup.toSubtractionMonoid
AddGroupWithOne.toAddMonoidWithOne
AddMonoid.toAddZeroClass
AddMonoidWithOne.toAddMonoid
AddMonoidWithOne.toNatCast
AddMonoidWithOne.toOne
AddSemigroup.toAdd
AddZero.toAdd
AddZero.toZero
AddZeroClass.toAddZero
And
And.intro
And.left
And.right
Bool
Bool.casesOn
Bool.eq_iff_iff
Bool.false
Bool.false_ne_true
Bool.fintype
Bool.true
Classical.propDecidable
CommRing.toNonUnitalCommRing
Decidable
Decidable.byContradiction
Decidable.decide
Decidable.decide.congr_simp
DecidableEq
DistribLattice.toLattice
Eq
Eq.casesOn
Eq.mpr
Eq.mpr_not
Eq.ndrec
Eq.refl
Eq.symm
Eq.trans
Exists
Exists.intro
False
False.elim
Fin
Fin.castSucc
Fin.ext
Fin.instOfNat
Fin.isLt
Fin.last
Fin.lastCases
Fin.mk
Fin.val
Fin.val_zero
Finset
Finset.Icc
Finset.instHasSubset
Finset.instMembership
Fintype
Function.Injective
Function.update
Function.update_eq_self
GT.gt
GetElem.getElem
GetElem?.getElem?
HAdd.hAdd
HAppend.hAppend
HEq
HEq.refl
HMul.hMul
HSub.hSub
HasSubset.Subset
Iff
Int
Int.add_one_le_of_lt
Int.decLe
Int.instAdd
Int.instAddCommGroup
Int.instAddGroup
Int.instAddLeftMono
Int.instAddMonoid
Int.instAddSemigroup
Int.instCommRing
Int.instDecidableEq
Int.instIsOrderedAddMonoid
Int.instLEInt
Int.instLTInt
Int.instLinearOrder
Int.instLocallyFiniteOrder
Int.instMul
Int.instNegInt
Int.instRing
Int.instSub
Int.lt_or_gt_of_ne
Int.natCast_add
Int.ofNat_mul
Int.ofNat_nonneg
Int.sub_eq_zero_of_eq
Int.sub_nonneg_of_le
IsOrderedAddMonoid
LE.le
LT.lt
Lattice.toSemilatticeInf
Lean.Name
Lean.Name.anonymous
Lean.Name.num
Lean.Name.str
Lean.Omega.Coeffs.isZero
Lean.Omega.Coeffs.ofList
Lean.Omega.Constraint.addEquality_sat
Lean.Omega.Constraint.addInequality_sat
Lean.Omega.Constraint.combine_sat'
Lean.Omega.Constraint.isImpossible
Lean.Omega.Constraint.mk
Lean.Omega.Constraint.not_sat'_of_isImpossible
Lean.Omega.Decidable.or_not_not_of_not_and
Lean.Omega.Int.add_congr
Lean.Omega.Int.lt_of_not_le
Lean.Omega.Int.mul_congr
Lean.Omega.Int.neg_congr
Lean.Omega.Int.ofNat_congr
Lean.Omega.Int.ofNat_le_of_le
Lean.Omega.Int.ofNat_lt_of_lt
Lean.Omega.Int.ofNat_sub_dichotomy
Lean.Omega.Int.ofNat_sub_sub
Lean.Omega.Int.sub_congr
Lean.Omega.LinearCombo
Lean.Omega.LinearCombo.add_eval
Lean.Omega.LinearCombo.coordinate
Lean.Omega.LinearCombo.coordinate_eval_0
Lean.Omega.LinearCombo.coordinate_eval_1
Lean.Omega.LinearCombo.coordinate_eval_2
Lean.Omega.LinearCombo.coordinate_eval_3
Lean.Omega.LinearCombo.coordinate_eval_4
Lean.Omega.LinearCombo.coordinate_eval_5
Lean.Omega.LinearCombo.coordinate_eval_6
Lean.Omega.LinearCombo.coordinate_eval_7
Lean.Omega.LinearCombo.coordinate_eval_8
Lean.Omega.LinearCombo.eval
Lean.Omega.LinearCombo.instAdd
Lean.Omega.LinearCombo.instNeg
Lean.Omega.LinearCombo.instSub
Lean.Omega.LinearCombo.mk
Lean.Omega.LinearCombo.mul
Lean.Omega.LinearCombo.mul_eval
Lean.Omega.LinearCombo.neg_eval
Lean.Omega.LinearCombo.sub_eval
Lean.Omega.combo_sat'
Lean.Omega.tidy_sat
LinearOrder
List
List.append_nil
List.cons
List.decidableBAll
List.drop
List.getElem?_eq_getElem
List.getElem?_eq_none
List.getElem?_replicate
List.instAppend
List.instGetElem?NatLtLength
List.instGetElemNatLtLength
List.length
List.nil
List.replicate
Membership.mem
MulZeroClass.toZero
Nat
Nat.cast
Nat.cast_zero
Nat.decLe
Nat.decLt
Nat.instNeZeroSucc
Nat.instPreorder
Nat.le_of_not_lt
Nat.lt_of_not_le
Nat.lt_or_gt_of_ne
Nat.recAux
Nat.sub_self
Nat.sub_zero
Nat.zero_le
Ne
NeZero
Neg.neg
NegZeroClass.toNeg
NegZeroClass.toZero
NonUnitalCommRing.toNonUnitalNonAssocCommRing
NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring
NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring
NonUnitalNonAssocSemiring.toMulZeroClass
Not
OfNat.ofNat
One
One.toOfNat1
Option
Option.ctorIdx
Option.getD
Option.getD_none
Option.instDecidableEq
Option.isNone
Option.isNone_iff_eq_none
Option.map
Option.none
Option.some
Option.some.inj
Option.some.noConfusion
Option.toList
Option.toList_none
Or
Or.elim
PUnit.fintype
PartialOrder.toPreorder
Preorder
Preorder.toLE
Preorder.toLT
Prod
Prod.casesOn
Prod.fst
Prod.mk
Prod.snd
Ring.toAddGroupWithOne
SemilatticeInf.toPartialOrder
SignType
SignType.cast
SignType.coe_neg_one
SignType.coe_one
SignType.instNeg
SignType.instOne
SignType.instZero
SignType.neg
SignType.neg_eq_neg_one
SignType.pos
SignType.pos_eq_one
SubNegMonoid.toAddMonoid
SubNegMonoid.toNeg
SubNegZeroMonoid.toNegZeroClass
SubtractionCommMonoid.toSubtractionMonoid
SubtractionMonoid.toSubNegZeroMonoid
Sum
Sum.casesOn
Sum.ctorIdx
Sum.inl
Sum.inr
Sum.inr.inj
True
Turing.Action
Turing.Action.apply
Turing.Action.apply_inputPos
Turing.Action.apply_output
Turing.Action.apply_state
Turing.Action.apply_workTapePos
Turing.Action.apply_workTapes
Turing.Action.mk
Turing.Action.output
Turing.Action.workTapes
Turing.Cfg
Turing.Cfg.ext
Turing.Cfg.inputPos
Turing.Cfg.inputSymbol
Turing.Cfg.inputSymbol._proof_2
Turing.Cfg.mk
Turing.Cfg.output
Turing.Cfg.state
Turing.Cfg.workTapePos
Turing.Cfg.workTapeSymbols
Turing.Cfg.workTapeSymbols_eq
Turing.Cfg.workTapes
Turing.FinTM
Turing.FinTM.bufferTape
Turing.FinTM.bufferTape_left
Turing.FinTM.bufferTape_nat
Turing.MultiTapeTM
Turing.MultiTapeTM.mk
Turing.MultiTapeTM.runFrom
Turing.MultiTapeTM.runFrom_succ_eq_step'
Turing.MultiTapeTM.runFrom_zero
Turing.MultiTapeTM.step
Turing.MultiTapeTM.step_of_some
Turing.MultiTapeTM.tr
Turing.MultiTapeTM.visitedByTapeHead
Turing.inputSymbolInner
Turing.instInhabitedCfg.default._proof_1
Turing.moveInputPos
Turing.moveInputPos_neg_of_ne_left
Turing.moveInputPos_neg_of_ne_left._proof_1
Turing.moveInputPos_pos_of_ne_right
Turing.moveInputPos_pos_of_ne_right._proof_1
Turing.moveInputPos_zero
Unit
Unit.unit
Zero.ofOfNat0
Zero.toOfNat0
abs
abs_le
abs_zero
add_assoc
add_sub_cancel_left
add_zero
by_cases
congr
congrArg
decide_eq_true_eq
decide_false
decide_true
dif_neg
dif_pos
dite
dite_cond_eq_true
dite_congr
eq_false
eq_false'
eq_self
eq_true
false_iff
funext
id
if_false
if_neg
if_pos
if_true
inferInstance
instAddNat
instDecidableAnd
instDecidableEqBool
instDecidableEqFin
instDecidableEqNat
instDecidableEqPUnit
instDecidableEqProd
instDecidableEqSum
instDecidableFalse
instDecidableNot
instDecidableOr
instDecidableTrue
instDistribLatticeOfLinearOrder
instFintypeProd
instFintypeSum
instHAdd
instHAppendOfAppend
instHMul
instHSub
instLENat
instLTNat
instLatticeInt
instMulNat
instNatCastInt
instNeZeroNatHAdd_1
instOfNat
instOfNatNat
instSubNat
ite
ite_cond_eq_true
ite_congr
le_of_le_of_eq
le_refl
le_rfl
lt_self_iff_false
neg_add_cancel
noConfusion_of_Nat
of_decide_eq_true
of_eq_true
propext
reduceCtorEq
rfl
sorryAx
sub_self
true_iff
zero_sub
```

## Verification

Base sorry inventory, recorded before filling:

```text
TuringMachine/Simulation: 1: branchTM_spaceUsed
TuringMachine/Composition: 3: idTM_computes, ifEqTM_computes, condTM_computes_iff
TuringMachine/Build/Wrappers: 2: timedCondTM_computes, timedCondTM_spaceUsed
TuringMachine/Build/Loop: 5: loopHostTM_contracts, loopHostTM_decides, loopHostTM_finds, loopHostTM_spaceUsed_le_budget, emitLoopTM_computes
TuringMachine/Encoding: 1: pairDiagTM_computes
ClassP/TimeConstructible: 2: _root_.Turing.FinTM.lengthBitsTM_computes, _root_.Turing.FinTM.lengthBitsTM_spaceUsed
TuringMachine/Build/NDHost: 1: ndWriterTM_run_block
TuringMachine/Build/Primitives: 3: polyUnaryTM_spaceUsed, unaryTokenTM_computes, appendBitTM_computes
TuringMachine/Build/ZoneRebalance: 2: exists_zoneRebalanceTM, exists_zoneExtendTM
TuringMachine/Build/InputWindow: 1: exists_inputWindowCopyTM
TuringMachine/Build/RecordTable: 4: exists_tableFindTM, exists_tableAppendTM, exists_recordValidTM, exists_recordNextTM
TuringMachine/CodeSimulator: 2: exists_canonGrammarStage [private], exists_uniformSimulator
TuringMachine/NDCodeSimulator: 2: exists_replayCanonizer, exists_ndInterpreterCore
TuringMachine/Build/InputDevice: 3: exists_rulerTestTM, exists_rulerDeviceTM, exists_rulerHostTM
TuringMachine/UniversalK: 3: exists_selfStartupTMK, exists_selfUniversalK, universalK
TOTAL 35
```

The fresh bootstrap checked 80/80 modules and found 35 baseline admissions. The final sweep
checked 80/80 modules and found 34: only `exists_rulerTestTM` was removed. All other warning
first-line locations and messages match the bootstrap. The owned module has exactly the two
open-target sorry warnings and no other warning. The expanded import probe has zero errors
and warnings. The delivered file has 557 lines, 15 public declarations
(unchanged), and 11 new private declarations.

Axiom walks for the three targets:

```text
'Turing.exists_rulerTestTM' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.exists_rulerDeviceTM' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.exists_rulerHostTM' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

Every new private and reachable own helper is printed in `axioms.log`. The proved target and
all new helpers use only `propext`, `Classical.choice`, and `Quot.sound` (or a subset).
`sorryAx` occurs only for the two explicitly open targets.

Final sweep tail:

```text
TCSlib/Complexity/TuringMachine/Universal.lean:1604:28: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:1604:55: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:2274:46: warning: This simp argument is unused:
  VirtualTag

Hint: Omit it from the simp argument list.
  simp_all ̵[̵V̵i̵r̵t̵u̵a̵l̵T̵a̵g̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
CHECK 78/80 TCSlib/Complexity/TuringMachine/UniversalK
TCSlib/Complexity/TuringMachine/UniversalK.lean:188:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/UniversalK.lean:233:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/UniversalK.lean:271:8: warning: declaration uses 'sorry'
CHECK 79/80 TCSlib/Complexity/TuringMachine/SelfUniversal
CHECK 80/80 TCSlib/Complexity/TuringMachine
FINAL SWEEP COMPLETE: 80/80 modules
```

Lint output:

```text
WARN  TCSlib/Complexity/TuringMachine/Build/Catalog.lean           13241 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Catalog.lean           9 public def(s) without a lemma beside them (check 8): catalogTrace, inputMoveAction, mealyRun, scanCarry, scanFold, scanKeep, scanMap, scanShift, tapeAction
WARN  TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean         5302 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean    1414 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean    1 public def(s) without a lemma beside them (check 8): roundStop
WARN  TCSlib/Complexity/TuringMachine/Build/Contract/Lift.lean     1 public def(s) without a lemma beside them (check 8): Contract.liftSymbols
WARN  TCSlib/Complexity/TuringMachine/Build/Convention.lean        4 public def(s) without a lemma beside them (check 8): solveSplit, solveSplitWith, splitAtLastTrue, unaryTokenSplit
WARN  TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean       2252 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean       2 public def(s) without a lemma beside them (check 8): counterLoopDecExit, counterLoopRedirect
WARN  TCSlib/Complexity/TuringMachine/Build/Embed.lean             1170 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Embed.lean             1 public def(s) without a lemma beside them (check 8): Cfg.select
WARN  TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean     1 public def(s) without a lemma beside them (check 8): SafeRun
WARN  TCSlib/Complexity/TuringMachine/Build/InputDevice.lean       2 public def(s) without a lemma beside them (check 8): RulerAt, rulerHostCfg
WARN  TCSlib/Complexity/TuringMachine/Build/Loop.lean              5294 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Loop.lean              2 public def(s) without a lemma beside them (check 8): callEntry, callExit
WARN  TCSlib/Complexity/TuringMachine/Build/NDHost.lean            1083 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/NDHost.lean            4 public def(s) without a lemma beside them (check 8): GuessRunPhase.State, guessRunPhases, guessRunRed, streamStartCfg
WARN  TCSlib/Complexity/TuringMachine/Build/OracleCall.lean        1 public def(s) without a lemma beside them (check 8): answerAction
WARN  TCSlib/Complexity/TuringMachine/Build/OracleSim.lean         2604 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Primitives.lean        6886 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/RecordTable.lean       6140 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/RecordTable.lean       4 public def(s) without a lemma beside them (check 8): TableAt, TableWF, recordTemplate, tableFields
WARN  TCSlib/Complexity/TuringMachine/Build/StepBlock.lean         3460 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/StepBlock.lean         12 public def(s) without a lemma beside them (check 8): Rep, SeekPh, SkipPh, afterTag, exit, recordFinTM, roundFinTM, succFieldCfg, summaryTape, tableBitsK, tableTape, workReadsK
WARN  TCSlib/Complexity/TuringMachine/Build/StepBlockForward.lean  1 public def(s) without a lemma beside them (check 8): forwardLoopCfg
WARN  TCSlib/Complexity/TuringMachine/Build/StepClock.lean         1160 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/StepClock.lean         2 public def(s) without a lemma beside them (check 8): Cfg.Stopped, clockCfg
WARN  TCSlib/Complexity/TuringMachine/Build/VirtualInput.lean      2 public def(s) without a lemma beside them (check 8): vhostCap, vhostSilentCfg
WARN  TCSlib/Complexity/TuringMachine/Build/WindowRun.lean         1377 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Wrappers.lean          4 public def(s) without a lemma beside them (check 8): captureAction, captureCfg, emitAction, emitCfg
WARN  TCSlib/Complexity/TuringMachine/Build/Zone.lean              1580 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/ZoneRebalance.lean     3 public def(s) without a lemma beside them (check 8): zoneExtendData, zoneRowHi, zoneRowLo
INFO  TCSlib/Complexity/TuringMachine/Build/Catalog.lean           13241 lines; 113 public / 392 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/CertShell.lean         904 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Build/CertShell.lean         904 lines; 2 public / 20 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean         5302 lines; 21 public / 98 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean    1414 lines; 84 public / 1 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Contract/Catalog.lean  562 lines; 27 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Contract/Counter.lean  134 lines; 3 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Contract/Embed.lean    130 lines; 3 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Contract/Lift.lean     84 lines; 1 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean     840 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean     840 lines; 15 public / 7 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Contract.lean          62 lines; 0 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Convention.lean        229 lines; 14 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean       2252 lines; 58 public / 20 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Embed.lean             1170 lines; 32 public / 16 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/EmitIterBody.lean      909 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Build/EmitIterBody.lean      909 lines; 1 public / 18 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean     326 lines; 18 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/InputCall.lean         535 lines; 2 public / 9 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/InputDevice.lean       557 lines; 15 public / 11 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/InputLength.lean       571 lines; 1 public / 11 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/InputWindow.lean       84 lines; 1 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Loop.lean              5294 lines; 21 public / 183 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/NDHost.lean            1083 lines; 25 public / 2 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/OracleCall.lean        182 lines; 6 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/OracleSim.lean         2604 lines; 13 public / 87 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Primitives.lean        6886 lines; 47 public / 234 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/RecordTable.lean       6140 lines; 29 public / 100 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Scan.lean              666 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Build/Scan.lean              666 lines; 9 public / 15 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Seam.lean              873 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Build/Seam.lean              873 lines; 22 public / 8 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/StepBlock.lean         3460 lines; 54 public / 71 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/StepBlockForward.lean  555 lines; 2 public / 20 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/StepBlockLoop.lean     511 lines; 5 public / 5 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/StepClock.lean         1160 lines; 7 public / 33 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/VirtualInput.lean      518 lines; 18 public / 1 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/WindowRun.lean         1377 lines; 10 public / 25 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Wrappers.lean          806 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Build/Wrappers.lean          806 lines; 14 public / 18 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Zone.lean              1580 lines; 87 public / 12 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/ZoneRebalance.lean     571 lines; 18 public / 18 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/ZoneTape.lean          568 lines; 48 public / 0 private declarations

style_lint: 0 FAIL, 32 WARN over 37 files
```

Evidence validation:

```text
PASS: 80/80 bootstrap and 80/80 final checks; 35 -> 34 baseline sorries.
PASS: all other warning first-line locations/messages identical.
PASS: target 1 and every new helper axiom walk uses only standard axioms.
EXPECTED OPEN: targets 2 and 3 retain sorryAx.
PASS: expanded public import probe, ownership, source inventory, duplication gates and lint.
```

## Duplication ledger

Both v3 screens ran sequentially under `nice -n 10` on the exact prescribed 11-file
population. The before output matches the supplied measured baseline byte-for-byte.
No new cross-file pair touches the owned file, and no new in-file pair reaches 90%.
New copies: none. New privately copied proved material: 0 characters (0% of the delivered file).

New in-file pairs:

- `InputDevice.lean::rd_trace_step  reproduces  InputDevice.lean::rd_read_nat: 73/90 = 81%` — Interior ruler reads are shared through rd_read_nat in both legs; the overlap is the separate right-delimiter lookup, which reads none rather than some true, using the same public bufferTape_nat and replicate equations. No second trajectory or induction is present.

screen-before.txt:

```text
declarations screened: 272; copy pairs (target reproduces >= half of source): 138; reproduced text: 31,217 chars
   Seam.lean::seamReleaseTM_step_inr  reproduces  Seam.lean::seamComp_step_right: 135/135 = 100%
   Seam.lean::seamComp_step_right  reproduces  Seam.lean::seamReleaseTM_step_inr: 135/135 = 100%
   Embed.lean::embedSilentRetTM  reproduces  Embed.lean::embedEmitRetTM: 215/219 = 98%
   Seam.lean::seamComp_step_left  reproduces  Seam.lean::seamReleaseTM_step_inr: 132/135 = 98%
   Seam.lean::seamComp_step_left  reproduces  Seam.lean::seamComp_step_right: 132/135 = 98%
   UniversalInterpreter.lean::universal_initialized  reproduces  UniversalInterpreter.lean::universalEval_reads: 86/88 = 98%
   UniversalInterpreter.lean::universalInterpreter_first  reproduces  UniversalInterpreter.lean::universalEval_reads: 86/88 = 98%
   UniversalBlock.lean::universal_apply_record  reproduces  UniversalInterpreter.lean::universalEval_reads: 86/88 = 98%
   UniversalStartup.lean::universalPrefix_start  reproduces  UniversalStartup.lean::universalPrefix_penultimate: 385/395 = 97%
   VirtualInput.lean::vhostEmitTM_visitedByTapeHead_buffer  reproduces  VirtualInput.lean::vhostEmitTM_visitedByTapeHead_bank: 122/126 = 97%
   Embed.lean::embedEmitRetTM  reproduces  Embed.lean::embedSilentRetTM: 215/224 = 96%
   VirtualInput.lean::vhostEmitTM_visitedByTapeHead_bank  reproduces  VirtualInput.lean::vhostEmitTM_visitedByTapeHead_buffer: 122/128 = 95%
   UniversalBlock.lean::universal_serialization_actions  reproduces  UniversalInterpreter.lean::universal_serialization_header: 589/619 = 95%
   Basic.lean::RoundContract  reproduces  Basic.lean::ReturnContract: 412/436 = 94%
   UniversalInterpreter.lean::universalAdmin_apply  reproduces  UniversalInterpreter.lean::universalEval_reads: 83/88 = 94%
   Simulation.lean::rewind_heads  reproduces  Simulation.lean::timed_rewind: 395/435 = 91%
   UniversalBlock.lean::universal_skip_unary  reproduces  UniversalInterpreter.lean::universal_initial_skip: 873/970 = 90%
   Simulation.lean::bufferedSecondCfg_run  reproduces  VirtualInput.lean::vhostEmitTM_runFrom: 241/268 = 90%
   UniversalInterpreter.lean::universalInterpreter  reproduces  UniversalInterpreter.lean::universalSkipDone: 60/69 = 87%
   Simulation.lean::bufferedFirstCfg_run  reproduces  UniversalStartup.lean::universalCapture_run: 146/169 = 86%
   Embed.lean::embedSilentCfg  reproduces  Embed.lean::embedEmitCfg: 165/192 = 86%
   UniversalStartup.lean::universalCapture_step  reproduces  UniversalStartup.lean::universalCapture_init: 287/334 = 86%
   Basic.lean::Cfg.SameOutside.keep_blank  reproduces  Basic.lean::endpoint_not_mem: 97/114 = 85%
   VirtualInput.lean::vhostEmitTM_runFrom  reproduces  Simulation.lean::bufferedSecondCfg_run: 241/284 = 85%
   Basic.lean::safeSegment_iff  reproduces  Basic.lean::segment_iff: 84/99 = 85%
   Basic.lean::time_box  reproduces  Basic.lean::time_envelope: 123/146 = 84%
   Basic.lean::hullLo  reproduces  Basic.lean::hullHi: 114/139 = 82%
   Basic.lean::hullHi  reproduces  Basic.lean::hullLo: 114/139 = 82%
   Simulation.lean::rightCfg_step  reproduces  Simulation.lean::leftCfg_step: 306/378 = 81%
   Embed.lean::embedSilent_step  reproduces  Embed.lean::embedEmit_step: 315/393 = 80%
   UniversalStartup.lean::universal_pair_separator  reproduces  UniversalStartup.lean::universal_pair_length: 121/151 = 80%
   Simulation.lean::leftCfg_step  reproduces  Simulation.lean::rightCfg_step: 306/384 = 80%
   UniversalInterpreter.lean::universalInterpreter_first  reproduces  UniversalInterpreter.lean::universalAdmin_apply: 210/264 = 80%
   UniversalStartup.lean::universalCapture_init  reproduces  Simulation.lean::bufferedFirstCfg_init: 255/322 = 79%
   Embed.lean::embedSilentRet_step  reproduces  Embed.lean::embedSilentRetTM_visitedByTapeHead: 106/134 = 79%
   Basic.lean::endpoint_not_mem  reproduces  Basic.lean::traj_iff: 80/103 = 78%
   Basic.lean::Frames.trans  reproduces  Basic.lean::traj_iff: 80/103 = 78%
   Basic.lean::Cfg.SameOutside.keep_blank  reproduces  Basic.lean::traj_iff: 80/103 = 78%
   Simulation.lean::bufferedFirstCfg_init  reproduces  UniversalStartup.lean::universalCapture_init: 255/334 = 76%
   Basic.lean::round_iff  reproduces  Basic.lean::segment_iff: 75/99 = 76%
   Embed.lean::embedEmitRet_step  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 87/115 = 76%
   Simulation.lean::rightCfg_apply  reproduces  Simulation.lean::leftCfg_apply: 142/188 = 76%
   Seam.lean::seamCompTM  reproduces  Seam.lean::seamReleaseTM: 148/196 = 76%
   UniversalStartup.lean::universalPrefix_bits  reproduces  UniversalStartup.lean::universalPrefix_start: 600/797 = 75%
   UniversalInterpreter.lean::universalRecords  reproduces  UniversalBlock.lean::universalActions: 105/140 = 75%
   Simulation.lean::leftCfg_apply  reproduces  Simulation.lean::rightCfg_apply: 142/192 = 74%
   Basic.lean::segment_iff  reproduces  Basic.lean::round_iff: 75/102 = 74%
   Basic.lean::safeSegment_iff  reproduces  Basic.lean::round_iff: 75/102 = 74%
   Basic.lean::endpoint_not_mem  reproduces  Basic.lean::Cfg.SameOutside.keep_blank: 97/132 = 73%
   Embed.lean::embedEmit_step  reproduces  Embed.lean::embedSilent_step: 315/429 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead_frame: 204/279 = 73%
   UniversalInterpreter.lean::universal_initial_skip  reproduces  UniversalBlock.lean::universal_skip_unary: 873/1196 = 73%
   Simulation.lean::bufferedFirstCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 235/322 = 73%
   UniversalInterpreter.lean::universal_serialization_header  reproduces  UniversalBlock.lean::universal_serialization_actions: 589/809 = 73%
   Basic.lean::ReturnContract  reproduces  Basic.lean::RoundContract: 412/566 = 73%
   UniversalInterpreter.lean::universal_unary_copy  reproduces  UniversalInterpreter.lean::universal_initial_skip: 706/970 = 73%
   UniversalStartup.lean::universalCapture_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_frame: 82/113 = 73%
   Seam.lean::seamCompTM_spaceUsedByTape_le_max  reproduces  Seam.lean::seamCompTM_spaceUsedByTape_le_add: 92/127 = 72%
   UniversalInterpreter.lean::universalAdmin_apply  reproduces  UniversalInterpreter.lean::universalInterpreter_first: 210/290 = 72%
   Seam.lean::seamCompTM_runFrom_left  reproduces  UniversalStartup.lean::universalCapture_run: 122/169 = 72%
   Simulation.lean::rightAction  reproduces  Simulation.lean::leftAction: 69/96 = 72%
   Simulation.lean::leftAction  reproduces  Simulation.lean::rightAction: 69/96 = 72%
   Basic.lean::locate  reproduces  Basic.lean::cut: 219/305 = 72%
   UniversalInterpreter.lean::universal_initial_skip  reproduces  UniversalInterpreter.lean::universal_unary_copy: 706/987 = 72%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::leftCfg_apply: 133/188 = 71%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 171/242 = 71%
   Seam.lean::seamCompTM_firstReturn  reproduces  Seam.lean::seamCompTM_run: 151/214 = 71%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::rightCfg_apply: 135/192 = 70%
   Simulation.lean::rightCfg_run  reproduces  Simulation.lean::leftCfg_run: 71/101 = 70%
   Basic.lean::traj_iff  reproduces  Basic.lean::endpoint_not_mem: 80/114 = 70%
   Basic.lean::Frames.trans  reproduces  Basic.lean::endpoint_not_mem: 80/114 = 70%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 188/268 = 70%
   UniversalInterpreter.lean::universal_record_shape  reproduces  UniversalBlock.lean::universalActionBits_decode: 133/191 = 70%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   Simulation.lean::bufferedFirstCfg_rewind  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   UniversalStartup.lean::universalPrefix_start  reproduces  UniversalStartup.lean::universalPrefix_bits: 600/864 = 69%
   Simulation.lean::leftCfg_run  reproduces  Simulation.lean::rightCfg_run: 71/103 = 69%
   UniversalStartup.lean::universalPrefix_bits  reproduces  UniversalStartup.lean::universalPrefix_penultimate: 272/395 = 69%
   UniversalBlock.lean::universal_skip_unary  reproduces  UniversalInterpreter.lean::universal_unary_copy: 673/987 = 68%
   UniversalStartup.lean::universalCapture_start  reproduces  UniversalStartup.lean::universal_live_before: 82/121 = 68%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 204/305 = 67%
   Simulation.lean::timed_rewind  reproduces  Simulation.lean::rewind_heads: 395/594 = 66%
   Embed.lean::embedSilent_apply  reproduces  Embed.lean::embedEmit_apply: 168/253 = 66%
   UniversalBlock.lean::universal_prepare_next  reproduces  UniversalInterpreter.lean::universal_initial_skip: 640/970 = 66%
   UniversalInterpreter.lean::universal_count_run  reproduces  UniversalInterpreter.lean::universal_initial_skip: 637/970 = 66%
   UniversalInterpreter.lean::universal_initialized  reproduces  UniversalInterpreter.lean::universalAdmin_apply: 171/264 = 65%
   Simulation.lean::rightCfg  reproduces  Simulation.lean::leftCfg: 84/130 = 65%
   Simulation.lean::leftCfg  reproduces  Simulation.lean::rightCfg: 84/130 = 65%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_rewind: 473/735 = 64%
   UniversalStartup.lean::universal_pair_get  reproduces  UniversalStartup.lean::universal_pair_separator: 133/207 = 64%
   UniversalStartup.lean::universalCapture_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 146/228 = 64%
   Embed.lean::embedEmitTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 171/268 = 64%
   Seam.lean::seamCompTM_run  reproduces  Seam.lean::seamCompTM_firstReturn: 151/237 = 64%
   UniversalBlock.lean::universal_apply_record  reproduces  UniversalInterpreter.lean::universalAdmin_apply: 168/264 = 64%
   UniversalStartup.lean::universalCaptureCfg  reproduces  Simulation.lean::bufferedFirstCfg: 109/172 = 63%
   UniversalStartup.lean::universalCapture_step  reproduces  Simulation.lean::bufferedFirstCfg_step: 725/1152 = 63%
   Basic.lean::RoundContract  reproduces  Basic.lean::Contract: 302/487 = 62%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_frame: 70/113 = 62%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 199/322 = 62%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 188/305 = 62%
   Embed.lean::embedEmitCfg  reproduces  Embed.lean::embedSilentCfg: 165/270 = 61%
   Seam.lean::seamReleaseTM_step_inr  reproduces  Seam.lean::seamComp_step_left: 132/216 = 61%
   Seam.lean::seamComp_step_right  reproduces  Seam.lean::seamComp_step_left: 132/216 = 61%
   Basic.lean::traj_iff  reproduces  Basic.lean::Cfg.SameOutside.keep_blank: 80/132 = 61%
   Basic.lean::Frames.trans  reproduces  Basic.lean::Cfg.SameOutside.keep_blank: 80/132 = 61%
   Simulation.lean::bufferedSecondCfg  reproduces  Simulation.lean::bufferedScanCfg: 83/137 = 61%
   Simulation.lean::bufferedCompTM  reproduces  UniversalStartup.lean::universalCaptureTM: 223/372 = 60%
   Simulation.lean::bufferedFirstCfg  reproduces  UniversalStartup.lean::universalCaptureCfg: 109/184 = 59%
   UniversalStartup.lean::universal_pair_length  reproduces  UniversalStartup.lean::universal_pair_separator: 121/207 = 58%
   UniversalBlock.lean::universal_apply_record  reproduces  UniversalInterpreter.lean::universalInterpreter_first: 169/290 = 58%
   Seam.lean::seamReleaseTM  reproduces  Seam.lean::seamCompTM: 148/254 = 58%
   UniversalInterpreter.lean::universal_initialized  reproduces  UniversalInterpreter.lean::universalInterpreter_first: 168/290 = 58%
   Embed.lean::embedSilentRetTM_run  reproduces  Embed.lean::embedSilentTM_runFrom: 68/118 = 58%
   Simulation.lean::bufferedScanCfg_run  reproduces  UniversalStartup.lean::universalCapture_init: 192/334 = 57%
   Simulation.lean::bufferedFirstCfg_rewind  reproduces  UniversalStartup.lean::universalCapture_init: 192/334 = 57%
   Basic.lean::time_envelope  reproduces  Basic.lean::time_box: 123/215 = 57%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 138/242 = 57%
   UniversalBlock.lean::universal_prepare_next  reproduces  UniversalInterpreter.lean::universal_unary_copy: 560/987 = 57%
   Simulation.lean::bufferedFirstCfg_step  reproduces  UniversalStartup.lean::universalCapture_step: 725/1281 = 57%
   Embed.lean::embedSilentRetTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 65/115 = 57%
   UniversalInterpreter.lean::universal_unary_copy  reproduces  UniversalBlock.lean::universal_skip_unary: 673/1196 = 56%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_frame: 63/113 = 56%
   Simulation.lean::rewind_from_any  reproduces  Simulation.lean::timed_rewind: 239/435 = 55%
   UniversalK.lean::EffectiveMachineCode2.toK  reproduces  UniversalK.lean::EffectiveMachineCode.toK: 84/154 = 55%
   UniversalBlock.lean::universal_prepare_next  reproduces  UniversalBlock.lean::universal_skip_unary: 651/1196 = 54%
   UniversalK.lean::EffectiveMachineCode.toK  reproduces  UniversalK.lean::EffectiveMachineCode2.toK: 84/155 = 54%
   UniversalBlock.lean::universal_read_fixed  reproduces  UniversalInterpreter.lean::universal_skip_fixed: 358/665 = 54%
   UniversalInterpreter.lean::universal_initialized  reproduces  UniversalStartup.lean::universalCanon_complete: 141/262 = 54%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Simulation.lean::bufferedFirstCfg_run: 122/228 = 54%
   Basic.lean::Contract  reproduces  Basic.lean::RoundContract: 302/566 = 53%
   UniversalInterpreter.lean::universal_count_run  reproduces  UniversalBlock.lean::universal_skip_unary: 636/1196 = 53%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 141/268 = 53%
   Simulation.lean::bufferedSecondCfg_step  reproduces  UniversalStartup.lean::universalCapture_init: 175/334 = 52%
   UniversalBlock.lean::universal_skip_unary  reproduces  UniversalInterpreter.lean::universal_skip_fixed: 343/665 = 52%
   Simulation.lean::timed_rewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   UniversalBlock.lean::universalActions  reproduces  UniversalInterpreter.lean::universalRecords: 105/209 = 50%
```

screen-after.txt:

```text
declarations screened: 281; copy pairs (target reproduces >= half of source): 139; reproduced text: 31,290 chars
   Seam.lean::seamReleaseTM_step_inr  reproduces  Seam.lean::seamComp_step_right: 135/135 = 100%
   Seam.lean::seamComp_step_right  reproduces  Seam.lean::seamReleaseTM_step_inr: 135/135 = 100%
   Embed.lean::embedSilentRetTM  reproduces  Embed.lean::embedEmitRetTM: 215/219 = 98%
   Seam.lean::seamComp_step_left  reproduces  Seam.lean::seamReleaseTM_step_inr: 132/135 = 98%
   Seam.lean::seamComp_step_left  reproduces  Seam.lean::seamComp_step_right: 132/135 = 98%
   UniversalInterpreter.lean::universal_initialized  reproduces  UniversalInterpreter.lean::universalEval_reads: 86/88 = 98%
   UniversalInterpreter.lean::universalInterpreter_first  reproduces  UniversalInterpreter.lean::universalEval_reads: 86/88 = 98%
   UniversalBlock.lean::universal_apply_record  reproduces  UniversalInterpreter.lean::universalEval_reads: 86/88 = 98%
   UniversalStartup.lean::universalPrefix_start  reproduces  UniversalStartup.lean::universalPrefix_penultimate: 385/395 = 97%
   VirtualInput.lean::vhostEmitTM_visitedByTapeHead_buffer  reproduces  VirtualInput.lean::vhostEmitTM_visitedByTapeHead_bank: 122/126 = 97%
   Embed.lean::embedEmitRetTM  reproduces  Embed.lean::embedSilentRetTM: 215/224 = 96%
   VirtualInput.lean::vhostEmitTM_visitedByTapeHead_bank  reproduces  VirtualInput.lean::vhostEmitTM_visitedByTapeHead_buffer: 122/128 = 95%
   UniversalBlock.lean::universal_serialization_actions  reproduces  UniversalInterpreter.lean::universal_serialization_header: 589/619 = 95%
   Basic.lean::RoundContract  reproduces  Basic.lean::ReturnContract: 412/436 = 94%
   UniversalInterpreter.lean::universalAdmin_apply  reproduces  UniversalInterpreter.lean::universalEval_reads: 83/88 = 94%
   Simulation.lean::rewind_heads  reproduces  Simulation.lean::timed_rewind: 395/435 = 91%
   UniversalBlock.lean::universal_skip_unary  reproduces  UniversalInterpreter.lean::universal_initial_skip: 873/970 = 90%
   Simulation.lean::bufferedSecondCfg_run  reproduces  VirtualInput.lean::vhostEmitTM_runFrom: 241/268 = 90%
   UniversalInterpreter.lean::universalInterpreter  reproduces  UniversalInterpreter.lean::universalSkipDone: 60/69 = 87%
   Simulation.lean::bufferedFirstCfg_run  reproduces  UniversalStartup.lean::universalCapture_run: 146/169 = 86%
   Embed.lean::embedSilentCfg  reproduces  Embed.lean::embedEmitCfg: 165/192 = 86%
   UniversalStartup.lean::universalCapture_step  reproduces  UniversalStartup.lean::universalCapture_init: 287/334 = 86%
   Basic.lean::Cfg.SameOutside.keep_blank  reproduces  Basic.lean::endpoint_not_mem: 97/114 = 85%
   VirtualInput.lean::vhostEmitTM_runFrom  reproduces  Simulation.lean::bufferedSecondCfg_run: 241/284 = 85%
   Basic.lean::safeSegment_iff  reproduces  Basic.lean::segment_iff: 84/99 = 85%
   Basic.lean::time_box  reproduces  Basic.lean::time_envelope: 123/146 = 84%
   Basic.lean::hullLo  reproduces  Basic.lean::hullHi: 114/139 = 82%
   Basic.lean::hullHi  reproduces  Basic.lean::hullLo: 114/139 = 82%
   InputDevice.lean::rd_trace_step  reproduces  InputDevice.lean::rd_read_nat: 73/90 = 81%
   Simulation.lean::rightCfg_step  reproduces  Simulation.lean::leftCfg_step: 306/378 = 81%
   Embed.lean::embedSilent_step  reproduces  Embed.lean::embedEmit_step: 315/393 = 80%
   UniversalStartup.lean::universal_pair_separator  reproduces  UniversalStartup.lean::universal_pair_length: 121/151 = 80%
   Simulation.lean::leftCfg_step  reproduces  Simulation.lean::rightCfg_step: 306/384 = 80%
   UniversalInterpreter.lean::universalInterpreter_first  reproduces  UniversalInterpreter.lean::universalAdmin_apply: 210/264 = 80%
   UniversalStartup.lean::universalCapture_init  reproduces  Simulation.lean::bufferedFirstCfg_init: 255/322 = 79%
   Embed.lean::embedSilentRet_step  reproduces  Embed.lean::embedSilentRetTM_visitedByTapeHead: 106/134 = 79%
   Basic.lean::endpoint_not_mem  reproduces  Basic.lean::traj_iff: 80/103 = 78%
   Basic.lean::Frames.trans  reproduces  Basic.lean::traj_iff: 80/103 = 78%
   Basic.lean::Cfg.SameOutside.keep_blank  reproduces  Basic.lean::traj_iff: 80/103 = 78%
   Simulation.lean::bufferedFirstCfg_init  reproduces  UniversalStartup.lean::universalCapture_init: 255/334 = 76%
   Basic.lean::round_iff  reproduces  Basic.lean::segment_iff: 75/99 = 76%
   Embed.lean::embedEmitRet_step  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 87/115 = 76%
   Simulation.lean::rightCfg_apply  reproduces  Simulation.lean::leftCfg_apply: 142/188 = 76%
   Seam.lean::seamCompTM  reproduces  Seam.lean::seamReleaseTM: 148/196 = 76%
   UniversalStartup.lean::universalPrefix_bits  reproduces  UniversalStartup.lean::universalPrefix_start: 600/797 = 75%
   UniversalInterpreter.lean::universalRecords  reproduces  UniversalBlock.lean::universalActions: 105/140 = 75%
   Simulation.lean::leftCfg_apply  reproduces  Simulation.lean::rightCfg_apply: 142/192 = 74%
   Basic.lean::segment_iff  reproduces  Basic.lean::round_iff: 75/102 = 74%
   Basic.lean::safeSegment_iff  reproduces  Basic.lean::round_iff: 75/102 = 74%
   Basic.lean::endpoint_not_mem  reproduces  Basic.lean::Cfg.SameOutside.keep_blank: 97/132 = 73%
   Embed.lean::embedEmit_step  reproduces  Embed.lean::embedSilent_step: 315/429 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead_frame: 204/279 = 73%
   UniversalInterpreter.lean::universal_initial_skip  reproduces  UniversalBlock.lean::universal_skip_unary: 873/1196 = 73%
   Simulation.lean::bufferedFirstCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 235/322 = 73%
   UniversalInterpreter.lean::universal_serialization_header  reproduces  UniversalBlock.lean::universal_serialization_actions: 589/809 = 73%
   Basic.lean::ReturnContract  reproduces  Basic.lean::RoundContract: 412/566 = 73%
   UniversalInterpreter.lean::universal_unary_copy  reproduces  UniversalInterpreter.lean::universal_initial_skip: 706/970 = 73%
   UniversalStartup.lean::universalCapture_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_frame: 82/113 = 73%
   Seam.lean::seamCompTM_spaceUsedByTape_le_max  reproduces  Seam.lean::seamCompTM_spaceUsedByTape_le_add: 92/127 = 72%
   UniversalInterpreter.lean::universalAdmin_apply  reproduces  UniversalInterpreter.lean::universalInterpreter_first: 210/290 = 72%
   Seam.lean::seamCompTM_runFrom_left  reproduces  UniversalStartup.lean::universalCapture_run: 122/169 = 72%
   Simulation.lean::rightAction  reproduces  Simulation.lean::leftAction: 69/96 = 72%
   Simulation.lean::leftAction  reproduces  Simulation.lean::rightAction: 69/96 = 72%
   Basic.lean::locate  reproduces  Basic.lean::cut: 219/305 = 72%
   UniversalInterpreter.lean::universal_initial_skip  reproduces  UniversalInterpreter.lean::universal_unary_copy: 706/987 = 72%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::leftCfg_apply: 133/188 = 71%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 171/242 = 71%
   Seam.lean::seamCompTM_firstReturn  reproduces  Seam.lean::seamCompTM_run: 151/214 = 71%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::rightCfg_apply: 135/192 = 70%
   Simulation.lean::rightCfg_run  reproduces  Simulation.lean::leftCfg_run: 71/101 = 70%
   Basic.lean::traj_iff  reproduces  Basic.lean::endpoint_not_mem: 80/114 = 70%
   Basic.lean::Frames.trans  reproduces  Basic.lean::endpoint_not_mem: 80/114 = 70%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 188/268 = 70%
   UniversalInterpreter.lean::universal_record_shape  reproduces  UniversalBlock.lean::universalActionBits_decode: 133/191 = 70%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   Simulation.lean::bufferedFirstCfg_rewind  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   UniversalStartup.lean::universalPrefix_start  reproduces  UniversalStartup.lean::universalPrefix_bits: 600/864 = 69%
   Simulation.lean::leftCfg_run  reproduces  Simulation.lean::rightCfg_run: 71/103 = 69%
   UniversalStartup.lean::universalPrefix_bits  reproduces  UniversalStartup.lean::universalPrefix_penultimate: 272/395 = 69%
   UniversalBlock.lean::universal_skip_unary  reproduces  UniversalInterpreter.lean::universal_unary_copy: 673/987 = 68%
   UniversalStartup.lean::universalCapture_start  reproduces  UniversalStartup.lean::universal_live_before: 82/121 = 68%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 204/305 = 67%
   Simulation.lean::timed_rewind  reproduces  Simulation.lean::rewind_heads: 395/594 = 66%
   Embed.lean::embedSilent_apply  reproduces  Embed.lean::embedEmit_apply: 168/253 = 66%
   UniversalBlock.lean::universal_prepare_next  reproduces  UniversalInterpreter.lean::universal_initial_skip: 640/970 = 66%
   UniversalInterpreter.lean::universal_count_run  reproduces  UniversalInterpreter.lean::universal_initial_skip: 637/970 = 66%
   UniversalInterpreter.lean::universal_initialized  reproduces  UniversalInterpreter.lean::universalAdmin_apply: 171/264 = 65%
   Simulation.lean::rightCfg  reproduces  Simulation.lean::leftCfg: 84/130 = 65%
   Simulation.lean::leftCfg  reproduces  Simulation.lean::rightCfg: 84/130 = 65%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_rewind: 473/735 = 64%
   UniversalStartup.lean::universal_pair_get  reproduces  UniversalStartup.lean::universal_pair_separator: 133/207 = 64%
   UniversalStartup.lean::universalCapture_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 146/228 = 64%
   Embed.lean::embedEmitTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 171/268 = 64%
   Seam.lean::seamCompTM_run  reproduces  Seam.lean::seamCompTM_firstReturn: 151/237 = 64%
   UniversalBlock.lean::universal_apply_record  reproduces  UniversalInterpreter.lean::universalAdmin_apply: 168/264 = 64%
   UniversalStartup.lean::universalCaptureCfg  reproduces  Simulation.lean::bufferedFirstCfg: 109/172 = 63%
   UniversalStartup.lean::universalCapture_step  reproduces  Simulation.lean::bufferedFirstCfg_step: 725/1152 = 63%
   Basic.lean::RoundContract  reproduces  Basic.lean::Contract: 302/487 = 62%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_frame: 70/113 = 62%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 199/322 = 62%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 188/305 = 62%
   Embed.lean::embedEmitCfg  reproduces  Embed.lean::embedSilentCfg: 165/270 = 61%
   Seam.lean::seamReleaseTM_step_inr  reproduces  Seam.lean::seamComp_step_left: 132/216 = 61%
   Seam.lean::seamComp_step_right  reproduces  Seam.lean::seamComp_step_left: 132/216 = 61%
   Basic.lean::traj_iff  reproduces  Basic.lean::Cfg.SameOutside.keep_blank: 80/132 = 61%
   Basic.lean::Frames.trans  reproduces  Basic.lean::Cfg.SameOutside.keep_blank: 80/132 = 61%
   Simulation.lean::bufferedSecondCfg  reproduces  Simulation.lean::bufferedScanCfg: 83/137 = 61%
   Simulation.lean::bufferedCompTM  reproduces  UniversalStartup.lean::universalCaptureTM: 223/372 = 60%
   Simulation.lean::bufferedFirstCfg  reproduces  UniversalStartup.lean::universalCaptureCfg: 109/184 = 59%
   UniversalStartup.lean::universal_pair_length  reproduces  UniversalStartup.lean::universal_pair_separator: 121/207 = 58%
   UniversalBlock.lean::universal_apply_record  reproduces  UniversalInterpreter.lean::universalInterpreter_first: 169/290 = 58%
   Seam.lean::seamReleaseTM  reproduces  Seam.lean::seamCompTM: 148/254 = 58%
   UniversalInterpreter.lean::universal_initialized  reproduces  UniversalInterpreter.lean::universalInterpreter_first: 168/290 = 58%
   Embed.lean::embedSilentRetTM_run  reproduces  Embed.lean::embedSilentTM_runFrom: 68/118 = 58%
   Simulation.lean::bufferedScanCfg_run  reproduces  UniversalStartup.lean::universalCapture_init: 192/334 = 57%
   Simulation.lean::bufferedFirstCfg_rewind  reproduces  UniversalStartup.lean::universalCapture_init: 192/334 = 57%
   Basic.lean::time_envelope  reproduces  Basic.lean::time_box: 123/215 = 57%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 138/242 = 57%
   UniversalBlock.lean::universal_prepare_next  reproduces  UniversalInterpreter.lean::universal_unary_copy: 560/987 = 57%
   Simulation.lean::bufferedFirstCfg_step  reproduces  UniversalStartup.lean::universalCapture_step: 725/1281 = 57%
   Embed.lean::embedSilentRetTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 65/115 = 57%
   UniversalInterpreter.lean::universal_unary_copy  reproduces  UniversalBlock.lean::universal_skip_unary: 673/1196 = 56%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_frame: 63/113 = 56%
   Simulation.lean::rewind_from_any  reproduces  Simulation.lean::timed_rewind: 239/435 = 55%
   UniversalK.lean::EffectiveMachineCode2.toK  reproduces  UniversalK.lean::EffectiveMachineCode.toK: 84/154 = 55%
   UniversalBlock.lean::universal_prepare_next  reproduces  UniversalBlock.lean::universal_skip_unary: 651/1196 = 54%
   UniversalK.lean::EffectiveMachineCode.toK  reproduces  UniversalK.lean::EffectiveMachineCode2.toK: 84/155 = 54%
   UniversalBlock.lean::universal_read_fixed  reproduces  UniversalInterpreter.lean::universal_skip_fixed: 358/665 = 54%
   UniversalInterpreter.lean::universal_initialized  reproduces  UniversalStartup.lean::universalCanon_complete: 141/262 = 54%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Simulation.lean::bufferedFirstCfg_run: 122/228 = 54%
   Basic.lean::Contract  reproduces  Basic.lean::RoundContract: 302/566 = 53%
   UniversalInterpreter.lean::universal_count_run  reproduces  UniversalBlock.lean::universal_skip_unary: 636/1196 = 53%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 141/268 = 53%
   Simulation.lean::bufferedSecondCfg_step  reproduces  UniversalStartup.lean::universalCapture_init: 175/334 = 52%
   UniversalBlock.lean::universal_skip_unary  reproduces  UniversalInterpreter.lean::universal_skip_fixed: 343/665 = 52%
   Simulation.lean::timed_rewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   UniversalBlock.lean::universalActions  reproduces  UniversalInterpreter.lean::universalRecords: 105/209 = 50%
```

## Archive and checklist

The ZIP contains exactly the full owned source, this report, one format-patch file, a git
bundle with the base as its sole prerequisite, bootstrap/final/axiom logs, both screen outputs,
the authorized shim source, and `SHA256SUMS`. No compiled shim, build product, draft helper, or
other source file is shipped. The final-sweep log also embeds ownership, probe, lint and
validation output so no extra log entry is required.

Bundle verification:

```text
/workspace/scratch/177f06803258/delivery/fill-b6-rulerdevice.bundle is okay
The bundle contains this ref:
f9810ddf411ebb40b07e287398787d0db4e160f6 refs/heads/fill/b6-rulerdevice
The bundle requires this ref:
94b986d4db7167ab2a8b20d38d4385f11e60be0e 
The bundle uses this hash algorithm: sha1
```

The boxes below mark that each requested report item is answered, not that E1/E2 are waived.

- [x] Targets/phase, exact base, and successful ancestor check: phase 1, 1/3 proved.
- [x] Imports and owned-region edits: exact delivered placement; recovery sequence exception E1.
- [x] Every new declaration and role, leaf justification, and three Fill appendices.
- [x] Delivered constant `C = 2`; open-target constants/cost explicitly only outlined.
- [x] Promotion candidates and escalations E1/E2, plus the workspace-loss obstruction.
- [x] External citation inventory, expanded probe, R3/private-name grep and dependency walk.
- [x] Both v3 screens, each new pair justified, and new copies: none.
- [x] File/declaration counts, full final-sweep tail, axiom prints, and lint result.
