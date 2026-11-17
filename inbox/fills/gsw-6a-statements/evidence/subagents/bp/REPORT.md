# Sub-agent bp report: BranchingPrograms statements (6a)

*Saved by the lead from the sub-agent's hand-back message (the harness did not let the sub-agent write
this file). Content as reported; the lead's verification is in the main `REPORT.md`.*

All six files compile, every C1–C25 row has its declaration, and every probe P1–P7 passes. No r3
statement turned out false. Worktree `/home/user/wt-bp` (branch `sub/bp`, base = the lead's first O1
commit `c51ccd065`); nothing committed. Every check went through `tools/check.py`; `lake` and `lean`
were never run directly.

Logs in this folder: `build-final.log` (+ `.summary`, the final module build); `probes-final.log`
(+ `.summary`, the final probe run against the final tree); `build.log`, `probes.log`, `scratch.log`
(history); `probes-src/` (copies of the probe sources); `run_probes.sh` and `guarded_check.sh` (the
guarded runner, which kills a Lean run after 110 s).

## 1. Files (final): lines / max width (Python `len`) / `sorry` targets

| File | Lines | Max width | `sorry` targets |
|---|---|---|---|
| `TCSlib/Complexity/BranchingPrograms.lean` (facade) | 39 | 97 | 0 |
| `TCSlib/Complexity/BranchingPrograms/Defs.lean` | 407 | 100 | 11 |
| `TCSlib/Complexity/BranchingPrograms/Eval.lean` | 172 | 98 | 5 |
| `TCSlib/Complexity/BranchingPrograms/Barrington.lean` | 463 | 99 | 11 |
| `TCSlib/Complexity/BranchingPrograms/BarringtonConverse.lean` | 304 | 100 | 11 |
| `TCSlib/Complexity/BranchingPrograms/NC1.lean` | 135 | 100 | 5 |

- Build: every module rc=0 with 0 errors (final run 21:05Z); the only warnings are the 43
  "declaration uses 'sorry'", exactly the targets.
- Lint: `scripts/style_lint.py` gives 0 findings on the 6 files (the facade carries the three
  `set_option` lines because the lint requires them; O1's `FormulaArith.lean` facade lacks them).
- No `@[simp]`, no global attribute, no `native_decide`, no `axiom`; the only attribute is the
  non-simp `@[simps (config := { isSimp := false })]` on `Instr.ofPerm`.
- Mathlib imports, all in the cache: `Data.Fintype.Inv` and `GroupTheory.Perm.Cycle.Type` (already
  imported elsewhere in TCSlib); `Data.Finset.Dedup`, `Data.Fintype.Defs`, `Logic.Equiv.Basic`,
  `Algebra.BigOperators.Group.Finset.Basic` (new to these files).

## 2. Declarations

**Defs.** Structures `BranchingProgram.Instr` (`var`, `map0`, `map1`), `BranchingProgram` (`instrs`),
`BranchingProgramFamily` (`program`, `accept`). Instructions: `Instr.eval`/`Instr.eval_eq`;
`Instr.IsPermutation`/`Instr.isPermutation_iff`; `Instr.ofPerm` with simps readers `ofPerm_var`,
`ofPerm_map0`, `ofPerm_map1`; `Instr.isPermutation_ofPerm` (proved glue). Programs: `length`/
`length_eq`; `append` and `instance : Append`/`append_eq`, `append_instrs` (rfl); `yield` (a `foldl`)/
`yield_eq`; `IsPermutation`/`isPermutation_iff` (the C4 reader, `Iff.rfl`); `conj`/`conj_eq`;
`complementLast` (total, a match on `getLast?`)/`complementLast_eq`, case lemmas `complementLast_nil`,
`complementLast_concat`. Families: `BranchingProgramFamily.language`/`mem_language_iff`;
`IsPolyLength`/`isPolyLength_iff`; `IsPermutation`/`isPermutation_iff`. Classes: `Language.InBWBP`/
`Language.inBWBP_iff`; `Language.InPBP`/`Language.inPBP_iff`.

**Eval.** `Instr.stepWith` (push form, `Finset` sums over `univ.filter`)/`Instr.stepWith_apply`;
`evalWith` (a `foldl`)/`evalWith_eq`.

**Barrington.** `IsFiveCycle`/`isFiveCycle_iff` and `instance instDecidablePredIsFiveCycle`;
`FiveCycleRecognizes`/`fiveCycleRecognizes_iff` (defined as
`IsFiveCycle σ ∧ ∀ x, (A x → yield = σ) ∧ (¬A x → yield = id)`); `sigma1`/`sigma1_eq`;
`sigma2`/`sigma2_eq`. Conjugator chain: `conjugatorIndex`/`conjugatorIndex_eq` (first `k < 5` with
`(σ^k) 0 = i`, by `List.find?`); `conjugatorFun`/`conjugatorFun_eq`; `conjugatorTable`
(`List.ofFn conjugatorFun`)/`conjugatorTable_eq`, `getD_conjugatorTable`; `conjugator`
(`if h : Bijective (fun i => table.getD i 0) then ⟨lookup, Fintype.bijInv h, …⟩ else 1`) with case
readers `conjugator_apply_of_bijective`, `conjugator_of_not_bijective` and one private glue lemma
`getD_conjugatorTable_fun`. `commutatorProgram`/`commutatorProgram_eq` (the AND step
`P₁τ₁ ++ P₂τ₂ ++ P₁τ₁⁻¹ ++ P₂τ₂⁻¹`). `barrington`, by well-founded recursion on `sizeOf c` with an
automatic, real termination proof; seven case readers cover every input: `barrington_lit_true`,
`_lit_false`, `_node_true_nil`, `_node_false_nil`, `_node_singleton`, `_node_true_cons_cons`,
`_node_false_cons_cons`. The OR case is
`(commutatorProgram (fun ρ => (barrington c₁ ρ⁻¹).complementLast ρ⁻¹) (…c₂…) σ⁻¹).complementLast σ⁻¹`
(derivation in the docstring).

**BarringtonConverse.** `Instr.wire`/`Instr.wire_eq`; `wireComp`/`wireComp_eq`; `compTree`/
`compTree_nil`, `compTree_singleton`, `compTree_cons_cons` (well-founded recursion on length; real
`decreasing_by`); `toFormula` (`noncomputable`, via `Finset.toList`)/`toFormula_eq`;
`topDepth`/`topDepth_eq`.

**Targets** (`sorry` unless marked):

| Row | Declarations |
|---|---|
| C1 | `yield_append`, `yield_nil` |
| C2 | `yield_conj`, `length_conj`, `length_append` |
| C3 | `yield_complementLast`, `length_complementLast` |
| C4 | `isPermutation_iff` (**proved**), `IsPermutation.append`, `.conj`, `.complementLast`, `.bijective_yield` |
| C5 | `evalWith_nil`, `evalWith_append` |
| C6 | `Instr.stepWith_of_isPermutation` |
| C7 | `evalWith_rel` |
| C8 | `evalWith_single` |
| C9 | `isFiveCycle_sigma1`, `isFiveCycle_sigma2`, `isFiveCycle_commutator` |
| C10 | `conjugator_conj` |
| C11 | `FiveCycleRecognizes.conj` |
| C12 | `FiveCycleRecognizes.complementLast` |
| C13 | `barrington_recognizes` |
| C14 | `barrington_length_le`, `barrington_length_pos` |
| C15 | `isPermutation_barrington` |
| C16 | `barrington_yield_zero` |
| C17 | `Instr.wire_eval`, `Instr.depth_wire_le`, `Instr.maxFanin_wire_le` |
| C18 | `wireComp_eval`, `depth_wireComp_le` |
| C19 | `compTree_eval`, `depth_compTree_le`, `maxFanin_compTree_le` |
| C20 | `toFormula_eval` |
| C21 | `depth_toFormula_le`, `maxFanin_toFormula_le` |
| C22 | `BranchingProgram.exists_fiveCycleRecognizes_of_dagCircuit` |
| C23 | `Language.InNC.inPBP_five` |
| C24 | `Language.InBWBP.inNC_one` |
| C25 | `Language.inNC_one_iff_inBWBP`, `Language.inNC_one_iff_inPBP_five` |

Every target docstring has the formula, the r3 tag and anchor (or "Glue"), the deviations, and a
`**Proof sketch.**` naming the readers it will use.

## 3. Statement changes against r3 (none changes a meaning; no probe found an r3 statement false)

1. `sigma1`, `sigma2` are written `List.formPerm [0,1,2,3,4]` and `List.formPerm [0,2,4,3,1]`, not
   `c[…]`: `c[…]` lives in `Mathlib.GroupTheory.Perm.Cycle.Concrete`, which is not in the Mathlib
   cache fetched for this job (only Basic, Factors and Type under `Perm/Cycle/`); `c[l]` is
   `Cycle.formPerm (Cycle.ofList l)`, equal to `List.formPerm l`; the docstrings say so.
2. C7 bounds the index through the reader: `B.instrs[t]'(ht.trans_eq B.length_eq)` (`length` is
   foreign to Eval); binders are r3's.
3. C6 projects through the reader: `(ι.isPermutation_iff.1 hι).1` instead of `hι.1` (which would
   unfold the foreign `Instr.IsPermutation`).
4. Explicit binders because `autoImplicit` is false: `{σ τ}` implicit in C10–C13 and C16, `{c}` in
   C14 `barrington_length_le` and C16; `wireComp_eval` and `depth_wireComp_le` take `(i k) (x)`
   explicitly after the hypotheses, with `f` and `g` implicit.
5. `compTree` readers use the pattern `ι₁ :: ι₂ :: l`, split at `length / 2`.
6. C21 `topDepth` settled at `+3`, not r3's draft `+4` (§4).
7. Extra helpers beyond r3's list, each with readers or proved: `Instr.isPermutation_ofPerm`,
   `conjugatorIndex`, `conjugatorFun`, `conjugatorTable`, `commutatorProgram`, the `complementLast`
   case lemmas.
8. `conjugator` reads its map from a stored list (`conjugatorTable`): otherwise Barrington's nested
   conjugates are recomputed at every application and evaluation is exponential in the depth
   (depth-2 formula, `scratch.log`: build and evaluate from 608 ms and 2312 ms to 2–3 ms). C10 and the
   meaning are unchanged; `conjugator_apply_of_bijective` reads
   `conjugator σ τ i = conjugatorFun σ τ i`.

## 4. Constants settled (*(fix)*)

- **C19 keeps r3's bound `depth ≤ (⌈log₂ w⌉+2)·⌈log₂ l⌉ + 1`**: leaves have depth ≤ 1; each split adds
  `⌈log₂ w⌉ + 2` (`+clog+1` from `depth_balanced_le`, `+1` for the binary `∧` node); for `l ≥ 2` the
  halves are `⌊l/2⌋ ≤ ⌈l/2⌉`, and `⌈log₂⌈l/2⌉⌉ = ⌈log₂ l⌉ − 1` (`Nat.clog_of_two_le`).
- **C21: `topDepth w := w·⌈log₂ w⌉ + ⌈log₂ w⌉ + 3`**: with `T = K·clog l + 1`, the inner `⋀` adds
  `clog w + 1`; the outer `⋁` over at most `w^w` maps adds `clog|F| + 1 ≤ w·clog w + 1`, since
  `w^w ≤ (2^{clog w})^w`; r3's `+4` is valid but one level loose.
- Checks are `#eval`, not `decide` (P7): `compTree` and `Nat.clog` are well-founded recursion. XOR
  program: wire depths 4 against bound 7; formula depths [1,5,5,6] against bound 12. Sweep: C19 for
  `l ≤ 17`, `w ≤ 4`; C21 with the largest accepting set (all `w^w` maps) for `l ≤ 9` at `w ≤ 3` and
  `l ≤ 3` at `w = 4`. Minimum slack 0 for C19 (tight at `l ≤ 1`), at least 2 for C21.

## 5. Reader census

| Foreign definition | Reader (or MISSING + proposal) |
|---|---|
| `TreeCircuit.eval` (Basic:144) | `eval_lit` Basic:150; `eval_node_true_iff`/`_false_iff` Basic:155/163; `eval_node_true`/`_false` TreeDAG:126/132 |
| `TreeCircuit.depth` (Basic:176) | `depth_node` Basic:213, `maxDepth_nil`/`_cons`; literal MISSING, propose `depth_lit : (lit l).depth = 0` |
| `TreeCircuit.maxFanin` (Basic:194) | `maxFanin_node` Basic:223, `maxFaninL_nil`/`_cons`; literal MISSING, propose `maxFanin_lit` (= 0) |
| `TreeCircuit.size` (C24 sketch) | `size_node`, `size_succ_le_two_pow` Basic:313; literal MISSING, propose `size_lit` (= 1) |
| `Lit.eval` (Basic:110, a `@[simp] def`) | MISSING, propose `Lit.eval_eq : l.eval x = if l.sign then x l.idx else !x l.idx` |
| `TreeCircuit.balanced` (Combinators) | `balanced_eval`, `depth_balanced_le`, `maxFanin_balanced_le`, `size_balanced_le`, `balanced_nil`, `balanced_singleton` |
| `DAGCircuit.IsFaninTwo` (DAGCircuit:512) | `isFaninTwo_iff` DAGCircuit:520 |
| `DAGCircuit.IsWellFormed` (DAGCircuit:508) | MISSING, propose `isWellFormed_iff` (`Iff.rfl`) or a circuit-level `IsFaninTwo.isWellFormed`; C22's fill needs it for `toTree_*` |
| `DAGCircuit.eval`, `depth` | `eval_eq`, `depth_eq` :609 (read only in statements) |
| `DAGCircuit.toTree` (TreeDAG:404) | `toTree_eval` :594, `toTree_depth_le` :623, `toTree_maxFanin_le` :645 |
| `Language.InNC` (NCAC:55) | only through `inTreeNC_one` :194, `InTreeNC.inNC` :149, `inNC_one_iff` :229 |
| `Language.InTreeNC` (TreeNCAC) | MISSING, propose `Language.inTreeNC_iff` (C23 destructs it, C24 builds it) |
| `TreeCircuitFamily.HasFaninTwo`, `IsPolySize`, `HasPolylogDepth` (TreeNCAC) | MISSING, propose `hasFaninTwo_iff`, `isPolySize_iff`, `hasPolylogDepth_iff` |
| `TreeCircuitFamily.language` | `mem_language_iff` (TreeNCAC) |
| `BoolCircuit.clog_poly_le` | public (TreeNCAC) |

Between its own files every cross-file read goes through the Defs, Eval and Barrington readers. The
proved lemmas and definition bodies reduce only their own file's definitions (seals not run by the
sub-agent).

## 6. Overlap and reuse

Searches (`git grep … HEAD -- 'TCSlib/*.lean'`, sparse checkout):
`BranchingProgram|InBWBP|InPBP|IsFiveCycle|FiveCycle|conjugator|sigma1|sigma2|compTree|wireComp|topDepth|toFormula|barrington|Barrington|evalWith|complementLast|commutatorProgram|IsPolyLength|stepWith`;
`branching program`; `formPerm`, `Perm (Fin 5)`, `cycleType`, `IsConj`, `bijInv`, `composition
circuit`, `state vector`, `def yield`; the helper names `conjugatorIndex`, `conjugatorFun`,
`cycleIndex`, `getD_conjugatorTable`, `instDecidablePredIsFiveCycle`. No branching-program,
Barrington or permutation-program material exists; the only hits are `NDTM.stepWith` (different
namespace) and `Randomized.bpp_subset_sigma2` (no clash); "branching" hits are unrelated. Reused:
`TreeCircuit.balanced` (O1); Mathlib's `List.formPerm`, `cycleType`, `Fintype.bijInv`; `toTree`; in
the sketches `inTreeNC_one`, `InTreeNC.inNC`, `clog_poly_le`, `size_succ_le_two_pow`. No duplicated
material.

## 7. Probes (`/home/user/wt-bp/evidence/probes/`, final log `probes-final.log`)

All pass; every run under 1 min (heaviest P3b, 46 s, 5.5 GB).
- P1_YieldOrder (kernel `decide`): Bar89's p004-b001 example in BV14 order yields
  `formPerm [0,2,1,4,3]` exactly when `x₀ ∧ x₁` and `id` otherwise; the accepted yield equals
  `sigma2⁻¹*sigma1⁻¹*sigma2*sigma1`. The p001-b002 XOR program (variables 6, 3, 7) yields the swap iff
  `x₇ ⊕ ¬x₄ ⊕ x₈`, on all 256 inputs (`decide +kernel`). `yield_append`'s direction holds and the
  reverse fails.
- P2_Commutator: program-order commutator `formPerm [0,2,1,4,3]`; right-to-left `formPerm [0,3,2,4,1]`;
  they differ. `IsFiveCycle` of all three by kernel `decide` (the commutator needs `decide +kernel`;
  the C9 sketch says so).
- P3_Conjugator: `#eval` shows it computable (`conjugator sigma1 sigma2` gives `[0,2,4,3,1]`); kernel
  `decide`: the 24 explicit `formPerm [0,a,b,c,d]` are distinct five-cycles and every five-cycle of
  S₅ is one of them; `#eval`: C10 holds and the table is bijective on all 576 pairs.
- P3b_ConjugatorAll: C10 on all 24×24 pairs by kernel `decide +kernel`, 46 s.
- P4_ComplementLast (kernel `decide`): C3's `σ.symm ∘ yield`; yield `id` on A and `ρ⁻¹` off A; `ρ⁻¹`
  a five-cycle; length unchanged; only the last instruction changes; the empty program unchanged.
- P5a/b/c_Barrington (`#eval`): `x₀∧x₁`, `x₀∨¬x₁`, true, false, fan-in-1 `∨[¬x₁]`, two depth-2 XORs,
  a depth-4 formula with a nested constant; for all 24 output five-cycles: C13 recognition, the C16
  `σ 0` reading, C14 `0 < length ≤ 4^depth`, C15 bijective maps. Lengths 4, 4, 1, 1, 1, 16, 16, 40.
  With a transposition as output the AND is not recognized (why C13 needs `IsFiveCycle`).
- P6_Host (kernel `decide`): C8 on a width-3 non-permutation program, all inputs and start states; the
  push form sums (a constant map collects mass 3); C6 as stated (with `Equiv.ofBijective`) on
  `Instr.ofPerm 0 sigma1 sigma2`.
- P7_Converse (`#eval`): `toFormula` is noncomputable, so a probe-local copy `topFormula` of its body
  taking the accepting set as a list was checked: the wires equal `decide (yield x i = j)` on all 256
  inputs and the formula equals `decide (yield ∈ F)` for four accepting sets; fan-in ≤ 2; depth sweep
  in §4.
- P0_Axioms (extra): every definition and reader depends only on `propext`, `Classical.choice`,
  `Quot.sound`; no `sorryAx`.

## 8. Definitions citing a `sorry` target

None (`conjugator` uses `Fintype.bijInv` under a `dite`; `barrington` and `compTree` have real
termination proofs; P0 confirms).

## Notes

- The first, unsplit P5 held the shared Lean lock for 13 min, before the conjugator fix; later runs
  were capped by the guarded runner.
- `evidence/probes/Scratch2.lean` (timing evidence) is in the worktree; the unsplit P5 is kept as
  `P5_Barrington.unsplit.lean.txt`.
- No file touched outside the six files, the probes and this evidence folder.
