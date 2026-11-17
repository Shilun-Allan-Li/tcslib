/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Logic.Equiv.Basic
import TCSlib.Complexity.BranchingPrograms.Defs

/-!
# The branching-program host `evalWith`

A program run on a *state vector* `V : Fin w → α` instead of a single state: one instruction
sends `V` to the vector whose coordinate `i` collects, through a selector `sel` applied to the
instruction's input, the sums of the entries that the `0`-branch and the `1`-branch send to `i`
(the push form).  Folding this step over the instructions in program order is the host
`BranchingProgram.evalWith`, generic in the selector `sel : β → α → α → α` and in the value type
`α` (an additive commutative monoid).  It is row H18 of the host registry
(`machine-library-design.md` §14).  Its consumers are the Boolean semantics (C8: a one-hot state
stays one-hot at the yield, for every program) and GSW's homomorphic evaluation of a permutation
program, where `α` is a ciphertext type and `sel` the homomorphic selector.

The push form needs no inverse, so the host is total and computable on the general model of
[Bar89, §1]; for a permutation instruction each sum has exactly one term and the step is
[BV14, Eq. (4)]'s pull form (C6).

## Main definitions

* `BranchingProgram.Instr.stepWith` — one instruction on a state vector (push form).
* `BranchingProgram.evalWith` — the host: `stepWith` folded in program order.

## Main results

All are statements of the 6a statement phase (targets admitted with `sorry`), except the readers.

* `BranchingProgram.evalWith_nil`, `evalWith_append` — readers of the fold (C5).
* `BranchingProgram.Instr.stepWith_of_isPermutation` — BV14's pull form for a permutation
  instruction (C6).
* `BranchingProgram.evalWith_rel` — the step-indexed relational host lemma (C7).
* `BranchingProgram.evalWith_single` — Boolean semantics for general maps (C8).

## References

* [Bar89] D. A. Mix Barrington, *Bounded-width polynomial-size branching programs recognize
  exactly those languages in NC¹*, J. Comput. System Sci. 38(1):150–164, 1989.
* [BV14] Z. Brakerski, V. Vaikuntanathan, *Lattice-based FHE as secure as PKE*, ITCS 2014,
  pp. 1–12; IACR ePrint 2013/541.
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BranchingProgram

open Finset

variable {w n : ℕ} {α α' β β' : Type*}

/-- One instruction on a state vector, push form: coordinate `i` of the new vector is
`sel (inp ι.var) (∑ j ∈ univ.filter (ι.map0 · = i), V j) (∑ j ∈ univ.filter (ι.map1 · = i), V j)`,
the selector applied to the instruction's input and to the sums of the entries that the
`0`-branch and the `1`-branch send to `i`.  Host step; glue generalizing
[BV14, Eq. (4), p013-b002] from permutations to general maps. -/
def Instr.stepWith [AddCommMonoid α] (sel : β → α → α → α) (inp : Fin n → β) (ι : Instr w n)
    (V : Fin w → α) : Fin w → α :=
  fun i => sel (inp ι.var) (∑ j ∈ univ.filter (fun j => ι.map0 j = i), V j)
    (∑ j ∈ univ.filter (fun j => ι.map1 j = i), V j)

/-- Reader of `Instr.stepWith`: `ι.stepWith sel inp V i =
sel (inp ι.var) (∑ j ∈ univ.filter (ι.map0 · = i), V j) (∑ j ∈ univ.filter (ι.map1 · = i), V j)`.
-/
theorem Instr.stepWith_apply [AddCommMonoid α] (sel : β → α → α → α) (inp : Fin n → β)
    (ι : Instr w n) (V : Fin w → α) (i : Fin w) :
    ι.stepWith sel inp V i = sel (inp ι.var) (∑ j ∈ univ.filter (fun j => ι.map0 j = i), V j)
      (∑ j ∈ univ.filter (fun j => ι.map1 j = i), V j) := rfl

/-- **The branching-program host** (registry row H18): fold `Instr.stepWith sel inp` over the
instructions in program order, starting from `V`,
`B.evalWith sel inp V = B.instrs.foldl (fun U ι => ι.stepWith sel inp U) V`.  Generic in the
selector `sel` and the value type `α`; its consumers are the Boolean semantics (C8) and GSW's
homomorphic evaluation (G2).  Glue generalizing [BV14, Eq. (4), p013-b002]. -/
def evalWith [AddCommMonoid α] (sel : β → α → α → α) (inp : Fin n → β)
    (B : BranchingProgram w n) (V : Fin w → α) : Fin w → α :=
  B.instrs.foldl (fun U ι => ι.stepWith sel inp U) V

/-- Reader of `evalWith`: `B.evalWith sel inp V = B.instrs.foldl (fun U ι => ι.stepWith sel inp U)
V`. -/
theorem evalWith_eq [AddCommMonoid α] (sel : β → α → α → α) (inp : Fin n → β)
    (B : BranchingProgram w n) (V : Fin w → α) :
    B.evalWith sel inp V = B.instrs.foldl (fun U ι => ι.stepWith sel inp U) V := rfl

/-! ### Targets C5–C8 -/

/-- **C5.** The empty program leaves the state unchanged:
`(⟨[]⟩ : BranchingProgram w n).evalWith sel inp V = V`.  Glue (reader of the fold).

**Proof sketch.** `evalWith_eq` and `List.foldl_nil`. -/
theorem evalWith_nil [AddCommMonoid α] (sel : β → α → α → α) (inp : Fin n → β)
    (V : Fin w → α) : (⟨[]⟩ : BranchingProgram w n).evalWith sel inp V = V := by
  sorry

/-- **C5.** The host runs a concatenation in program order:
`(B₁ ++ B₂).evalWith sel inp V = B₂.evalWith sel inp (B₁.evalWith sel inp V)`.  Glue (reader of
the fold).

**Proof sketch.** `evalWith_eq`, the reader `append_instrs` of `++`, and `List.foldl_append`. -/
theorem evalWith_append [AddCommMonoid α] (sel : β → α → α → α) (inp : Fin n → β)
    (B₁ B₂ : BranchingProgram w n) (V : Fin w → α) :
    (B₁ ++ B₂).evalWith sel inp V = B₂.evalWith sel inp (B₁.evalWith sel inp V) := by
  sorry

/-- **C6.** For a permutation instruction each sum of the push form has exactly one term, and the
step is BV14's pull form: `ι.stepWith sel inp V i = sel (inp ι.var) (V (σ₀⁻¹ i)) (V (σ₁⁻¹ i))`
with `σ₀ = Equiv.ofBijective ι.map0 _`, `σ₁ = Equiv.ofBijective ι.map1 _`
[BV14, Eq. (4), p013-b002: `v_t[i] := v_{t−1}[σ_{t,0}⁻¹(i)]·(1 − x) + v_{t−1}[σ_{t,1}⁻¹(i)]·x`].
Deviation: BV14's selector is the arithmetic `(1 − x)·u + x·v`; here it is the abstract `sel`.

**Proof sketch.** Rewrite with `Instr.stepWith_apply`.  With `e = Equiv.ofBijective ι.map0 _`
(bijective by `Instr.isPermutation_iff`), `ι.map0 j = i ↔ j = e.symm i`
(`Equiv.apply_eq_iff_eq_symm_apply`), so the filter is the singleton `{e.symm i}`
(`Finset.filter_eq'`) and the sum is `V (e.symm i)` (`Finset.sum_singleton`); the same for
`map1`. -/
theorem Instr.stepWith_of_isPermutation [AddCommMonoid α] (sel : β → α → α → α)
    (inp : Fin n → β) {ι : Instr w n} (hι : ι.IsPermutation) (V : Fin w → α) (i : Fin w) :
    ι.stepWith sel inp V i =
      sel (inp ι.var) (V ((Equiv.ofBijective _ (ι.isPermutation_iff.1 hι).1).symm i))
        (V ((Equiv.ofBijective _ (ι.isPermutation_iff.1 hι).2).symm i)) := by
  sorry

/-- **C7.** **Step-indexed relational host lemma**: two runs of the host on the same program,
possibly with different selectors, inputs and value types, that are related by `R 0` at the
start and whose relation is carried from `R t` to `R (t + 1)` by every instruction
`B.instrs[t]`, end related by `R B.length`:
`R 0 V V' → (∀ t < B.length, ∀ U U', R t U U' → R (t + 1) (ι_t.stepWith sel inp U)
(ι_t.stepWith sel' inp' U')) → R B.length (B.evalWith sel inp V) (B.evalWith sel' inp' V')`.
Glue; GSW carries its noise bound `t·2Nβ` in the index.

**Proof sketch.** By `evalWith_eq` both sides are left folds over `B.instrs`.  Prove, by
induction on `k ≤ B.instrs.length`, that the folds over `B.instrs.take k` are related by `R k`:
the step `k → k + 1` uses `List.take_succ`, `List.foldl_append` and `hstep k` with
`B.instrs[k]`; at `k = B.instrs.length` use `List.take_length` and `length_eq`. -/
theorem evalWith_rel [AddCommMonoid α] [AddCommMonoid α'] (sel : β → α → α → α)
    (sel' : β' → α' → α' → α') (inp : Fin n → β) (inp' : Fin n → β')
    (B : BranchingProgram w n) (R : ℕ → (Fin w → α) → (Fin w → α') → Prop) (V : Fin w → α)
    (V' : Fin w → α') (h0 : R 0 V V')
    (hstep : ∀ t (ht : t < B.length) (U : Fin w → α) (U' : Fin w → α'), R t U U' →
      R (t + 1) ((B.instrs[t]'(ht.trans_eq B.length_eq)).stepWith sel inp U)
        ((B.instrs[t]'(ht.trans_eq B.length_eq)).stepWith sel' inp' U')) :
    R B.length (B.evalWith sel inp V) (B.evalWith sel' inp' V') := by
  sorry

/-- **C8.** Boolean semantics for **general** maps: with values in `ℕ` and the selector
`sel b u v = if b then v else u`, the host started at the one-hot vector of `s` ends at the
one-hot vector of `B.yield x s`:
`B.evalWith (fun b u v => if b then v else u) x (Pi.single s 1) = Pi.single (B.yield x s) 1`
[BV14, Eq. (4), p013-b002, generalized from permutations; Bar89, §1, p001-b002].
Deviation: BV14 states Eq. (4) for permutations; the push form makes it hold for every map.

**Proof sketch.** One step: for every instruction `ι`,
`ι.stepWith sel x (Pi.single s 1) = Pi.single (ι.eval x s) 1`; at coordinate `i` the `0`-sum is
`∑ j ∈ univ.filter (ι.map0 · = i), Pi.single s 1 j = if ι.map0 s = i then 1 else 0`
(`Finset.sum_filter`, `Pi.single_apply`, `Finset.sum_ite_eq'`), likewise the `1`-sum, and the
selector picks the branch of `x ι.var` as `Instr.eval_eq` does.  Then induct on `B.instrs` with
the yield's fold generalized to a start map `f` (claim: the host fold from `Pi.single (f s) 1`
is `Pi.single (fold f s) 1`), using `evalWith_eq` and `yield_eq`. -/
theorem evalWith_single (B : BranchingProgram w n) (x : Fin n → Bool) (s : Fin w) :
    B.evalWith (fun b (u v : ℕ) => if b then v else u) x (Pi.single s 1) =
      Pi.single (B.yield x s) 1 := by
  sorry

end BranchingProgram
