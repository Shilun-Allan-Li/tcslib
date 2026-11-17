/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Mathlib.Data.Fintype.Inv
import Mathlib.GroupTheory.Perm.Cycle.Type
import TCSlib.Complexity.BranchingPrograms.Defs
import TCSlib.Complexity.CircuitComplexity.Basic

/-!
# Barrington's Theorem 1: formulas to width-5 permutation programs

[Bar89, Thm 1]: a fan-in-2 AND/OR formula of depth `d` over literals is *five-cycle recognized*
by a width-5 permutation branching program of length at most `4^d`.  The construction
`BranchingProgram.barrington` is computable (P6-Q13): Lemma 1's conjugator is the explicit
`θ (σ^k 0) = τ^k 0`, and the OR case goes through Lemma 2 by De Morgan.

## Main definitions

* `BranchingProgram.IsFiveCycle`, `BranchingProgram.FiveCycleRecognizes` — five-cycles and
  five-cycle recognition [Bar89, §3].
* `BranchingProgram.sigma1`, `sigma2` — Lemma 3's five-cycles `(12345)`, `(13542)`, 0-based.
* `BranchingProgram.conjugator` — Lemma 1's explicit conjugator (with `conjugatorIndex`,
  `conjugatorFun`, `conjugatorTable`).
* `BranchingProgram.commutatorProgram` — the AND step `B₁ B₂ B₁' B₂'` of Thm 1's proof.
* `BranchingProgram.barrington` — Barrington's program for a formula and an output.

## Main results

All are statements of the 6a statement phase (targets admitted with `sorry`), except the readers.

* `isFiveCycle_sigma1`, `isFiveCycle_sigma2`, `isFiveCycle_commutator` — Lemma 3 (C9).
* `conjugator_conj` — the conjugator conjugates (C10).
* `FiveCycleRecognizes.conj`, `FiveCycleRecognizes.complementLast` — Lemmas 1 and 2 (C11, C12).
* `barrington_recognizes`, `barrington_length_le`, `barrington_length_pos`,
  `isPermutation_barrington`, `barrington_yield_zero` — Thm 1 (C13–C16).

## Conventions and deviations

* **Orders.** Instructions follow BV14's order (`map0` on `0`) and programs compose in program
  order (`Defs.lean`).  Bar89's commutator `σ₁σ₂σ₁⁻¹σ₂⁻¹`, read left to right, is the Mathlib
  product `sigma2⁻¹ * sigma1⁻¹ * sigma2 * sigma1`.  That is `(13254)` in Bar89's one-based cycle
  notation, whose zero-based form `(0 2 1 4 3)`, the cycle `0 ↦ 2 ↦ 1 ↦ 4 ↦ 3 ↦ 0`, is what the
  code implements; the right-to-left reading gives `(14352)` instead (r3 §H3.6).
* **Cycle notation.** `sigma1`, `sigma2` are written `List.formPerm [0, 1, 2, 3, 4]` and
  `List.formPerm [0, 2, 4, 3, 1]`: Mathlib's `c[…]` notation lives in
  `Mathlib.GroupTheory.Perm.Cycle.Concrete`, which is not in the pinned Mathlib cache;
  `c[l]` is `Cycle.formPerm (Cycle.ofList l)`, which is `List.formPerm l` (`Cycle.formPerm_coe`).
* **Constants and literals.** [Bar89, Thm 1] allows "inputs and negated inputs"; `TreeCircuit`
  also has constant nodes `node true []`, `node false []` and fan-in-1 nodes, which get their own
  trivial cases (the ingest's transcription note).  A constant reads variable `0`, hence
  `[NeZero n]`.
* **OR gates.** "Appeal to Lemma 2" is De Morgan through `complementLast` (see `barrington`).
* **Fan-in.** `barrington` is total; at a node of fan-in above 2 it uses the first two children
  only.  The theorems assume `c.maxFanin ≤ 2`, where nothing is dropped.
* **Reading.** BV14 reads the state reached from the start state; here the start state is `0`
  and the accepting reading is `σ 0` (C16).

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

open BoolCircuit Equiv

variable {n : ℕ}

/-! ### Five-cycles and five-cycle recognition -/

/-- `σ` is a five-cycle: its cycle type is `{5}`, `σ.cycleType = {5}` (decidable)
[Bar89, §3, p003-b001]. -/
def IsFiveCycle (σ : Perm (Fin 5)) : Prop :=
  σ.cycleType = {5}

/-- Reader of `IsFiveCycle`: `IsFiveCycle σ ↔ σ.cycleType = {5}`. -/
theorem isFiveCycle_iff (σ : Perm (Fin 5)) : IsFiveCycle σ ↔ σ.cycleType = {5} := Iff.rfl

instance instDecidablePredIsFiveCycle : DecidablePred IsFiveCycle := fun σ =>
  inferInstanceAs (Decidable (σ.cycleType = {5}))

/-- `B` five-cycle recognizes `A` with output `σ`: `σ` is a five-cycle, and `B.yield x` is `σ` on
`A` and the identity off `A`,
`IsFiveCycle σ ∧ ∀ x, (A x → B.yield x = σ) ∧ (¬ A x → B.yield x = id)`
[Bar89, §3, p003-b001]. -/
def FiveCycleRecognizes (B : BranchingProgram 5 n) (A : (Fin n → Bool) → Prop)
    (σ : Perm (Fin 5)) : Prop :=
  IsFiveCycle σ ∧ ∀ x, (A x → B.yield x = σ) ∧ (¬ A x → B.yield x = id)

/-- Reader of `FiveCycleRecognizes`: `FiveCycleRecognizes B A σ ↔
IsFiveCycle σ ∧ ∀ x, (A x → B.yield x = σ) ∧ (¬ A x → B.yield x = id)`. -/
theorem fiveCycleRecognizes_iff (B : BranchingProgram 5 n) (A : (Fin n → Bool) → Prop)
    (σ : Perm (Fin 5)) :
    FiveCycleRecognizes B A σ ↔
      IsFiveCycle σ ∧ ∀ x, (A x → B.yield x = σ) ∧ (¬ A x → B.yield x = id) :=
  Iff.rfl

/-! ### Lemma 3's five-cycles -/

/-- Bar89's `(12345)`, 0-based: the five-cycle `0 ↦ 1 ↦ 2 ↦ 3 ↦ 4 ↦ 0`, Mathlib's `c[0,1,2,3,4]`,
written `sigma1 = List.formPerm [0, 1, 2, 3, 4]` [Bar89, Lemma 3, p003-b005]. -/
def sigma1 : Perm (Fin 5) :=
  List.formPerm [0, 1, 2, 3, 4]

/-- Reader of `sigma1`: `sigma1 = List.formPerm [0, 1, 2, 3, 4]`. -/
theorem sigma1_eq : sigma1 = List.formPerm [0, 1, 2, 3, 4] := rfl

/-- Bar89's `(13542)`, 0-based: the five-cycle `0 ↦ 2 ↦ 4 ↦ 3 ↦ 1 ↦ 0`, Mathlib's `c[0,2,4,3,1]`,
written `sigma2 = List.formPerm [0, 2, 4, 3, 1]` [Bar89, Lemma 3, p003-b005]. -/
def sigma2 : Perm (Fin 5) :=
  List.formPerm [0, 2, 4, 3, 1]

/-- Reader of `sigma2`: `sigma2 = List.formPerm [0, 2, 4, 3, 1]`. -/
theorem sigma2_eq : sigma2 = List.formPerm [0, 2, 4, 3, 1] := rfl

/-! ### Lemma 1's explicit conjugator -/

/-- The position of `i` on the orbit of `0` under `σ`: the first `k < 5` with `(σ ^ k) 0 = i`, or
`0` if there is none,
`conjugatorIndex σ i = ((List.range 5).find? fun k => (σ ^ k) 0 = i).getD 0`.  Glue for
[Bar89, Lemma 1 proof, p003-b003]; for a five-cycle every `i` is found. -/
def conjugatorIndex (σ : Perm (Fin 5)) (i : Fin 5) : ℕ :=
  ((List.range 5).find? fun k => (σ ^ k) 0 = i).getD 0

/-- Reader of `conjugatorIndex`:
`conjugatorIndex σ i = ((List.range 5).find? fun k => (σ ^ k) 0 = i).getD 0`. -/
theorem conjugatorIndex_eq (σ : Perm (Fin 5)) (i : Fin 5) :
    conjugatorIndex σ i = ((List.range 5).find? fun k => (σ ^ k) 0 = i).getD 0 := rfl

/-- The conjugating map `σ^k 0 ↦ τ^k 0`: `conjugatorFun σ τ i = (τ ^ conjugatorIndex σ i) 0`
[Bar89, Lemma 1 proof, p003-b003]. -/
def conjugatorFun (σ τ : Perm (Fin 5)) (i : Fin 5) : Fin 5 :=
  (τ ^ conjugatorIndex σ i) 0

/-- Reader of `conjugatorFun`: `conjugatorFun σ τ i = (τ ^ conjugatorIndex σ i) 0`. -/
theorem conjugatorFun_eq (σ τ : Perm (Fin 5)) (i : Fin 5) :
    conjugatorFun σ τ i = (τ ^ conjugatorIndex σ i) 0 := rfl

/-- The values of `conjugatorFun σ τ` stored as a list:
`conjugatorTable σ τ = List.ofFn (conjugatorFun σ τ) = [f 0, f 1, f 2, f 3, f 4]` with
`f = conjugatorFun σ τ`.  `conjugator` reads its map from this list (`getD_conjugatorTable`), so
that evaluating a conjugator computes the five values once and later applications are lookups;
without it, Barrington's nested conjugates cost time exponential in the depth when evaluated.
Glue for [Bar89, Lemma 1 proof, p003-b003]. -/
def conjugatorTable (σ τ : Perm (Fin 5)) : List (Fin 5) :=
  List.ofFn (conjugatorFun σ τ)

/-- Reader of `conjugatorTable`: `conjugatorTable σ τ = List.ofFn (conjugatorFun σ τ)`. -/
theorem conjugatorTable_eq (σ τ : Perm (Fin 5)) :
    conjugatorTable σ τ = List.ofFn (conjugatorFun σ τ) := rfl

/-- Looking up the table gives the map: `(conjugatorTable σ τ).getD i 0 = conjugatorFun σ τ i`. -/
theorem getD_conjugatorTable (σ τ : Perm (Fin 5)) (i : Fin 5) :
    (conjugatorTable σ τ).getD i 0 = conjugatorFun σ τ i := by
  rw [conjugatorTable_eq, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp

/-- The explicit conjugator of two five-cycles: the permutation `θ` with `θ (σ^k 0) = τ^k 0`
for `k < 5`, i.e. `conjugatorFun σ τ` (read from the list `conjugatorTable σ τ`) packaged with
its computable inverse (`Fintype.bijInv`) when it is a bijection, and the identity otherwise
[Bar89, Lemma 1 proof, p003-b003: "there exists some permutation `θ` with `τ = θσθ⁻¹`"].
Computable (P6-Q13); it is not `Equiv.ofBijective`, whose inverse is noncomputable.  For
five-cycles `σ`, `τ` the map is a bijection and `θ * σ * θ⁻¹ = τ` (C10). -/
def conjugator (σ τ : Perm (Fin 5)) : Perm (Fin 5) :=
  let t := conjugatorTable σ τ
  if h : Function.Bijective (fun i : Fin 5 => t.getD i 0) then
    { toFun := fun i => t.getD i 0
      invFun := Fintype.bijInv h
      left_inv := Fintype.leftInverse_bijInv h
      right_inv := Fintype.rightInverse_bijInv h }
  else 1

/-- The looked-up map is `conjugatorFun σ τ`:
`(fun i => (conjugatorTable σ τ).getD i 0) = conjugatorFun σ τ`.  Glue. -/
private theorem getD_conjugatorTable_fun (σ τ : Perm (Fin 5)) :
    (fun i : Fin 5 => (conjugatorTable σ τ).getD i 0) = conjugatorFun σ τ :=
  funext (getD_conjugatorTable σ τ)

/-- Reader of `conjugator`, bijective case: if `conjugatorFun σ τ` is a bijection then
`conjugator σ τ i = conjugatorFun σ τ i`. -/
theorem conjugator_apply_of_bijective {σ τ : Perm (Fin 5)}
    (h : Function.Bijective (conjugatorFun σ τ)) (i : Fin 5) :
    conjugator σ τ i = conjugatorFun σ τ i := by
  have h' : Function.Bijective (fun i : Fin 5 => (conjugatorTable σ τ).getD i 0) := by
    rw [getD_conjugatorTable_fun]; exact h
  unfold conjugator
  rw [dif_pos h']
  exact getD_conjugatorTable σ τ i

/-- Reader of `conjugator`, degenerate case: if `conjugatorFun σ τ` is not a bijection then
`conjugator σ τ = 1`. -/
theorem conjugator_of_not_bijective {σ τ : Perm (Fin 5)}
    (h : ¬ Function.Bijective (conjugatorFun σ τ)) : conjugator σ τ = 1 := by
  have h' : ¬ Function.Bijective (fun i : Fin 5 => (conjugatorTable σ τ).getD i 0) := by
    rw [getD_conjugatorTable_fun]; exact h
  unfold conjugator
  rw [dif_neg h']

/-! ### Barrington's construction -/

/-- The AND step of [Bar89, Thm 1 proof, p004-b002] for output `σ`: with
`θ = conjugator (sigma2⁻¹ * sigma1⁻¹ * sigma2 * sigma1) σ` and `τᵢ = θ * sigmaᵢ * θ⁻¹`,
`commutatorProgram P₁ P₂ σ = P₁ τ₁ ++ P₂ τ₂ ++ P₁ τ₁⁻¹ ++ P₂ τ₂⁻¹`, Bar89's `B₁B₂B₁'B₂'`.
If `P₁ ρ`, `P₂ ρ` recognize `A₁`, `A₂` with output `ρ`, it yields `τ₂⁻¹ * τ₁⁻¹ * τ₂ * τ₁ =
θ * (sigma2⁻¹ * sigma1⁻¹ * sigma2 * sigma1) * θ⁻¹ = σ` on `A₁ ∩ A₂` and the identity elsewhere.
Deviation: Bar89 takes `B₁, B₂` with outputs `σ₁, σ₂` and conjugates the result (Lemma 1); here
the outputs `τᵢ` are conjugated in advance, which gives output `σ` directly. -/
def commutatorProgram (P₁ P₂ : Perm (Fin 5) → BranchingProgram 5 n) (σ : Perm (Fin 5)) :
    BranchingProgram 5 n :=
  let θ := conjugator (sigma2⁻¹ * sigma1⁻¹ * sigma2 * sigma1) σ
  P₁ (θ * sigma1 * θ⁻¹) ++ P₂ (θ * sigma2 * θ⁻¹) ++ P₁ (θ * sigma1 * θ⁻¹)⁻¹ ++
    P₂ (θ * sigma2 * θ⁻¹)⁻¹

/-- Reader of `commutatorProgram`: with `θ = conjugator (sigma2⁻¹ * sigma1⁻¹ * sigma2 * sigma1) σ`,
`commutatorProgram P₁ P₂ σ = P₁ (θ * sigma1 * θ⁻¹) ++ P₂ (θ * sigma2 * θ⁻¹) ++
P₁ (θ * sigma1 * θ⁻¹)⁻¹ ++ P₂ (θ * sigma2 * θ⁻¹)⁻¹`. -/
theorem commutatorProgram_eq (P₁ P₂ : Perm (Fin 5) → BranchingProgram 5 n) (σ : Perm (Fin 5)) :
    commutatorProgram P₁ P₂ σ =
      P₁ (conjugator (sigma2⁻¹ * sigma1⁻¹ * sigma2 * sigma1) σ * sigma1 *
          (conjugator (sigma2⁻¹ * sigma1⁻¹ * sigma2 * sigma1) σ)⁻¹) ++
        P₂ (conjugator (sigma2⁻¹ * sigma1⁻¹ * sigma2 * sigma1) σ * sigma2 *
          (conjugator (sigma2⁻¹ * sigma1⁻¹ * sigma2 * sigma1) σ)⁻¹) ++
        P₁ (conjugator (sigma2⁻¹ * sigma1⁻¹ * sigma2 * sigma1) σ * sigma1 *
          (conjugator (sigma2⁻¹ * sigma1⁻¹ * sigma2 * sigma1) σ)⁻¹)⁻¹ ++
        P₂ (conjugator (sigma2⁻¹ * sigma1⁻¹ * sigma2 * sigma1) σ * sigma2 *
          (conjugator (sigma2⁻¹ * sigma1⁻¹ * sigma2 * sigma1) σ)⁻¹)⁻¹ := rfl

/-- Barrington's program for a formula `c` with output `σ` [Bar89, Thm 1 proof, p004-b002;
BV14, Thm 3.5, p014-b001], by recursion on `c` with the output generalized:
- the literal `x_i` gives `⟨i, 1, σ⟩` and `¬x_i` gives `⟨i, σ, 1⟩` (BV14's order: `map0` first);
- the constant `node true []` (true) gives `⟨0, σ, σ⟩`, and `node false []` (false) gives
  `⟨0, 1, 1⟩`; both read variable `0`, hence `[NeZero n]`;
- a fan-in-1 node gives its child's program;
- `node true (c₁ :: c₂ :: _)` (`∧`) gives `commutatorProgram (barrington c₁) (barrington c₂) σ`:
  the children with outputs `τ₁, τ₂, τ₁⁻¹, τ₂⁻¹`, `τᵢ = θ * sigmaᵢ * θ⁻¹`, where `θ` conjugates the
  commutator `sigma2⁻¹ * sigma1⁻¹ * sigma2 * sigma1` to `σ`;
- `node false (c₁ :: c₂ :: _)` (`∨`) is De Morgan through Lemma 2 (`complementLast`).
  *Derivation.* If `B` recognizes `A` with output `ρ`, then `B.complementLast ρ` yields
  `ρ⁻¹ ∘ B(x)`: the identity on `A` and `ρ⁻¹` off it, so it recognizes `¬A` with output `ρ⁻¹`
  (C12).  Hence `N c μ := (barrington c μ⁻¹).complementLast μ⁻¹` recognizes `¬c` with output `μ`.
  The AND step on `N c₁`, `N c₂` with output `σ⁻¹` recognizes `¬c₁ ∧ ¬c₂` with output `σ⁻¹`;
  applying `complementLast σ⁻¹` gives `¬(¬c₁ ∧ ¬c₂) = c₁ ∨ c₂` with output `(σ⁻¹)⁻¹ = σ`.  Lemma 2
  keeps lengths, so the length stays `4 · 4^(d−1) = 4^d`.
Computable (P6-Q13); defined by well-founded recursion on `sizeOf c`, so it is evaluated by
`#eval`, not by the kernel.  At a node of fan-in above 2 only the first two children are used:
the theorems assume `c.maxFanin ≤ 2`, where nothing is dropped. -/
def barrington [NeZero n] : TreeCircuit n → Perm (Fin 5) → BranchingProgram 5 n
  | .lit ⟨i, true⟩, σ => ⟨[Instr.ofPerm i 1 σ]⟩
  | .lit ⟨i, false⟩, σ => ⟨[Instr.ofPerm i σ 1]⟩
  | .node true [], σ => ⟨[Instr.ofPerm 0 σ σ]⟩
  | .node false [], _ => ⟨[Instr.ofPerm 0 1 1]⟩
  | .node _ [c], σ => barrington c σ
  | .node true (c₁ :: c₂ :: _), σ =>
      commutatorProgram (fun ρ => barrington c₁ ρ) (fun ρ => barrington c₂ ρ) σ
  | .node false (c₁ :: c₂ :: _), σ =>
      (commutatorProgram (fun ρ => (barrington c₁ ρ⁻¹).complementLast ρ⁻¹)
        (fun ρ => (barrington c₂ ρ⁻¹).complementLast ρ⁻¹) σ⁻¹).complementLast σ⁻¹
termination_by c => sizeOf c

section Readers

variable [NeZero n]

/-- Reader of `barrington`, positive literal: `barrington (.lit ⟨i, true⟩) σ =
⟨[Instr.ofPerm i 1 σ]⟩`. -/
theorem barrington_lit_true (i : Fin n) (σ : Perm (Fin 5)) :
    barrington (.lit ⟨i, true⟩) σ = ⟨[Instr.ofPerm i 1 σ]⟩ := by
  rw [barrington]

/-- Reader of `barrington`, negative literal: `barrington (.lit ⟨i, false⟩) σ =
⟨[Instr.ofPerm i σ 1]⟩`. -/
theorem barrington_lit_false (i : Fin n) (σ : Perm (Fin 5)) :
    barrington (.lit ⟨i, false⟩) σ = ⟨[Instr.ofPerm i σ 1]⟩ := by
  rw [barrington]

/-- Reader of `barrington`, the constant true: `barrington (.node true []) σ =
⟨[Instr.ofPerm 0 σ σ]⟩`. -/
theorem barrington_node_true_nil (σ : Perm (Fin 5)) :
    barrington (.node true [] : TreeCircuit n) σ = ⟨[Instr.ofPerm 0 σ σ]⟩ := by
  rw [barrington]

/-- Reader of `barrington`, the constant false: `barrington (.node false []) σ =
⟨[Instr.ofPerm 0 1 1]⟩`. -/
theorem barrington_node_false_nil (σ : Perm (Fin 5)) :
    barrington (.node false [] : TreeCircuit n) σ = ⟨[Instr.ofPerm 0 1 1]⟩ := by
  rw [barrington]

/-- Reader of `barrington`, fan-in 1: `barrington (.node b [c]) σ = barrington c σ`. -/
theorem barrington_node_singleton (b : Bool) (c : TreeCircuit n) (σ : Perm (Fin 5)) :
    barrington (.node b [c]) σ = barrington c σ := by
  rw [barrington]

/-- Reader of `barrington`, `∧` node: `barrington (.node true (c₁ :: c₂ :: cs)) σ =
commutatorProgram (fun ρ => barrington c₁ ρ) (fun ρ => barrington c₂ ρ) σ`. -/
theorem barrington_node_true_cons_cons (c₁ c₂ : TreeCircuit n) (cs : List (TreeCircuit n))
    (σ : Perm (Fin 5)) :
    barrington (.node true (c₁ :: c₂ :: cs)) σ =
      commutatorProgram (fun ρ => barrington c₁ ρ) (fun ρ => barrington c₂ ρ) σ := by
  rw [barrington]

/-- Reader of `barrington`, `∨` node: `barrington (.node false (c₁ :: c₂ :: cs)) σ =
(commutatorProgram (fun ρ => (barrington c₁ ρ⁻¹).complementLast ρ⁻¹)
(fun ρ => (barrington c₂ ρ⁻¹).complementLast ρ⁻¹) σ⁻¹).complementLast σ⁻¹`. -/
theorem barrington_node_false_cons_cons (c₁ c₂ : TreeCircuit n) (cs : List (TreeCircuit n))
    (σ : Perm (Fin 5)) :
    barrington (.node false (c₁ :: c₂ :: cs)) σ =
      (commutatorProgram (fun ρ => (barrington c₁ ρ⁻¹).complementLast ρ⁻¹)
        (fun ρ => (barrington c₂ ρ⁻¹).complementLast ρ⁻¹) σ⁻¹).complementLast σ⁻¹ := by
  rw [barrington]

end Readers

/-! ### Targets C9–C16 -/

/-- **C9.** Lemma 3, first five-cycle: `IsFiveCycle sigma1` (Bar89's `(12345)`)
[Bar89, Lemma 3, p003-b005].

**Proof sketch.** Kernel `decide` (`isFiveCycle_iff`, `sigma1_eq`; no `native_decide`). -/
theorem isFiveCycle_sigma1 : IsFiveCycle sigma1 := by
  sorry

/-- **C9.** Lemma 3, second five-cycle: `IsFiveCycle sigma2` (Bar89's `(13542)`)
[Bar89, Lemma 3, p003-b005].

**Proof sketch.** Kernel `decide` (`isFiveCycle_iff`, `sigma2_eq`; no `native_decide`). -/
theorem isFiveCycle_sigma2 : IsFiveCycle sigma2 := by
  sorry

/-- **C9.** Lemma 3 in program order: the commutator of the two five-cycles is a five-cycle,
`IsFiveCycle (sigma2⁻¹ * sigma1⁻¹ * sigma2 * sigma1)`; the product is `(13254)` in Bar89's
one-based cycle notation, whose zero-based form `(0 2 1 4 3)` is what the code implements,
`List.formPerm [0, 2, 1, 4, 3]` [Bar89, Lemma 3, p003-b005: "`(12345)(13542)(54321)(24531) =
(13254)`"].
Deviation: Bar89's product is read left to right; the Mathlib product applies its right factor
first, so Bar89's `σ₁σ₂σ₁⁻¹σ₂⁻¹` is `sigma2⁻¹ * sigma1⁻¹ * sigma2 * sigma1` (r3 §H3.6).

**Proof sketch.** Kernel `decide` (`isFiveCycle_iff`, `sigma1_eq`, `sigma2_eq`), as
`decide +kernel`: the elaborator's pre-evaluation of plain `decide` hits `maxRecDepth` here
(probe P2). -/
theorem isFiveCycle_commutator : IsFiveCycle (sigma2⁻¹ * sigma1⁻¹ * sigma2 * sigma1) := by
  sorry

/-- **C10.** The explicit conjugator conjugates one five-cycle to the other:
`IsFiveCycle σ → IsFiveCycle τ → conjugator σ τ * σ * (conjugator σ τ)⁻¹ = τ`
[Bar89, Lemma 1 proof, p003-b003].  Checked by computation for all 24 × 24 pairs (r3 §H3.6).

**Proof sketch.** Reduce to a finite check: every five-cycle is one of the 24 explicit
`List.formPerm [0, a, b, c, d]` (`∀ σ, IsFiveCycle σ → σ ∈ l`, kernel `decide +kernel`, about
15 s), and C10 holds on the 24 × 24 explicit pairs (kernel `decide +kernel`, about 40 s and
5.5 GB; probes P3, P3b).  Alternatively argue: for a five-cycle `σ`, `k ↦ (σ ^ k) 0` is a
bijection from `range 5` onto `Fin 5` (`Equiv.Perm.IsCycle`, `cycleType` `{5}`), so
`conjugatorIndex σ (σ^k 0) = k`
(`conjugatorIndex_eq`, `List.find?`), `conjugatorFun σ τ (σ^k 0) = τ^k 0` (`conjugatorFun_eq`)
and it is a bijection; by `conjugator_apply_of_bijective`, `θ (σ (σ^k 0)) = τ^(k+1) 0 =
τ (θ (σ^k 0))`, i.e. `θ * σ = τ * θ` on the orbit of `0`, which is everything. -/
theorem conjugator_conj {σ τ : Perm (Fin 5)} (hσ : IsFiveCycle σ) (hτ : IsFiveCycle τ) :
    conjugator σ τ * σ * (conjugator σ τ)⁻¹ = τ := by
  sorry

/-- **C11.** **Lemma 1**: change the output to any five-cycle at the same length: if `B` five-cycle
recognizes `A` with output `σ` and `τ` is a five-cycle, then `B.conj (conjugator σ τ)` five-cycle
recognizes `A` with output `τ` [Bar89, Lemma 1, p003-b003].

**Proof sketch.** `fiveCycleRecognizes_iff`; the yield of the conjugate is `θ ∘ B.yield x ∘ θ⁻¹`
(`yield_conj`), which is `θ * σ * θ⁻¹ = τ` on `A` (`conjugator_conj`) and `θ ∘ θ⁻¹ = id` off `A`
(`Equiv.self_comp_symm`).  The length is kept by `length_conj`. -/
theorem FiveCycleRecognizes.conj {B : BranchingProgram 5 n} {A : (Fin n → Bool) → Prop}
    {σ τ : Perm (Fin 5)} (h : FiveCycleRecognizes B A σ) (hτ : IsFiveCycle τ) :
    FiveCycleRecognizes (B.conj (conjugator σ τ)) A τ := by
  sorry

/-- **C12.** **Lemma 2**: the complement, at the same length, with output `σ⁻¹`: if `B` (nonempty)
five-cycle recognizes `A` with output `σ`, then `B.complementLast σ` five-cycle recognizes
`fun x => ¬ A x` with output `σ⁻¹` [Bar89, Lemma 2, p003-b004].

**Proof sketch.** `fiveCycleRecognizes_iff` and `yield_complementLast` (using `hB`): the new
yield is `σ⁻¹ ∘ B.yield x`, which is `σ⁻¹ ∘ σ = id` on `A` (`Equiv.symm_comp_self`) and `σ⁻¹` off
`A`; `σ⁻¹` is a five-cycle (`Equiv.Perm.cycleType_inv`). -/
theorem FiveCycleRecognizes.complementLast {B : BranchingProgram 5 n}
    {A : (Fin n → Bool) → Prop} {σ : Perm (Fin 5)} (h : FiveCycleRecognizes B A σ)
    (hB : 0 < B.length) :
    FiveCycleRecognizes (B.complementLast σ) (fun x => ¬ A x) σ⁻¹ := by
  sorry

/-- **C13.** **Barrington's Theorem 1**, recognition: for a fan-in-2 formula `c` and a five-cycle
`σ`, `barrington c σ` five-cycle recognizes `{x | c.eval x = true}` with output `σ`
[Bar89, Thm 1, p003-b002, proof p004-b002; BV14, Thm 3.5, p014-b001].
Deviations: formulas over literals with constant and fan-in-1 nodes (each handled directly); the
OR case by De Morgan through Lemma 2; BV14 states the theorem for NAND circuits.

**Proof sketch.** Induction on `c` (`TreeCircuit.ind`), generalizing `σ`; `maxFanin_node` and
`maxFanin_le_maxFaninL` give each child fan-in `≤ 2` and the child list length `≤ 2`.
* Literals and constants: one instruction (`barrington_lit_true`, …, `yield_eq`,
  `Instr.eval_eq`, `Instr.ofPerm_map0`/`_map1`); the values by `TreeCircuit.eval_lit`
  and `eval_node_true_iff`/`eval_node_false_iff`.
* Fan-in 1: `barrington_node_singleton` and `eval_node_true`/`eval_node_false` on `[c]`.
* `∧`: `barrington_node_true_cons_cons`, `commutatorProgram_eq`, `yield_append` (three times).
  The outputs `τᵢ` are five-cycles (`Equiv.Perm.cycleType_conj`, `cycleType_inv`), so the
  induction hypothesis applies to each block; on `c₁ ∧ c₂` the yield is
  `θ * (sigma2⁻¹ * sigma1⁻¹ * sigma2 * sigma1) * θ⁻¹ = σ` (`isFiveCycle_commutator`,
  `conjugator_conj`), and off it two blocks cancel.
* `∨`: `barrington_node_false_cons_cons`; C12 (with `barrington_length_pos`) turns each child
  into a recognizer of its negation, the `∧` case gives `¬c₁ ∧ ¬c₂` with output `σ⁻¹`, and C12
  again gives `c₁ ∨ c₂` with output `σ` (`inv_inv`). -/
theorem barrington_recognizes [NeZero n] (c : TreeCircuit n) (hc : c.maxFanin ≤ 2)
    {σ : Perm (Fin 5)} (hσ : IsFiveCycle σ) :
    FiveCycleRecognizes (barrington c σ) (fun x => c.eval x = true) σ := by
  sorry

/-- **C14.** **Theorem 1**, length: `(barrington c σ).length ≤ 4 ^ c.depth` for a fan-in-2
formula [Bar89, Thm 1, p003-b002: "of length at most `4^d`"].

**Proof sketch.** Induction on `c` (`TreeCircuit.ind`) generalizing `σ`.  Leaves have length 1
and depth 0 or 1 (`depth_node`, `maxDepth_nil`).  Fan-in 1 keeps the length and adds one level.
`∧`: four blocks (`commutatorProgram_eq`, `length_append`) each of length `≤ 4 ^ maxDepth`
(`depth_le_maxDepth`), so `≤ 4 · 4 ^ maxDepth = 4 ^ (1 + maxDepth) = 4 ^ depth` (`depth_node`).
`∨`: the same, `complementLast` keeping lengths (`length_complementLast`). -/
theorem barrington_length_le [NeZero n] {c : TreeCircuit n} (hc : c.maxFanin ≤ 2)
    (σ : Perm (Fin 5)) : (barrington c σ).length ≤ 4 ^ c.depth := by
  sorry

/-- **C14.** Every Barrington program is nonempty: `0 < (barrington c σ).length`.  Glue for
Lemma 2 (`yield_complementLast` needs a last instruction).

**Proof sketch.** Induction on `c` (`TreeCircuit.ind`) generalizing `σ`, by the readers
`barrington_lit_true`, …: leaves have one instruction; fan-in 1 is the child; the `∧` and `∨`
programs contain a child's program (`commutatorProgram_eq`, `length_append`,
`length_complementLast`). -/
theorem barrington_length_pos [NeZero n] (c : TreeCircuit n) (σ : Perm (Fin 5)) :
    0 < (barrington c σ).length := by
  sorry

/-- **C15.** Every Barrington program is a permutation program: `(barrington c σ).IsPermutation`.
Glue; [Bar89, Thm 1, p003-b002]: "a 5-PBP".

**Proof sketch.** Induction on `c` (`TreeCircuit.ind`) generalizing `σ`: leaves are
`Instr.ofPerm` instructions (`Instr.isPermutation_ofPerm`, `isPermutation_iff`); the `∧` and `∨`
programs are closed under `IsPermutation.append` and `IsPermutation.complementLast`
(`commutatorProgram_eq`). -/
theorem isPermutation_barrington [NeZero n] (c : TreeCircuit n) (σ : Perm (Fin 5)) :
    (barrington c σ).IsPermutation := by
  sorry

/-- **C16.** BV14's reading from start state `0`: for a fan-in-2 formula and a five-cycle `σ`,
`(barrington c σ).yield x 0 = if c.eval x then σ 0 else 0` [BV14, Thm 3.5, p014-b001; §3.3,
p013-b002].
Deviation: BV14 reads coordinate `1` of a 1-based state; here the start state is `0` and an
accepted input ends at `σ 0 ≠ 0` (r3 §H3.7).

**Proof sketch.** `barrington_recognizes` and `fiveCycleRecognizes_iff`; split on `c.eval x`. -/
theorem barrington_yield_zero [NeZero n] {c : TreeCircuit n} (hc : c.maxFanin ≤ 2)
    {σ : Perm (Fin 5)} (hσ : IsFiveCycle σ) (x : Fin n → Bool) :
    (barrington c σ).yield x 0 = if c.eval x then σ 0 else 0 := by
  sorry

end BranchingProgram
