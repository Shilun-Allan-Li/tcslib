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
* `BranchingProgram.sigma1`, `sigma2` — Lemma 3's five-cycles `(12345)`, `(13542)` in Bar89's
  one-based cycle notation, implemented in zero-based form as `(0 1 2 3 4)`, `(0 2 4 3 1)`.
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

/-- Bar89's `(12345)` in its one-based cycle notation, whose zero-based form `(0 1 2 3 4)` is what
the code implements: the five-cycle `0 ↦ 1 ↦ 2 ↦ 3 ↦ 4 ↦ 0`, Mathlib's `c[0,1,2,3,4]`, written
`sigma1 = List.formPerm [0, 1, 2, 3, 4]` [Bar89, Lemma 3, p003-b005]. -/
def sigma1 : Perm (Fin 5) :=
  List.formPerm [0, 1, 2, 3, 4]

/-- Reader of `sigma1`: `sigma1 = List.formPerm [0, 1, 2, 3, 4]`. -/
theorem sigma1_eq : sigma1 = List.formPerm [0, 1, 2, 3, 4] := rfl

/-- Bar89's `(13542)` in its one-based cycle notation, whose zero-based form `(0 2 4 3 1)` is what
the code implements: the five-cycle `0 ↦ 2 ↦ 4 ↦ 3 ↦ 1 ↦ 0`, Mathlib's `c[0,2,4,3,1]`, written
`sigma2 = List.formPerm [0, 2, 4, 3, 1]` [Bar89, Lemma 3, p003-b005]. -/
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
  decide

/-- **C9.** Lemma 3, second five-cycle: `IsFiveCycle sigma2` (Bar89's `(13542)`)
[Bar89, Lemma 3, p003-b005].

**Proof sketch.** Kernel `decide` (`isFiveCycle_iff`, `sigma2_eq`; no `native_decide`). -/
theorem isFiveCycle_sigma2 : IsFiveCycle sigma2 := by
  decide

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
  decide +kernel

/-- The inverse of a five-cycle is a five-cycle: `IsFiveCycle σ → IsFiveCycle σ⁻¹`
(`Equiv.Perm.cycleType_inv`).  Glue for Lemma 2 [Bar89, Lemma 2 proof, p003-b004]. -/
private theorem isFiveCycle_inv {σ : Perm (Fin 5)} (h : IsFiveCycle σ) : IsFiveCycle σ⁻¹ := by
  rw [isFiveCycle_iff, Perm.cycleType_inv]
  exact h

/-- A conjugate of a five-cycle is a five-cycle: `IsFiveCycle σ → IsFiveCycle (θ * σ * θ⁻¹)`
(`Equiv.Perm.cycleType_conj`).  Glue for [Bar89, Thm 1 proof, p004-b002]. -/
private theorem isFiveCycle_conj {σ : Perm (Fin 5)} (h : IsFiveCycle σ) (θ : Perm (Fin 5)) :
    IsFiveCycle (θ * σ * θ⁻¹) := by
  rw [isFiveCycle_iff, Perm.cycleType_conj]
  exact h

/-- A five-cycle is a cycle: `IsFiveCycle σ → σ.IsCycle` (`Equiv.Perm.card_cycleType_eq_one`).
Glue for C10. -/
private theorem IsFiveCycle.isCycle {σ : Perm (Fin 5)} (h : IsFiveCycle σ) : σ.IsCycle := by
  rw [isFiveCycle_iff] at h
  rw [← Perm.card_cycleType_eq_one, h, Multiset.card_singleton]

/-- A five-cycle has order five: `IsFiveCycle σ → orderOf σ = 5` (`Equiv.Perm.lcm_cycleType`).
Glue for C10. -/
private theorem IsFiveCycle.orderOf_eq {σ : Perm (Fin 5)} (h : IsFiveCycle σ) :
    orderOf σ = 5 := by
  rw [isFiveCycle_iff] at h
  rw [← Perm.lcm_cycleType, h, Multiset.lcm_singleton, normalize_eq]

/-- A five-cycle on `Fin 5` moves every point: `IsFiveCycle σ → σ i ≠ i` (its support has
`5 = Fintype.card (Fin 5)` elements, `Equiv.Perm.sum_cycleType`).  Glue for C10. -/
private theorem IsFiveCycle.apply_ne {σ : Perm (Fin 5)} (h : IsFiveCycle σ) (i : Fin 5) :
    σ i ≠ i := by
  rw [isFiveCycle_iff] at h
  have hs : σ.support = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [← Perm.sum_cycleType, h, Multiset.sum_singleton, Fintype.card_fin]
  rw [← Perm.mem_support, hs]
  exact Finset.mem_univ i

/-- On the orbit of `0` under a five-cycle, powers agree exactly modulo `5`:
`IsFiveCycle σ → ((σ ^ a) 0 = (σ ^ b) 0 ↔ a ≡ b [MOD 5])` (`Equiv.Perm.IsCycle.pow_eq_pow_iff`,
`pow_eq_pow_iff_modEq`).  Glue for C10 [Bar89, Lemma 1 proof, p003-b003]. -/
private theorem IsFiveCycle.pow_apply_eq_iff {σ : Perm (Fin 5)} (h : IsFiveCycle σ) {a b : ℕ} :
    (σ ^ a) 0 = (σ ^ b) 0 ↔ a ≡ b [MOD 5] := by
  have h5 := h.orderOf_eq
  constructor
  · intro hab
    have hmod := pow_eq_pow_iff_modEq.1 (h.isCycle.pow_eq_pow_iff.2 ⟨0, h.apply_ne 0, hab⟩)
    rwa [h5] at hmod
  · intro hab
    rw [← h5] at hab
    rw [pow_eq_pow_iff_modEq.2 hab]

/-- For a five-cycle `σ`, `conjugatorIndex σ i` is an exponent reaching `i` from `0`:
`IsFiveCycle σ → (σ ^ conjugatorIndex σ i) 0 = i`.  Some `k < orderOf σ = 5` reaches `i`
(`Equiv.Perm.SameCycle.exists_pow_eq'`), so `List.find?` succeeds on `List.range 5`.  Glue for
C10 [Bar89, Lemma 1 proof, p003-b003]. -/
private theorem pow_conjugatorIndex {σ : Perm (Fin 5)} (h : IsFiveCycle σ) (i : Fin 5) :
    (σ ^ conjugatorIndex σ i) 0 = i := by
  obtain ⟨k, hk, hki⟩ := (h.isCycle.sameCycle (h.apply_ne 0) (h.apply_ne i)).exists_pow_eq'
  rw [h.orderOf_eq] at hk
  rw [conjugatorIndex_eq]
  cases hf : (List.range 5).find? (fun k => (σ ^ k) 0 = i) with
  | none =>
    rw [List.find?_eq_none] at hf
    exact absurd (decide_eq_true hki) (hf k (List.mem_range.2 hk))
  | some m =>
    rw [Option.getD_some]
    have hm := List.find?_some (p := fun k => decide ((σ ^ k) 0 = i)) hf
    exact of_decide_eq_true hm

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
  -- the sketch's "alternatively" route: `θ (σ^k 0) = τ^k 0` intertwines `σ` and `τ`
  have hcomm : ∀ i, conjugatorFun σ τ (σ i) = τ (conjugatorFun σ τ i) := by
    intro i
    have hstep : τ ((τ ^ conjugatorIndex σ i) 0) = (τ ^ (conjugatorIndex σ i + 1)) 0 := by
      rw [pow_succ', Perm.mul_apply]
    rw [conjugatorFun_eq, conjugatorFun_eq, hstep, hτ.pow_apply_eq_iff, ← hσ.pow_apply_eq_iff,
      pow_conjugatorIndex hσ, pow_succ', Perm.mul_apply, pow_conjugatorIndex hσ]
  -- it is injective, hence a bijection of `Fin 5`
  have hinj : Function.Injective (conjugatorFun σ τ) := by
    intro i j hij
    rw [conjugatorFun_eq, conjugatorFun_eq, hτ.pow_apply_eq_iff, ← hσ.pow_apply_eq_iff,
      pow_conjugatorIndex hσ, pow_conjugatorIndex hσ] at hij
    exact hij
  have hbij : Function.Bijective (conjugatorFun σ τ) := Finite.injective_iff_bijective.1 hinj
  rw [mul_inv_eq_iff_eq_mul]
  ext i
  rw [Perm.mul_apply, Perm.mul_apply, conjugator_apply_of_bijective hbij,
    conjugator_apply_of_bijective hbij, hcomm]

/-- **C11.** **Lemma 1**: change the output to any five-cycle at the same length: if `B` five-cycle
recognizes `A` with output `σ` and `τ` is a five-cycle, then `B.conj (conjugator σ τ)` five-cycle
recognizes `A` with output `τ` [Bar89, Lemma 1, p003-b003].

**Proof sketch.** `fiveCycleRecognizes_iff`; the yield of the conjugate is `θ ∘ B.yield x ∘ θ⁻¹`
(`yield_conj`), which is `θ * σ * θ⁻¹ = τ` on `A` (`conjugator_conj`) and `θ ∘ θ⁻¹ = id` off `A`
(`Equiv.self_comp_symm`).  The length is kept by `length_conj`. -/
theorem FiveCycleRecognizes.conj {B : BranchingProgram 5 n} {A : (Fin n → Bool) → Prop}
    {σ τ : Perm (Fin 5)} (h : FiveCycleRecognizes B A σ) (hτ : IsFiveCycle τ) :
    FiveCycleRecognizes (B.conj (conjugator σ τ)) A τ := by
  rw [fiveCycleRecognizes_iff] at h ⊢
  refine ⟨hτ, fun x => ⟨fun hA => ?_, fun hA => ?_⟩⟩
  · rw [yield_conj, (h.2 x).1 hA]
    conv_rhs => rw [← conjugator_conj h.1 hτ]
    rw [Perm.coe_mul, Perm.coe_mul, Perm.inv_def]
    rfl
  · rw [yield_conj, (h.2 x).2 hA, Function.id_comp, Equiv.self_comp_symm]

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
  rw [fiveCycleRecognizes_iff] at h ⊢
  refine ⟨isFiveCycle_inv h.1, fun x => ⟨fun hA => ?_, fun hA => ?_⟩⟩
  · rw [yield_complementLast B σ hB, (h.2 x).2 hA, Function.comp_id, Perm.inv_def]
  · rw [yield_complementLast B σ hB, (h.2 x).1 (not_not.1 hA), Equiv.symm_comp_self]

/-- A one-instruction program `⟨[⟨i, σ₀, σ₁⟩]⟩` yields `σ₁` on `x i = 1` and `σ₀` on `x i = 0`:
`(⟨[Instr.ofPerm i σ₀ σ₁]⟩ : BranchingProgram 5 n).yield x = if x i then ⇑σ₁ else ⇑σ₀`.  Glue for
the leaves of C13 (`yield_eq`, `Instr.eval_eq`, the `Instr.ofPerm` field readers). -/
private theorem yield_ofPerm (i : Fin n) (σ₀ σ₁ : Perm (Fin 5)) (x : Fin n → Bool) :
    (⟨[Instr.ofPerm i σ₀ σ₁]⟩ : BranchingProgram 5 n).yield x = if x i then ⇑σ₁ else ⇑σ₀ := by
  simp only [yield_eq, List.foldl_cons, List.foldl_nil, Function.comp_id]
  rw [Instr.eval_eq, Instr.ofPerm_var, funext (Instr.ofPerm_map0 i σ₀ σ₁),
    funext (Instr.ofPerm_map1 i σ₀ σ₁)]

/-- A one-instruction program has length one:
`(⟨[Instr.ofPerm i σ₀ σ₁]⟩ : BranchingProgram 5 n).length = 1`.  Glue for C14. -/
private theorem length_ofPerm (i : Fin n) (σ₀ σ₁ : Perm (Fin 5)) :
    (⟨[Instr.ofPerm i σ₀ σ₁]⟩ : BranchingProgram 5 n).length = 1 := by
  simp only [length_eq, List.length_singleton]

/-- A one-instruction program built from permutations is a permutation program:
`(⟨[Instr.ofPerm i σ₀ σ₁]⟩ : BranchingProgram 5 n).IsPermutation` (`Instr.isPermutation_ofPerm`).
Glue for C15. -/
private theorem isPermutation_ofPerm (i : Fin n) (σ₀ σ₁ : Perm (Fin 5)) :
    (⟨[Instr.ofPerm i σ₀ σ₁]⟩ : BranchingProgram 5 n).IsPermutation := by
  rw [isPermutation_iff]
  intro ι hι
  simp only [List.mem_singleton] at hι
  subst hι
  exact (Instr.isPermutation_iff _).1 (Instr.isPermutation_ofPerm i σ₀ σ₁)

/-- A five-cycle recognizer's yield as a permutation: if `B` five-cycle recognizes `A` with output
`σ`, then `B.yield x = ⇑(if A x then σ else 1)`.  Glue for the `∧` step of C13. -/
private theorem FiveCycleRecognizes.yield_eq_ite {B : BranchingProgram 5 n}
    {A : (Fin n → Bool) → Prop} {σ : Perm (Fin 5)} (h : FiveCycleRecognizes B A σ)
    (x : Fin n → Bool) [Decidable (A x)] : B.yield x = ⇑(if A x then σ else 1) := by
  rw [fiveCycleRecognizes_iff] at h
  by_cases hA : A x
  · rw [if_pos hA, (h.2 x).1 hA]
  · rw [if_neg hA, (h.2 x).2 hA, Perm.coe_one]

/-- Five-cycle recognition only depends on the recognized set: if `B` five-cycle recognizes `A`
with output `σ` and `A x ↔ A' x` for all `x`, then it recognizes `A'`.  Glue for C13. -/
private theorem FiveCycleRecognizes.of_iff {B : BranchingProgram 5 n}
    {A A' : (Fin n → Bool) → Prop} {σ : Perm (Fin 5)} (h : FiveCycleRecognizes B A σ)
    (hA : ∀ x, A x ↔ A' x) : FiveCycleRecognizes B A' σ := by
  have hAA : A = A' := funext fun x => propext (hA x)
  subst hAA
  exact h

/-- **The `∧` step** of [Bar89, Thm 1 proof, p004-b002]: if `P₁ ρ` and `P₂ ρ` five-cycle recognize
`A₁` and `A₂` with output `ρ` for every five-cycle `ρ`, then `commutatorProgram P₁ P₂ σ`
recognizes `A₁ ∩ A₂` with output `σ`.  On `A₁ ∩ A₂` the yield is `τ₂⁻¹ τ₁⁻¹ τ₂ τ₁ =
θ (sigma2⁻¹ sigma1⁻¹ sigma2 sigma1) θ⁻¹ = σ` (`isFiveCycle_commutator`, `conjugator_conj`); off it
two of the four blocks are the identity and the other two cancel.  A named step of C13's
sketch.

**Proof sketch.** Write `θ` for the conjugator and `τᵢ = θ * sigmaᵢ * θ⁻¹`, five-cycles by
`Equiv.Perm.cycleType_conj`, as are their inverses.  By `yield_append` the yield is the product of
the four blocks' yields, and each block's yield is `τ` or `1` according to its recognized set.
Split on `A₁ x` and `A₂ x`: if both hold the product `τ₂⁻¹ τ₁⁻¹ τ₂ τ₁` equals
`θ (sigma2⁻¹ sigma1⁻¹ sigma2 sigma1) θ⁻¹`, which is `σ` by `conjugator_conj` (group identities);
otherwise the surviving blocks are `τ⁻¹` and `τ` for the same `τ`, or none, and cancel. -/
private theorem commutatorProgram_recognizes {P₁ P₂ : Perm (Fin 5) → BranchingProgram 5 n}
    {A₁ A₂ : (Fin n → Bool) → Prop}
    (h₁ : ∀ ρ, IsFiveCycle ρ → FiveCycleRecognizes (P₁ ρ) A₁ ρ)
    (h₂ : ∀ ρ, IsFiveCycle ρ → FiveCycleRecognizes (P₂ ρ) A₂ ρ)
    {σ : Perm (Fin 5)} (hσ : IsFiveCycle σ) :
    FiveCycleRecognizes (commutatorProgram P₁ P₂ σ) (fun x => A₁ x ∧ A₂ x) σ := by
  classical
  set θ := conjugator (sigma2⁻¹ * sigma1⁻¹ * sigma2 * sigma1) σ with hθ
  have hc₁ : IsFiveCycle (θ * sigma1 * θ⁻¹) := isFiveCycle_conj isFiveCycle_sigma1 θ
  have hc₂ : IsFiveCycle (θ * sigma2 * θ⁻¹) := isFiveCycle_conj isFiveCycle_sigma2 θ
  have hθσ : θ * (sigma2⁻¹ * sigma1⁻¹ * sigma2 * sigma1) * θ⁻¹ = σ :=
    conjugator_conj isFiveCycle_commutator hσ
  -- the yield, as a product of the four blocks' permutations
  have key : ∀ x, (commutatorProgram P₁ P₂ σ).yield x = ⇑(if A₁ x ∧ A₂ x then σ else 1) := by
    intro x
    rw [commutatorProgram_eq, ← hθ, yield_append, yield_append, yield_append,
      (h₁ _ hc₁).yield_eq_ite x, (h₂ _ hc₂).yield_eq_ite x,
      (h₁ _ (isFiveCycle_inv hc₁)).yield_eq_ite x, (h₂ _ (isFiveCycle_inv hc₂)).yield_eq_ite x,
      ← Perm.coe_mul, ← Perm.coe_mul, ← Perm.coe_mul]
    congr 1
    -- off `A₁ ∩ A₂` the blocks cancel; on it the product is the conjugated commutator
    by_cases ha₁ : A₁ x <;> by_cases ha₂ : A₂ x <;>
      simp only [ha₁, ha₂, and_self, and_true, and_false, ↓reduceIte,
        one_mul, mul_one, inv_mul_cancel]
    rw [← hθσ]
    group
  rw [fiveCycleRecognizes_iff]
  refine ⟨hσ, fun x => ⟨fun hA => ?_, fun hA => ?_⟩⟩
  · rw [key, if_pos hA]
  · rw [key, if_neg hA, Perm.coe_one]

/-- A commutator program is nonempty when its first block is: `(∀ ρ, 0 < (P₁ ρ).length) →
0 < (commutatorProgram P₁ P₂ σ).length` (`commutatorProgram_eq`, `length_append`).  Glue for
C13 and C14. -/
private theorem commutatorProgram_length_pos {P₁ P₂ : Perm (Fin 5) → BranchingProgram 5 n}
    (h₁ : ∀ ρ, 0 < (P₁ ρ).length) (σ : Perm (Fin 5)) :
    0 < (commutatorProgram P₁ P₂ σ).length := by
  set θ := conjugator (sigma2⁻¹ * sigma1⁻¹ * sigma2 * sigma1) σ with hθ
  rw [commutatorProgram_eq, ← hθ, length_append, length_append, length_append]
  have := h₁ (θ * sigma1 * θ⁻¹)
  omega

/-- A commutator program of blocks of length at most `K` has length at most `4 · K`:
`(∀ ρ, (P₁ ρ).length ≤ K) → (∀ ρ, (P₂ ρ).length ≤ K) → (commutatorProgram P₁ P₂ σ).length ≤ 4 * K`
(`commutatorProgram_eq`, `length_append`) [Bar89, Thm 1 proof, p004-b002].  Glue for C14. -/
private theorem length_commutatorProgram_le {P₁ P₂ : Perm (Fin 5) → BranchingProgram 5 n}
    {K : ℕ} (h₁ : ∀ ρ, (P₁ ρ).length ≤ K) (h₂ : ∀ ρ, (P₂ ρ).length ≤ K) (σ : Perm (Fin 5)) :
    (commutatorProgram P₁ P₂ σ).length ≤ 4 * K := by
  set θ := conjugator (sigma2⁻¹ * sigma1⁻¹ * sigma2 * sigma1) σ with hθ
  rw [commutatorProgram_eq, ← hθ, length_append, length_append, length_append]
  have a := h₁ (θ * sigma1 * θ⁻¹)
  have b := h₂ (θ * sigma2 * θ⁻¹)
  have c := h₁ (θ * sigma1 * θ⁻¹)⁻¹
  have d := h₂ (θ * sigma2 * θ⁻¹)⁻¹
  omega

/-- Every Barrington program is nonempty: `0 < (barrington c σ).length`.  The proof of C14's
`barrington_length_pos`, placed before C13, which needs it for Lemma 2 in the `∨` case.

**Proof sketch.** Induction on `c` (`TreeCircuit.ind`) generalizing `σ`, by the readers of
`barrington`: literals and constants have one instruction; a fan-in-1 node is its child's
program; the `∧` and `∨` programs contain the first child's program as a block
(`commutatorProgram_length_pos`; `length_complementLast` for the `∨` case's complements). -/
private theorem barrington_length_pos_aux [NeZero n] (c : TreeCircuit n) (σ : Perm (Fin 5)) :
    0 < (barrington c σ).length := by
  refine TreeCircuit.ind (motive := fun c => ∀ σ, 0 < (barrington c σ).length) ?_ ?_ c σ
  · rintro ⟨i, s⟩ σ
    cases s
    · rw [barrington_lit_false, length_ofPerm]
      exact Nat.one_pos
    · rw [barrington_lit_true, length_ofPerm]
      exact Nat.one_pos
  · intro b cs ih σ
    rcases cs with _ | ⟨c₁, _ | ⟨c₂, cs⟩⟩
    · cases b
      · rw [barrington_node_false_nil, length_ofPerm]
        exact Nat.one_pos
      · rw [barrington_node_true_nil, length_ofPerm]
        exact Nat.one_pos
    · rw [barrington_node_singleton]
      exact ih c₁ (List.mem_singleton.2 rfl) σ
    · have h₁ := ih c₁ (List.mem_cons.2 (Or.inl rfl))
      cases b
      · rw [barrington_node_false_cons_cons, length_complementLast]
        exact commutatorProgram_length_pos
          (P₁ := fun ρ => (barrington c₁ ρ⁻¹).complementLast ρ⁻¹)
          (fun ρ => by simp only [length_complementLast]; exact h₁ ρ⁻¹) σ⁻¹
      · rw [barrington_node_true_cons_cons]
        exact commutatorProgram_length_pos (P₁ := fun ρ => barrington c₁ ρ) h₁ σ

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
  refine TreeCircuit.ind (motive := fun c => c.maxFanin ≤ 2 → ∀ σ, IsFiveCycle σ →
    FiveCycleRecognizes (barrington c σ) (fun x => c.eval x = true) σ) ?_ ?_ c hc σ hσ
  · -- literals: one instruction
    rintro ⟨i, s⟩ - σ hσ
    rw [fiveCycleRecognizes_iff]
    refine ⟨hσ, fun x => ?_⟩
    rw [TreeCircuit.eval_lit, Lit.eval_eq]
    cases s
    · rw [barrington_lit_false, yield_ofPerm]
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases x i <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        Perm.coe_one, not_true_eq_false, not_false_eq_true, false_implies, true_implies, and_self]
    · rw [barrington_lit_true, yield_ofPerm]
      simp only [↓reduceIte]
      cases x i <;> simp only [Bool.false_eq_true, ↓reduceIte, Perm.coe_one, not_true_eq_false,
        not_false_eq_true, false_implies, true_implies, and_self]
  · intro b cs ih hc σ hσ
    rw [TreeCircuit.maxFanin_node] at hc
    have hlen : cs.length ≤ 2 := le_of_max_le_left hc
    have hch : ∀ c ∈ cs, c.maxFanin ≤ 2 := fun c hc' =>
      (TreeCircuit.maxFanin_le_maxFaninL hc').trans (le_of_max_le_right hc)
    rcases cs with _ | ⟨c₁, _ | ⟨c₂, _ | ⟨c₃, cs⟩⟩⟩
    · -- constants: one instruction, `σ` for true and `1` for false
      rw [fiveCycleRecognizes_iff]
      refine ⟨hσ, fun x => ?_⟩
      cases b
      · have hf : ¬ (TreeCircuit.node false [] : TreeCircuit n).eval x = true := by
          rw [TreeCircuit.eval_node_false_iff]
          rintro ⟨c, hc, -⟩
          exact absurd hc List.not_mem_nil
        rw [barrington_node_false_nil, yield_ofPerm, ite_self, Perm.coe_one]
        exact ⟨fun h => absurd h hf, fun _ => rfl⟩
      · have ht : (TreeCircuit.node true [] : TreeCircuit n).eval x = true := by
          rw [TreeCircuit.eval_node_true_iff]
          intro c hc
          exact absurd hc List.not_mem_nil
        rw [barrington_node_true_nil, yield_ofPerm, ite_self]
        exact ⟨fun _ => rfl, fun h => absurd ht h⟩
    · -- fan-in 1: the child's program
      have hm : c₁ ∈ [c₁] := List.mem_singleton.2 rfl
      rw [barrington_node_singleton]
      refine (ih c₁ hm (hch c₁ hm) σ hσ).of_iff fun x => ?_
      cases b
      · rw [TreeCircuit.eval_node_false_iff]
        exact ⟨fun h => ⟨c₁, hm, h⟩, fun ⟨c, hc, h⟩ => List.mem_singleton.1 hc ▸ h⟩
      · rw [TreeCircuit.eval_node_true_iff]
        exact ⟨fun h c hc => List.mem_singleton.1 hc ▸ h, fun h => h c₁ hm⟩
    · -- fan-in 2
      have hm₁ : c₁ ∈ [c₁, c₂] := List.mem_cons.2 (Or.inl rfl)
      have hm₂ : c₂ ∈ [c₁, c₂] := List.mem_cons.2 (Or.inr (List.mem_singleton.2 rfl))
      have hmem : ∀ c, c ∈ [c₁, c₂] → c = c₁ ∨ c = c₂ := fun c hc => by
        rcases List.mem_cons.1 hc with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_singleton.1 h)
      have ih₁ : ∀ ρ, IsFiveCycle ρ →
          FiveCycleRecognizes (barrington c₁ ρ) (fun x => c₁.eval x = true) ρ :=
        fun ρ hρ => ih c₁ hm₁ (hch c₁ hm₁) ρ hρ
      have ih₂ : ∀ ρ, IsFiveCycle ρ →
          FiveCycleRecognizes (barrington c₂ ρ) (fun x => c₂.eval x = true) ρ :=
        fun ρ hρ => ih c₂ hm₂ (hch c₂ hm₂) ρ hρ
      cases b
      · -- `∨`: De Morgan through Lemma 2 (C12)
        have hn₁ : ∀ ρ, IsFiveCycle ρ →
            FiveCycleRecognizes ((barrington c₁ ρ⁻¹).complementLast ρ⁻¹)
              (fun x => ¬ c₁.eval x = true) ρ := by
          intro ρ hρ
          have h := (ih₁ ρ⁻¹ (isFiveCycle_inv hρ)).complementLast
            (barrington_length_pos_aux c₁ ρ⁻¹)
          rwa [inv_inv] at h
        have hn₂ : ∀ ρ, IsFiveCycle ρ →
            FiveCycleRecognizes ((barrington c₂ ρ⁻¹).complementLast ρ⁻¹)
              (fun x => ¬ c₂.eval x = true) ρ := by
          intro ρ hρ
          have h := (ih₂ ρ⁻¹ (isFiveCycle_inv hρ)).complementLast
            (barrington_length_pos_aux c₂ ρ⁻¹)
          rwa [inv_inv] at h
        have hand := commutatorProgram_recognizes
          (P₁ := fun ρ => (barrington c₁ ρ⁻¹).complementLast ρ⁻¹)
          (P₂ := fun ρ => (barrington c₂ ρ⁻¹).complementLast ρ⁻¹) hn₁ hn₂ (isFiveCycle_inv hσ)
        have hpos := commutatorProgram_length_pos
          (P₁ := fun ρ => (barrington c₁ ρ⁻¹).complementLast ρ⁻¹)
          (P₂ := fun ρ => (barrington c₂ ρ⁻¹).complementLast ρ⁻¹)
          (fun ρ => by
            simp only [length_complementLast]
            exact barrington_length_pos_aux c₁ ρ⁻¹) σ⁻¹
        have hor := hand.complementLast hpos
        rw [inv_inv] at hor
        rw [barrington_node_false_cons_cons]
        refine hor.of_iff fun x => ?_
        dsimp only
        rw [TreeCircuit.eval_node_false_iff]
        constructor
        · intro h
          by_contra h'
          exact h ⟨fun h₁ => h' ⟨c₁, hm₁, h₁⟩, fun h₂ => h' ⟨c₂, hm₂, h₂⟩⟩
        · rintro ⟨c, hc, hce⟩ ⟨h₁, h₂⟩
          rcases hmem c hc with rfl | rfl
          · exact h₁ hce
          · exact h₂ hce
      · -- `∧`: the commutator step
        rw [barrington_node_true_cons_cons]
        refine (commutatorProgram_recognizes (P₁ := fun ρ => barrington c₁ ρ)
          (P₂ := fun ρ => barrington c₂ ρ) ih₁ ih₂ hσ).of_iff fun x => ?_
        dsimp only
        rw [TreeCircuit.eval_node_true_iff]
        constructor
        · rintro ⟨h₁, h₂⟩ c hc
          rcases hmem c hc with rfl | rfl
          · exact h₁
          · exact h₂
        · intro h
          exact ⟨h c₁ hm₁, h c₂ hm₂⟩
    · -- fan-in above 2 contradicts `hc`
      simp only [List.length_cons] at hlen
      omega

/-- **C14.** **Theorem 1**, length: `(barrington c σ).length ≤ 4 ^ c.depth` for a fan-in-2
formula [Bar89, Thm 1, p003-b002: "of length at most `4^d`"].

**Proof sketch.** Induction on `c` (`TreeCircuit.ind`) generalizing `σ`.  Leaves have length 1
and depth 0 or 1 (`depth_node`, `maxDepth_nil`).  Fan-in 1 keeps the length and adds one level.
`∧`: four blocks (`commutatorProgram_eq`, `length_append`) each of length `≤ 4 ^ maxDepth`
(`depth_le_maxDepth`), so `≤ 4 · 4 ^ maxDepth = 4 ^ (1 + maxDepth) = 4 ^ depth` (`depth_node`).
`∨`: the same, `complementLast` keeping lengths (`length_complementLast`). -/
theorem barrington_length_le [NeZero n] {c : TreeCircuit n} (hc : c.maxFanin ≤ 2)
    (σ : Perm (Fin 5)) : (barrington c σ).length ≤ 4 ^ c.depth := by
  refine TreeCircuit.ind (motive := fun c => c.maxFanin ≤ 2 → ∀ σ,
    (barrington c σ).length ≤ 4 ^ c.depth) ?_ ?_ c hc σ
  · -- leaves have length one
    rintro ⟨i, s⟩ - σ
    cases s
    · rw [barrington_lit_false, length_ofPerm]
      exact Nat.one_le_pow _ _ (by norm_num)
    · rw [barrington_lit_true, length_ofPerm]
      exact Nat.one_le_pow _ _ (by norm_num)
  · intro b cs ih hc σ
    rw [TreeCircuit.maxFanin_node] at hc
    have hch : ∀ c ∈ cs, c.maxFanin ≤ 2 := fun c hc' =>
      (TreeCircuit.maxFanin_le_maxFaninL hc').trans (le_of_max_le_right hc)
    -- each child's bound is at most `4 ^ maxDepth cs`
    have hchild : ∀ c ∈ cs, ∀ ρ, (barrington c ρ).length ≤ 4 ^ TreeCircuit.maxDepth cs :=
      fun c hc' ρ => (ih c hc' (hch c hc') ρ).trans
        (Nat.pow_le_pow_right (by norm_num) (TreeCircuit.depth_le_maxDepth hc'))
    rw [TreeCircuit.depth_node, add_comm, pow_succ]
    rcases cs with _ | ⟨c₁, _ | ⟨c₂, cs⟩⟩
    · cases b
      · rw [barrington_node_false_nil, length_ofPerm]
        exact Nat.one_le_iff_ne_zero.2 (by positivity)
      · rw [barrington_node_true_nil, length_ofPerm]
        exact Nat.one_le_iff_ne_zero.2 (by positivity)
    · rw [barrington_node_singleton]
      have := hchild c₁ (List.mem_singleton.2 rfl) σ
      omega
    · have h₁ := hchild c₁ (List.mem_cons.2 (Or.inl rfl))
      have h₂ := hchild c₂ (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl))))
      rw [mul_comm]
      cases b
      · rw [barrington_node_false_cons_cons, length_complementLast]
        exact length_commutatorProgram_le
          (P₁ := fun ρ => (barrington c₁ ρ⁻¹).complementLast ρ⁻¹)
          (P₂ := fun ρ => (barrington c₂ ρ⁻¹).complementLast ρ⁻¹)
          (fun ρ => by simp only [length_complementLast]; exact h₁ ρ⁻¹)
          (fun ρ => by simp only [length_complementLast]; exact h₂ ρ⁻¹) σ⁻¹
      · rw [barrington_node_true_cons_cons]
        exact length_commutatorProgram_le (P₁ := fun ρ => barrington c₁ ρ)
          (P₂ := fun ρ => barrington c₂ ρ) h₁ h₂ σ

/-- **C14.** Every Barrington program is nonempty: `0 < (barrington c σ).length`.  Glue for
Lemma 2 (`yield_complementLast` needs a last instruction).

**Proof sketch.** Induction on `c` (`TreeCircuit.ind`) generalizing `σ`, by the readers
`barrington_lit_true`, …: leaves have one instruction; fan-in 1 is the child; the `∧` and `∨`
programs contain a child's program (`commutatorProgram_eq`, `length_append`,
`length_complementLast`). -/
theorem barrington_length_pos [NeZero n] (c : TreeCircuit n) (σ : Perm (Fin 5)) :
    0 < (barrington c σ).length := by
  exact barrington_length_pos_aux c σ

/-- **C15.** Every Barrington program is a permutation program: `(barrington c σ).IsPermutation`.
Glue; [Bar89, Thm 1, p003-b002]: "a 5-PBP".

**Proof sketch.** Induction on `c` (`TreeCircuit.ind`) generalizing `σ`: leaves are
`Instr.ofPerm` instructions (`Instr.isPermutation_ofPerm`, `isPermutation_iff`); the `∧` and `∨`
programs are closed under `IsPermutation.append` and `IsPermutation.complementLast`
(`commutatorProgram_eq`). -/
theorem isPermutation_barrington [NeZero n] (c : TreeCircuit n) (σ : Perm (Fin 5)) :
    (barrington c σ).IsPermutation := by
  refine TreeCircuit.ind (motive := fun c => ∀ σ, (barrington c σ).IsPermutation) ?_ ?_ c σ
  · rintro ⟨i, s⟩ σ
    cases s
    · rw [barrington_lit_false]
      exact isPermutation_ofPerm i σ 1
    · rw [barrington_lit_true]
      exact isPermutation_ofPerm i 1 σ
  · intro b cs ih σ
    rcases cs with _ | ⟨c₁, _ | ⟨c₂, cs⟩⟩
    · cases b
      · rw [barrington_node_false_nil]
        exact isPermutation_ofPerm 0 1 1
      · rw [barrington_node_true_nil]
        exact isPermutation_ofPerm 0 σ σ
    · rw [barrington_node_singleton]
      exact ih c₁ (List.mem_singleton.2 rfl) σ
    · have h₁ := ih c₁ (List.mem_cons.2 (Or.inl rfl))
      have h₂ := ih c₂ (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl))))
      cases b
      · rw [barrington_node_false_cons_cons, commutatorProgram_eq]
        exact IsPermutation.complementLast (IsPermutation.append (IsPermutation.append
          (IsPermutation.append ((h₁ _).complementLast _) ((h₂ _).complementLast _))
          ((h₁ _).complementLast _)) ((h₂ _).complementLast _)) _
      · rw [barrington_node_true_cons_cons, commutatorProgram_eq]
        exact IsPermutation.append (IsPermutation.append (IsPermutation.append (h₁ _) (h₂ _))
          (h₁ _)) (h₂ _)

/-- **C16.** BV14's reading from start state `0`: for a fan-in-2 formula and a five-cycle `σ`,
`(barrington c σ).yield x 0 = if c.eval x then σ 0 else 0` [BV14, Thm 3.5, p014-b001; §3.3,
p013-b002].
Deviation: BV14 reads coordinate `1` of a 1-based state; here the start state is `0` and an
accepted input ends at `σ 0 ≠ 0` (r3 §H3.7).

**Proof sketch.** `barrington_recognizes` and `fiveCycleRecognizes_iff`; split on `c.eval x`. -/
theorem barrington_yield_zero [NeZero n] {c : TreeCircuit n} (hc : c.maxFanin ≤ 2)
    {σ : Perm (Fin 5)} (hσ : IsFiveCycle σ) (x : Fin n → Bool) :
    (barrington c σ).yield x 0 = if c.eval x then σ 0 else 0 := by
  have h := barrington_recognizes c hc hσ
  rw [fiveCycleRecognizes_iff] at h
  cases hx : c.eval x
  · rw [(h.2 x).2 (by rw [hx]; exact Bool.false_ne_true)]
    rfl
  · rw [(h.2 x).1 hx]
    rfl

end BranchingProgram
