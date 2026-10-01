/-
Copyright (c) 2026 Yichuan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yichuan Wang
-/
import TCSlib.Complexity.CircuitComplexity.SizeClasses

/-!
# Arora–Barak Claim 6.8: every unary language is in `P/poly`

## Main definitions

* `Language.unary` — the language `{1ⁿ : n ∈ S}`.
* `ACP.notGateOp` / `ACP.constZeroCircuit` — the `NOT` gate and the circuit that
  outputs `0` on every input.
* `ACP.unaryFamily` — [AB09, Claim 6.8]'s circuit family for a unary `L`.

## Main results

* `Language.le_allOnes_iff` — `L ≤ Language.allOnes` says `L ⊆ {1ⁿ : n ∈ ℕ}`.
* `Language.mem_unary_iff`, `Language.unary_le_allOnes`,
  `Language.replicate_mem_unary_iff` — the `Language.unary` API.
* `Language.exists_le_allOnes` — one unary language per `S : Set ℕ`.
* `ACP.unaryFamily_language` — for a unary `L`, the family decides exactly `L`.
* `Language.inSIZE_two_of_le_allOnes` — a unary language is in `SIZE(2)`.
* `Language.inPPoly_of_le_allOnes` / `Language.unary_inPPoly` — [AB09, Claim 6.8],
  in general and for `Language.unary`.

## Design

`AC_GateOps` has no constant gate, so `constZeroCircuit` builds one out of the
two it uses: the empty `AND` is the empty product `1`, and `NOT` of that is `0`.
Hence depth `2` and size `2`.

Whether `1ⁿ ∈ L` is in general undecidable, so `unaryFamily` chooses between the
two branches by `Classical.propDecidable`. The per-length choice is what makes Claim 6.8
true, and is how AB then puts an undecidable language in `P/poly`.

`Language` has a `CompleteAtomicBooleanAlgebra` instance but no `HasSubset`, so
AB's `L ⊆ {1ⁿ : n ∈ ℕ}` is written `L ≤ Language.allOnes`.

AB describes a family of linear size; ours has size `2` at every length, so
`Language.inSIZE_two_of_le_allOnes` states the constant bound and Claim 6.8
follows from it with `a = 2`, `k = 0`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-- A language is below `Language.allOnes` exactly when all its words are `1ⁿ`. -/
theorem Language.le_allOnes_iff (L : Language Bool) :
    L ≤ Language.allOnes ↔ ∀ w ∈ L, ∃ n, w = List.replicate n true := by
  constructor
  · intro h w hw
    exact ⟨w.length, (Language.mem_allOnes_iff w).mp (h hw)⟩
  · intro h w hw
    obtain ⟨n, rfl⟩ := h w hw
    exact fun b hb => List.eq_of_mem_replicate hb

/-- The unary language `{1ⁿ : n ∈ S}`. -/
def Language.unary (S : Set ℕ) : Language Bool :=
  {w | w ∈ Language.allOnes ∧ w.length ∈ S}

/-- Membership in `unary S` is being all ones and having length in `S`. -/
theorem Language.mem_unary_iff {S : Set ℕ} (w : List Bool) :
    w ∈ Language.unary S ↔ w ∈ Language.allOnes ∧ w.length ∈ S := Iff.rfl

/-- `unary S` is a unary language. -/
theorem Language.unary_le_allOnes (S : Set ℕ) : Language.unary S ≤ Language.allOnes :=
  fun _ hw => hw.1

/-- `1ⁿ` belongs to `unary S` exactly when `n ∈ S`. -/
theorem Language.replicate_mem_unary_iff {S : Set ℕ} (n : ℕ) :
    List.replicate n true ∈ Language.unary S ↔ n ∈ S := by
  rw [Language.mem_unary_iff, List.length_replicate]
  exact and_iff_right fun b hb => List.eq_of_mem_replicate hb

/-- For every `S : Set ℕ` some unary language contains exactly the words `1ⁿ`
with `n ∈ S`. -/
theorem Language.exists_le_allOnes (S : Set ℕ) :
    ∃ L : Language Bool, L ≤ Language.allOnes ∧
      ∀ n, List.replicate n true ∈ L ↔ n ∈ S :=
  ⟨Language.unary S, Language.unary_le_allOnes S,
    fun n => Language.replicate_mem_unary_iff n⟩

namespace ACP

open FeedForward

/-- The `NOT` gate, in the shape used by `AC_GateOps`. -/
def notGateOp : GateOp (Fin 2) := ⟨Fin 1, fun x => 1 - x 0⟩

/-- `notGateOp` is one of the `AC_GateOps`. -/
theorem notGateOp_mem_AC_GateOps : notGateOp ∈ AC_GateOps :=
  Set.mem_union_left _ (Set.mem_insert_iff.mpr (Or.inr rfl))

/-- The three layers of `constZeroCircuit n`: the `n` inputs, then two
singleton layers. -/
private def constZeroNodes (n : ℕ) : Fin 3 → Type
  | ⟨0, _⟩ => Fin n
  | ⟨_ + 1, _⟩ => Unit

/-- The depth-2 circuit computing the constant `0` on `n` inputs. -/
def constZeroCircuit (n : ℕ) : FeedForward (Fin 2) (Fin n) Unit where
  depth := 2
  nodes := constZeroNodes n
  gates := fun d => match d with
    | ⟨0, _⟩ => fun _ => ⟨andGateOp 0, fun i => i.elim0⟩
    | ⟨1, _⟩ => fun _ => ⟨notGateOp, fun _ => ()⟩
    | ⟨_ + 2, h⟩ => absurd h (by omega)
  nodes_zero := rfl
  nodes_last := rfl

/-- The circuit outputs `0` whatever its inputs are. -/
@[simp]
theorem constZeroCircuit_eval₁ (n : ℕ) (x : Fin n → Fin 2) :
    (constZeroCircuit n).eval₁ x = 0 := by
  show (1 : Fin 2) - 1 = 0
  rfl

/-- The circuit has two non-input nodes. -/
theorem constZeroCircuit_size (n : ℕ) : (constZeroCircuit n).size = 2 := by
  show Nat.card (Σ _ : Fin 2, Unit) = 2
  simp

/-- Every layer of the circuit is finite. -/
theorem constZeroCircuit_finite (n : ℕ) : (constZeroCircuit n).Finite := by
  rintro ⟨_ | v, hv⟩
  · exact inferInstanceAs (Finite (Fin n))
  · exact inferInstanceAs (Finite Unit)

/-- The circuit uses only `AC_GateOps`. -/
theorem constZeroCircuit_onlyUsesGates (n : ℕ) :
    (constZeroCircuit n).onlyUsesGates AC_GateOps := by
  rintro ⟨_ | _ | d, hd⟩ u
  · exact andGateOp_mem_AC_GateOps 0
  · exact notGateOp_mem_AC_GateOps
  · exact absurd hd (by have : (constZeroCircuit n).depth = 2 := rfl; omega)

open scoped Classical in
/-- [AB09, Claim 6.8]'s family for `L`: the all-ones circuit at the lengths `n`
with `1ⁿ ∈ L`, and the constant-`0` circuit at the others. -/
noncomputable def unaryFamily (L : Language Bool) : CircuitFamily where
  circuit n := if List.replicate n true ∈ L then allOnesCircuit n else constZeroCircuit n
  finite n := by
    by_cases h : List.replicate n true ∈ L
    · rw [if_pos h]; exact allOnesFamily.finite n
    · rw [if_neg h]; exact constZeroCircuit_finite n

/-- At a length with `1ⁿ ∈ L` the family uses `allOnesCircuit n`. -/
theorem unaryFamily_circuit_of_mem {L : Language Bool} {n : ℕ}
    (h : List.replicate n true ∈ L) : (unaryFamily L).circuit n = allOnesCircuit n :=
  if_pos h

/-- At a length with `1ⁿ ∉ L` the family uses `constZeroCircuit n`. -/
theorem unaryFamily_circuit_of_not_mem {L : Language Bool} {n : ℕ}
    (h : List.replicate n true ∉ L) : (unaryFamily L).circuit n = constZeroCircuit n :=
  if_neg h

/-- The family uses only `AC_GateOps`. -/
theorem unaryFamily_onlyUsesGates (L : Language Bool) :
    (unaryFamily L).OnlyUsesGates AC_GateOps := by
  intro n
  by_cases h : List.replicate n true ∈ L
  · rw [unaryFamily_circuit_of_mem h]; exact allOnesFamily_onlyUsesGates n
  · rw [unaryFamily_circuit_of_not_mem h]; exact constZeroCircuit_onlyUsesGates n

/-- Every circuit in the family has size at most `2`. -/
theorem unaryFamily_size_le (L : Language Bool) (n : ℕ) :
    ((unaryFamily L).circuit n).size ≤ 2 := by
  by_cases h : List.replicate n true ∈ L
  · rw [unaryFamily_circuit_of_mem h, allOnesCircuit_size]; omega
  · rw [unaryFamily_circuit_of_not_mem h, constZeroCircuit_size]

/-- For a unary `L`, the family decides exactly `L`.

**Proof sketch.** Every word of a unary `L` is a string of ones, so membership
in `L` splits into two independent conditions: `w` is all ones, and the all-ones
word of `w`'s own length lies in `L`.  Establishing that equivalence is the
first step.  Fix `w` and split on the second condition.  When it holds, the
family runs the all-ones circuit at length `w.length`, which accepts exactly the
all-ones words, so acceptance reduces to the first condition; when it fails, the
family runs the constant-`0` circuit, which accepts nothing, and both sides are
false.  The two cases exhaust the split. -/
theorem unaryFamily_language {L : Language Bool} (hL : L ≤ Language.allOnes) :
    (unaryFamily L).language = L := by
  have key : ∀ w : List Bool,
      w ∈ L ↔ w ∈ Language.allOnes ∧ List.replicate w.length true ∈ L := by
    intro w
    refine ⟨fun hw => ⟨hL hw, ?_⟩, ?_⟩
    · rwa [← (Language.mem_allOnes_iff w).mp (hL hw)]
    · rintro ⟨h₁, h₂⟩
      rwa [(Language.mem_allOnes_iff w).mp h₁]
  ext w
  rw [CircuitFamily.mem_language_iff, key w]
  by_cases h : List.replicate w.length true ∈ L
  · rw [unaryFamily_circuit_of_mem h]
    simp only [h, and_true]
    exact Set.ext_iff.mp allOnesFamily_language w
  · rw [unaryFamily_circuit_of_not_mem h, constZeroCircuit_eval₁]
    simp only [h, and_false, iff_false]
    decide

end ACP

/-- A unary language is decided by circuits of size `2`.  [AB09, Claim 6.8] -/
theorem Language.inSIZE_two_of_le_allOnes {L : Language Bool}
    (hL : L ≤ Language.allOnes) : L.InSIZE (fun _ => 2) :=
  ⟨ACP.unaryFamily L, ACP.unaryFamily_onlyUsesGates L, ACP.unaryFamily_size_le L,
    ACP.unaryFamily_language hL⟩

/-- Every unary language is in `P/poly`.  [AB09, Claim 6.8] -/
theorem Language.inPPoly_of_le_allOnes {L : Language Bool}
    (hL : L ≤ Language.allOnes) : L.InPPoly :=
  (Language.inSIZE_two_of_le_allOnes hL).inPPoly (a := 2) (k := 0) fun _ => by simp

/-- [AB09, Claim 6.8] for `Language.unary S`. -/
theorem Language.unary_inPPoly (S : Set ℕ) : (Language.unary S).InPPoly :=
  Language.inPPoly_of_le_allOnes (Language.unary_le_allOnes S)
