/-
Copyright (c) 2026 Yichuan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yichuan Wang
-/
import TCSlib.Complexity.CircuitComplexity.LayeredDAG

/-!
# `SIZE` monotonicity, and Arora–Barak Example 6.3

## Main definitions

* `Language.allOnes` — the language `{1ⁿ}` of [AB09, Ex 6.3], part 1.
* `BoolCircuit.andGateOp` — the unbounded fan-in `AND` gate.
* `BoolCircuit.allOnesCircuit` / `BoolCircuit.allOnesFamily` — the circuit and family deciding it.

## Main results

* `Language.InLayeredSIZE.mono` — `SIZE(T) ⊆ SIZE(T')` when `T ≤ T'` pointwise.
* `Language.InLayeredSIZE.inLayeredPPoly` — `SIZE(T) ⊆ P/poly` when `T n ≤ a * (n + 1) ^ k`.
* `Language.allOnes_inLayeredSIZE_linear` / `_inLayeredPPoly` — `{1ⁿ}` is linear-size, so in `P/poly`;
  `Language.allOnes_inPPoly` — the same for the book's `P/poly`.

## Divergences from Arora–Barak Example 6.3

AB's circuit is a tree of fan-in-2 `AND` gates (`n - 1` non-input vertices, depth
`⌈log₂ n⌉`); ours is one unbounded `AND` gate (`size = 1`, depth `1`), the same
function in the unbounded-fan-in basis `LayeredPPoly.lean` fixes — both linear-size,
which is all AB claims. AB writes `{1ⁿ : n ∈ ℤ}`; we read that `ℤ` as `ℕ`, since
`1ⁿ` names no word for `n < 0`, so `n = 0` is in and the empty `AND` gate, being
the empty product `1`, makes `C₀` accept `ε = 1⁰`. Words are `List Bool`, so AB's
letter `1` is `true`, and `finTwoEquiv` converts at the circuit boundary.

## Deferred: Theorem 6.6, `P ⊆ P/poly`

Not formalized, and not stubbed with `sorry`. AB simulates an oblivious Turing
machine (Remark 1.7) by a circuit, Cook–Levin style, which needs a machine model,
the class `P`, and the oblivious-simulation theorem. All three now live on this
branch (`TuringMachine/` with `Robustness/ObliviousSchedule.lean`, and
`ClassP/`); the bridge theorem is tracked in `backlog.md` §3.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-- `SIZE(T) ⊆ SIZE(T')` whenever `T ≤ T'` pointwise. -/
theorem Language.InLayeredSIZE.mono {T T' : ℕ → ℕ} {L : Language Bool} (hL : L.InLayeredSIZE T)
    (h : ∀ n, T n ≤ T' n) : L.InLayeredSIZE T' := by
  obtain ⟨C, hG, hS, hC⟩ := hL
  exact ⟨C, hG, fun n => (hS n).trans (h n), hC⟩

/-- A language in `SIZE(T)` for a polynomially bounded `T` is in `P/poly`. -/
theorem Language.InLayeredSIZE.inLayeredPPoly {T : ℕ → ℕ} {L : Language Bool} {a k : ℕ}
    (hL : L.InLayeredSIZE T) (hT : ∀ n, T n ≤ a * (n + 1) ^ k) : L.InLayeredPPoly :=
  ⟨a, k, hL.mono hT⟩

/-- `finTwoEquiv` sends `true`, and only `true`, to `1`. -/
private theorem finTwoEquiv_symm_eq_one_iff (b : Bool) :
    finTwoEquiv.symm b = 1 ↔ b = true := by
  cases b <;> decide

/-- `{1ⁿ : n ∈ ℕ}`, the words all of whose letters are `true`.  [AB09, Ex 6.3] -/
def Language.allOnes : Language Bool := {w | ∀ b ∈ w, b = true}

/-- `Language.allOnes` is the set of words `1ⁿ`. -/
theorem Language.mem_allOnes_iff (w : List Bool) :
    w ∈ Language.allOnes ↔ w = List.replicate w.length true :=
  List.eq_replicate_length.symm

namespace BoolCircuit

open LayeredCircuit

/-- The unbounded fan-in `AND` gate on `w` inputs, in the shape used by `stdGateOps`. -/
def andGateOp (w : ℕ) : GateOp (Fin 2) := ⟨Fin w, fun x => ∏ i, x i⟩

/-- `andGateOp w` is one of the `stdGateOps`. -/
theorem andGateOp_mem_stdGateOps (w : ℕ) : andGateOp w ∈ stdGateOps :=
  Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨w, rfl⟩)

/-- Over `Fin 2` a product is `1` exactly when every factor is. -/
theorem prod_fin_two_eq_one_iff {ι : Type*} [Fintype ι] (x : ι → Fin 2) :
    ∏ i, x i = 1 ↔ ∀ i, x i = 1 := by
  classical
  constructor
  · intro h i
    rw [← Finset.mul_prod_erase _ x (Finset.mem_univ i)] at h
    exact (by decide : ∀ a b : Fin 2, a * b = 1 → a = 1) _ _ h
  · exact fun h => Finset.prod_eq_one fun i _ => h i

/-- The two layers of `allOnesCircuit n`: the `n` inputs, then the single output. -/
private def allOnesNodes (n : ℕ) : Fin 2 → Type
  | ⟨0, _⟩ => Fin n
  | ⟨_ + 1, _⟩ => Unit

/-- The depth-1 circuit taking the `AND` of all `n` inputs.  [AB09, Ex 6.3] -/
def allOnesCircuit (n : ℕ) : LayeredCircuit (Fin 2) (Fin n) Unit where
  depth := 1
  nodes := allOnesNodes n
  gates := fun d => match d with
    | ⟨0, _⟩ => fun _ => ⟨andGateOp n, fun i => i⟩
    | ⟨_ + 1, h⟩ => absurd h (by omega)
  nodes_zero := rfl
  nodes_last := rfl

/-- The circuit outputs the product, that is the `AND`, of its inputs. -/
@[simp]
theorem allOnesCircuit_eval₁ (n : ℕ) (x : Fin n → Fin 2) :
    (allOnesCircuit n).eval₁ x = ∏ i, x i := rfl

/-- The circuit has a single non-input node, so `size = 1` for every `n`. -/
theorem allOnesCircuit_size (n : ℕ) : (allOnesCircuit n).size = 1 := by
  show Nat.card (Σ _ : Fin 1, Unit) = 1
  simp

/-- The family of [AB09, Ex 6.3], part 1. -/
def allOnesFamily : LayeredCircuitFamily where
  circuit := allOnesCircuit
  finite n := by
    rintro ⟨_ | v, hv⟩
    · exact inferInstanceAs (Finite (Fin n))
    · exact inferInstanceAs (Finite Unit)

/-- The family's length-`n` circuit is `allOnesCircuit n`. -/
@[simp]
theorem allOnesFamily_circuit (n : ℕ) : allOnesFamily.circuit n = allOnesCircuit n := rfl

/-- The family uses only `stdGateOps`. -/
theorem allOnesFamily_onlyUsesGates : allOnesFamily.OnlyUsesGates stdGateOps := by
  intro n
  show (allOnesCircuit n).onlyUsesGates stdGateOps
  rintro ⟨_ | d, hd⟩ u
  · exact andGateOp_mem_stdGateOps n
  · exact absurd hd (by have : (allOnesCircuit n).depth = 1 := rfl; omega)

/-- The family decides exactly `Language.allOnes`. -/
theorem allOnesFamily_language : allOnesFamily.language = Language.allOnes := by
  ext w
  simp only [LayeredCircuitFamily.mem_language_iff, allOnesFamily_circuit, allOnesCircuit_eval₁,
    prod_fin_two_eq_one_iff, finTwoEquiv_symm_eq_one_iff, Language.allOnes,
    List.get_eq_getElem, List.forall_mem_iff_getElem]
  exact ⟨fun h i hi => h ⟨i, hi⟩, fun h i => h i i.2⟩

end BoolCircuit

/-- `{1ⁿ} ∈ SIZE(1)`. -/
theorem Language.allOnes_inLayeredSIZE_one : Language.allOnes.InLayeredSIZE (fun _ => 1) :=
  ⟨BoolCircuit.allOnesFamily, BoolCircuit.allOnesFamily_onlyUsesGates,
    fun n => (BoolCircuit.allOnesCircuit_size n).le, BoolCircuit.allOnesFamily_language⟩

/-- [AB09, Ex 6.3], part 1: `{1ⁿ}` is decided by a linear-size circuit family. -/
theorem Language.allOnes_inLayeredSIZE_linear : Language.allOnes.InLayeredSIZE (fun n => n + 1) :=
  Language.allOnes_inLayeredSIZE_one.mono fun n => Nat.succ_le_succ n.zero_le

/-- [AB09, Ex 6.3], part 1: consequently `{1ⁿ} ∈ P/poly`. -/
theorem Language.allOnes_inLayeredPPoly : Language.allOnes.InLayeredPPoly :=
  Language.allOnes_inLayeredSIZE_linear.inLayeredPPoly (a := 1) (k := 1) fun n => by simp

/-- `{1ⁿ} ∈ P/poly` for the book's `P/poly`.  [AB09, Ex 6.3] -/
theorem Language.allOnes_inPPoly : Language.allOnes.InPPoly :=
  Language.allOnes_inLayeredPPoly.inPPoly
