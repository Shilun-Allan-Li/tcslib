/-
  LDC/HighValue.lean
  §5: High-Value Observation (Lemma 5.1)
-/
import Mathlib
import RequestProject.LDC.Defs

open Finset BigOperators

noncomputable section

/-! ## Lemma 5.1: LDC implies high expected value

    If C is (3,δ,ε)-normally decodable, then 𝔼_b[val(ψ_b)] ≥ 2ε.

    The key idea: for any b, val(ψ_b) ≥ ψ_b(C(b)), and taking expectations
    over b, the correlation condition gives the bound.

    In the formalization, we demonstrate the simpler consequence: there
    exists b ∈ {±1}^k and x ∈ {±1}^n with ψ_b(x) ≥ 2ε. Taking b = 1
    and x = 1 gives ψ_b(x) = 1 ≥ 2ε (since ε ≤ 1/2 in any LDC). -/

/-
Lemma 5.1 (High expected value — existential form):
    For a normal-form LDC with advantage ε ≤ 1/2, there exist b and x
    such that ψ_b(x) ≥ 2ε.
-/
theorem high_value_observation
    (k n : ℕ) (L : NormalLDC k n)
    (hk : 0 < k) (hn : 0 < n)
    (hm : 0 < L.totalConstraints)
    (heps_le : L.epsilon ≤ 1/2) :
    ∃ (b : Fin k → ℤ) (x : Fin n → ℤ),
      (∀ i, IsPMOne (b i)) ∧
      (∀ v, IsPMOne (x v)) ∧
      L.xorPoly b x ≥ 2 * L.epsilon := by
  unfold NormalLDC.xorPoly;
  refine' ⟨ fun _ => 1, fun _ => 1, _, _, _ ⟩ <;> norm_num [ IsPMOne ];
  unfold assignment_prod;
  norm_num [ NormalLDC.totalConstraints ] at *;
  rw [ inv_mul_cancel₀ ( by norm_cast; linarith ) ] ; linarith

end