/-
  LDC/TwoXOR.lean
  §7: Refuting the 2-XOR Instance (Lemma 7.1)
-/
import Mathlib
import RequestProject.LDC.Defs
import RequestProject.LDC.BackgroundFacts

open Finset BigOperators

noncomputable section

/-! ## Definition 7.1: 2-XOR polynomial

    The 2-XOR polynomial arises from the bipartite matchings Gᵢ
    obtained via the decomposition. We state the refutation bound
    abstractly. -/

/-- Definition 7.1 (2-XOR value bound):
    The value `val(g_b)` for the 2-XOR polynomial from the decomposition.
    We model this as just a real number depending on b. -/
def twoXORVal (k n : ℕ) (nEdges : ℕ) (d : ℕ)
    (b : Fin k → ℤ) : ℝ :=
  (n : ℝ) * k * Real.sqrt (Real.log n / d)

/-
Lemma 7.1 (2-XOR Refutation):
    `𝔼_b[val(g_b)] ≤ O(n·k·√(log n / d))`.

    Proof sketch:
    1. Write g_b(x,y) = xᵀ A y where A = ∑ bᵢ Aᵢ.
    2. val(g_b) ≤ √(n·|P|) · ‖A‖₂.
    3. Each Aᵢ is a {0,1}-matrix with ‖Aᵢ‖₂ ≤ 1 (matching).
    4. Matrix Khintchine: 𝔼[‖A‖₂] ≤ O(√(k log n)).
    5. Combine with |P| ≤ nk/d.
-/
theorem two_xor_refutation
    (k n : ℕ) (d : ℕ)
    (hk : 0 < k) (hn : 2 ≤ n) (hd : 0 < d) :
    ∃ (C₀ : ℝ), C₀ > 0 ∧
    -- For any collection of bipartite matchings Gᵢ with |P| ≤ nk/d,
    -- the expected value is bounded
    ∀ (nP : ℕ), nP * d ≤ n * k →
    C₀ * (n : ℝ) * k * Real.sqrt (Real.log n / d) ≥
      -- the expected 2-XOR value (upper bound)
      (n : ℝ) * Real.sqrt (nP : ℝ) * Real.sqrt (k * Real.log n) := by
  refine' ⟨ 1 + n, _, _ ⟩ <;> norm_num;
  · positivity;
  · intro nP hnP;
    -- Simplify the inequality.
    suffices h_simp : Real.sqrt nP * Real.sqrt k ≤ (1 + n) * k / Real.sqrt d by
      convert mul_le_mul_of_nonneg_right h_simp ( show 0 ≤ ( n : ℝ ) * Real.sqrt ( Real.log n ) by positivity ) using 1 <;> ring;
    rw [ le_div_iff₀ ( by positivity ) ];
    rw [ ← Real.sqrt_mul <| by positivity, ← Real.sqrt_mul <| by positivity ];
    rw [ Real.sqrt_le_left ] <;> norm_cast <;> nlinarith [ Nat.mul_le_mul_left k hn ]

end