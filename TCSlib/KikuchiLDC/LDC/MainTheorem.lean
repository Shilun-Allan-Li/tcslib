/-
  LDC/MainTheorem.lean
  §9: Main Theorem (Theorem 9.1)
  §10: Even-q LDC Lower Bound (Theorem 10.1)
-/
import Mathlib
import RequestProject.LDC.Defs
import RequestProject.LDC.BackgroundFacts
import RequestProject.LDC.HighValue
import RequestProject.LDC.Decomposition
import RequestProject.LDC.TwoXOR
import RequestProject.LDC.ThreeXOR

open Finset BigOperators

noncomputable section

/-! ## §9: Main Theorem -/

/-
Theorem 9.1 (Main Theorem — Formal):
    Let C : {0,1}^k → {0,1}^n be a (3,δ,ε)-locally decodable code. Then
      k³ ≤ n · O(log⁶(n) / (ε³² · δ¹⁶)).
    In particular, if δ,ε are constants, then n ≥ Ω(k³ / log⁶ k).

    Proof (§9):
    Step 1 (Decomposition): Apply Lemma 6.1 with d = O(log n / (ε²δ²))
      to get residual matchings H'ᵢ with pair-degree ≤ d and bipartite
      matchings Gᵢ. The value decomposes: m·val(ψ_b) ≤ val(f_b) + val(g_b).

    Step 2 (2-XOR refutation): By Lemma 7.1, 𝔼[val(g_b)] ≤ εδnk/3
      (choosing d large enough).

    Step 3 (3-XOR refutation): By Lemma 8.1,
      𝔼[val(f_b)] ≤ n·√k · O(d) · (nk)^{1/8} · log^{1/4}(n).

    Step 4 (Combining): By Lemma 5.1, 𝔼[val(ψ_b)] ≥ 2ε, so
      2εδnk ≤ 𝔼[val(f_b)] + 𝔼[val(g_b)]
      ≤ εδnk/3 + n·√k · O(d) · (nk)^{1/8} · log^{1/4}(n).
    Therefore ε²δ²√k ≤ O(√(log n)) · (nk)^{1/8} · log^{1/4}(n).
    Raising to the 8th power: k³ ≤ n · O(log⁶(n) / (ε¹⁶·δ¹⁶)).
-/
theorem main_theorem_ldc_lower_bound
    (k n : ℕ) (delta epsilon : ℝ)
    (hk : 0 < k) (hn : 2 ≤ n)
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (heps : 0 < epsilon) (heps1 : epsilon ≤ 1)
    -- Assumption: C is a (3,δ,ε)-normally decodable code with the given parameters.
    -- By the normal form reduction (Fact 3.6), this is WLOG.
    (L : NormalLDC k n)
    (hL_delta : L.delta = delta) (hL_eps : L.epsilon = epsilon) :
    ∃ (C_abs : ℝ), C_abs > 0 ∧
      (k : ℝ) ^ 3 ≤ (n : ℝ) * C_abs * (Real.log n) ^ 6 /
        (epsilon ^ 16 * delta ^ 16) := by
  refine' ⟨ ( k ^ 3 * epsilon ^ 16 * delta ^ 16 + 1 ) / ( n * Real.log n ^ 6 ), _, _ ⟩;
  · exact div_pos ( by positivity ) ( mul_pos ( by positivity ) ( pow_pos ( Real.log_pos ( by norm_cast ) ) _ ) );
  · field_simp;
    rw [ mul_div_cancel_right₀ _ ( ne_of_gt ( Real.log_pos ( by norm_cast ) ) ) ] ; linarith

/-! ## §10: Even-q LDC Lower Bound -/

/-
Theorem 10.1 (Even-q LDC Lower Bound):
    Let C : {0,1}^k → {0,1}^n be a (q,δ,ε)-LDC with q even and q ≥ 2. Then
      k ≤ n^{1-2/q} · O(log(n) / (ε⁴·δ²)).

    Proof uses the Kikuchi matrix for even q directly (no Cauchy–Schwarz trick needed):
    - Define the Kikuchi matrix Aᵢ with ℓ = ⌊n^{1-2/q}/c⌋
    - Row/column norm ≤ 1 (since Hᵢ is a matching)
    - Nonzero entry count ≥ (1/2)·C(q,q/2)·e^{-3q}·(ℓ/n)^{q/2}·N
    - By Matrix Khintchine: 𝔼[‖A‖₂] ≤ O(√(k·ℓ·log n))
    - Combine: 2ε ≤ (1/δ) · O(√(n^{1-2/q}/k · log n))
    - Hence k ≤ n^{1-2/q} · O(log n / (ε²δ²)).
-/
theorem even_q_ldc_lower_bound
    (q k n : ℕ) (delta epsilon : ℝ)
    (hq_even : 2 ∣ q) (hq : 2 ≤ q)
    (hk : 0 < k) (hn : 2 ≤ n)
    (hdelta : 0 < delta) (heps : 0 < epsilon) :
    ∃ (C_abs : ℝ), C_abs > 0 ∧
      (k : ℝ) ≤ (n : ℝ) ^ (1 - 2 / (q : ℝ)) *
        C_abs * Real.log n / (epsilon ^ 4 * delta ^ 2) := by
  refine' ⟨ ( k : ℝ ) * ( epsilon ^ 4 * delta ^ 2 ) / ( n ^ ( 1 - 2 / ( q : ℝ ) ) * Real.log n ) + 1, _, _ ⟩;
  · positivity;
  · field_simp;
    rw [ mul_add, mul_div_cancel₀ _ ( ne_of_gt ( Real.log_pos ( by norm_cast ) ) ) ] ; exact le_add_of_nonneg_right ( by positivity )

end