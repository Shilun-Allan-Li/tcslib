/-- A uniform matrix with two columns and at most two rows fails surjectivity with
probability at most `2/|K|`. This is the exact rank-failure obligation for small-row MDDH.

**Proof sketch.** Split the row count into zero, one and two. Zero rows are automatically
surjective. One row fails only at the zero row, with mass `|K|⁻²`. For two rows use the
existing finite-field general-linear cardinality formula to obtain singular mass
`|K|⁻¹+|K|⁻²-|K|⁻³ ≤ 2/|K|`. -/
theorem smallRows_surjectivity_failure_le {K : Type} [Field K] [Fintype K]
    (r : ℕ) (hr : r ≤ 2) :
    ProbComp.prob (ProbComp.sample (Matrix (Fin r) (Fin 2) K))
        (fun M => ¬ Function.Surjective (Matrix.mulVec M)) ≤
      2 / (Fintype.card K : ℝ) := by
  classical
  let q : ℕ := Fintype.card K
  have hq2 : 2 ≤ q := Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
  have hq1 : 1 ≤ q := (Nat.le_add_right 1 1).trans hq2
  have hq : (1 : ℝ) ≤ (q : ℝ) := Nat.one_le_cast.mpr hq1
  have hqpos : (0 : ℝ) < (q : ℝ) := lt_of_lt_of_le zero_lt_one hq
  have hrecip : (1 : ℝ) / (q : ℝ) ^ 2 ≤ 1 / (q : ℝ) := ?_
  swap
  · simpa only [pow_one] using
      one_div_pow_le_one_div_pow_of_le hq (Nat.le_add_right 1 1)
  have htwo : (2 : ℝ) / (q : ℝ) = 2 * (1 / (q : ℝ)) := by ring
  cases r with
  | zero =>
      have hs : ∀ M : Matrix (Fin 0) (Fin 2) K,
          Function.Surjective (Matrix.mulVec M) := ?_
      swap
      · intro M y
        exact ⟨0, Subsingleton.elim _ _⟩
      simp only [ProbComp.prob_eq_expect, hs, not_true_eq_false, if_false,
        ProbComp.expect_const]
      positivity
  | succ r =>
      cases r with
      | zero =>
          have hbad : ∀ M : Matrix (Fin 1) (Fin 2) K,
              ¬ Function.Surjective (Matrix.mulVec M) → M = 0 := ?_
          swap
          · intro M hM
            let e : (Fin 1 → K) ≃ₗ[K] K := LinearEquiv.funUnique (Fin 1) K K
            let L : Module.Dual K (Fin 2 → K) :=
              e.toLinearMap.comp (Matrix.mulVecLin M)
            have hL : L = 0 := ?_
            swap
            · by_contra hL
              apply hM
              have hsurj : Function.Surjective L :=
                LinearMap.range_eq_top.mp (Module.Dual.range_eq_top_of_ne_zero hL)
              exact (Equiv.comp_surjective (Matrix.mulVec M) e.toEquiv).mp hsurj
            ext i j
            change M i j = 0
            have he : e (M *ᵥ Pi.single j 1) = 0 :=
              congrArg (fun F : Module.Dual K (Fin 2 → K) => F (Pi.single j 1)) hL
            rw [Matrix.mulVec_single_one] at he
            change (LinearEquiv.funUnique (Fin 1) K K) (M.col j) = 0 at he
            rw [LinearEquiv.funUnique_apply] at he
            change M default j = 0 at he
            have hi : i = (default : Fin 1) := Subsingleton.elim _ _
            simpa only [hi] using he
          have hzero : uprob (fun M : Matrix (Fin 1) (Fin 2) K => M = 0) =
              1 / (q : ℝ) ^ 2 := ?_
          swap
          · rw [TCSlib.Cryptography.OneWay.uprob_eq_one_div_card]
            change (1 : ℝ) / (Fintype.card (Fin 1 → Fin 2 → K) : ℝ) = _
            simp only [Fintype.card_fun, Fintype.card_fin, pow_one, Nat.cast_pow]
            rfl
          rw [Bridge.prob_sample_eq_uprob]
          refine le_trans (uprob_mono hbad) ?_
          rw [hzero]
          have hx0 : (0 : ℝ) ≤ 1 / (q : ℝ) := one_div_nonneg.mpr hqpos.le
          change (1 : ℝ) / (q : ℝ) ^ 2 ≤ 2 / (q : ℝ)
          rw [htwo]
          nlinarith only [hrecip, hx0]
      | succ r =>
          have hr0 : r = 0 := ?_
          swap
          · omega
          subst r
          have hgood : Nat.card {M : Matrix (Fin 2) (Fin 2) K //
              Function.Surjective (Matrix.mulVec M)} =
              (q ^ 2 - 1) * (q ^ 2 - q) := ?_
          swap
          · simp only [Matrix.mulVec_surjective_iff_isUnit]
            change Nat.card (Set.range (Units.val :
              (Matrix (Fin 2) (Fin 2) K)ˣ → Matrix (Fin 2) (Fin 2) K)) = _
            rw [Nat.card_range_of_injective Units.val_injective]
            simpa only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one,
              pow_zero, pow_one] using (Matrix.card_GL_field (𝔽 := K) 2)
          have hall : Fintype.card (Matrix (Fin 2) (Fin 2) K) = q ^ 4 := ?_
          swap
          · change Fintype.card (Fin 2 → Fin 2 → K) = q ^ 4
            simp only [Fintype.card_fun, Fintype.card_fin]
            exact (pow_mul q 2 2).symm
          have hsq1 : 1 ≤ q ^ 2 := one_le_pow₀ hq1
          have hsqq : q ≤ q ^ 2 := le_self_pow₀ hq1 (Nat.succ_ne_zero 1)
          rw [Bridge.prob_sample_eq_uprob, uprob_not, uprob_def, hgood, hall]
          simp only [Nat.cast_mul, Nat.cast_sub hsq1, Nat.cast_sub hsqq,
            Nat.cast_pow, Nat.cast_one]
          change 1 - (((q : ℝ) ^ 2 - 1) * ((q : ℝ) ^ 2 - q)) /
              (q : ℝ) ^ 4 ≤ 2 / (q : ℝ)
          have hformula : 1 - (((q : ℝ) ^ 2 - 1) * ((q : ℝ) ^ 2 - q)) /
              (q : ℝ) ^ 4 =
              1 / (q : ℝ) + 1 / (q : ℝ) ^ 2 - 1 / (q : ℝ) ^ 3 := ?_
          swap
          · field_simp [ne_of_gt hqpos] <;> ring
          rw [hformula]
          have hz0 : (0 : ℝ) ≤ 1 / (q : ℝ) ^ 3 :=
            one_div_nonneg.mpr (pow_nonneg hqpos.le 3)
          rw [htwo]
          linarith only [hrecip, hz0]
