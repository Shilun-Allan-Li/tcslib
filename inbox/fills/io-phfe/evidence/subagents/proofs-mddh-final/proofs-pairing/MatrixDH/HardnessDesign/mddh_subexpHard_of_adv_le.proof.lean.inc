/-- A machine-wise bound by a fixed polynomial times one DLIN advantage plus a common
subexponentially small correction transfers subexponential DLIN hardness to uniform-matrix
MDDH. The resulting positive exponent is fixed before the MDDH adversary is chosen.
Each chosen DLIN machine must satisfy the bound at all security parameters.

**Proof sketch.** Read DLIN's common exponent `a>0` and choose `η=min(a,1)/4` before D.
Use the fixed polynomial majorant and mul_pow/const_mul to reach exponent `2η` for the
weighted DLIN advantage. The correction has that same exponent; add at exponent `η`
and use pointwise domination. No generic polynomial-closure lemma is introduced. -/
theorem mddh_subexpHard_of_adv_le (G : BilinearGen) (d ℓ : PolyExpr) (β : ℕ → ℝ)
    (hβ : ∀ c : ℝ, 0 < c → c < 1 → SubexpSmall c β)
    (hBound : ∀ D : NUPPT, ∃ B : NUPPT, ∀ κ,
      G.mddhAdv d ℓ D κ ≤ (d.eval κ : ℝ) * G.dlinAdv B κ + β κ)
    (h : G.SubexpDLIN) : SubexpHard (G.mddhAdv d ℓ) := by
  obtain ⟨a, ha, hA⟩ := (subexpHard_iff G.dlinAdv).1 (G.subexpDLIN_iff.1 h)
  let η : ℝ := min a 1 / 4
  have hmin₀ : 0 < min a (1 : ℝ) := lt_min ha zero_lt_one
  have hη₀ : 0 < η := ?_
  swap
  · dsimp only [η]
    linarith only [hmin₀]
  have h3a : 3 * η < a := ?_
  swap
  · have hmin := min_le_left a (1 : ℝ)
    dsimp only [η]
    linarith only [hmin, ha]
  have h21 : 2 * η < 1 := ?_
  swap
  · have hmin := min_le_right a (1 : ℝ)
    dsimp only [η]
    linarith only [hmin]
  have h3₀ : 0 < 3 * η := ?_
  swap
  · linarith only [hη₀]
  have h2₀ : 0 < 2 * η := ?_
  swap
  · linarith only [hη₀]
  have h23 : 2 * η < 3 * η := ?_
  swap
  · linarith only [hη₀]
  have hη2 : η < 2 * η := ?_
  swap
  · linarith only [hη₀]
  obtain ⟨C, k, hC⟩ := d.eval_le
  refine (subexpHard_iff _).2 ⟨η, hη₀, ?_⟩
  intro D
  obtain ⟨B, hB⟩ := hBound D
  have hbase := ((hA B).mul_pow ha h3a k).const_mul h3₀ h23 ((C : ℝ) * 2 ^ k)
  have hweighted : SubexpSmall (2 * η)
      (fun κ => (d.eval κ : ℝ) * G.dlinAdv B κ) := ?_
  swap
  · refine hbase.mono ⟨1, ?_⟩
    intro κ hκ
    have hκ₁ : (1 : ℝ) ≤ κ := Nat.one_le_cast.mpr hκ
    have hd : (d.eval κ : ℝ) ≤ (C : ℝ) * ((κ : ℝ) + 1) ^ k := ?_
    swap
    · exact_mod_cast hC κ
    have hstep : (κ : ℝ) + 1 ≤ 2 * (κ : ℝ) := ?_
    swap
    · linarith only [hκ₁]
    have hpoly : (d.eval κ : ℝ) ≤ (C : ℝ) * 2 ^ k * (κ : ℝ) ^ k := ?_
    swap
    · calc
        _ ≤ (C : ℝ) * (2 * (κ : ℝ)) ^ k :=
          hd.trans (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (add_nonneg (Nat.cast_nonneg _) zero_le_one) hstep k)
            (Nat.cast_nonneg _))
        _ = (C : ℝ) * 2 ^ k * (κ : ℝ) ^ k := ?_
      rw [_root_.mul_pow, mul_assoc]
    have hAdv : 0 ≤ G.dlinAdv B κ := ?_
    swap
    · rw [G.dlinAdv_eq B κ]
      exact advantage_nonneg _ _
    have hbase₀ : 0 ≤ ((C : ℝ) * 2 ^ k) * ((κ : ℝ) ^ k * G.dlinAdv B κ) :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg zero_le_two _))
        (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hAdv)
    rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hAdv), abs_of_nonneg hbase₀]
    calc
      _ ≤ ((C : ℝ) * 2 ^ k * (κ : ℝ) ^ k) * G.dlinAdv B κ :=
        mul_le_mul_of_nonneg_right hpoly hAdv
      _ = _ := mul_assoc _ _ _
  have hsum := hweighted.add (hβ (2 * η) h2₀ h21) h2₀ hη2
  refine hsum.mono ⟨0, ?_⟩
  intro κ _
  have hM : 0 ≤ G.mddhAdv d ℓ D κ := ?_
  swap
  · rw [G.mddhAdv_eq d ℓ D κ]
    exact advantage_nonneg _ _
  rw [abs_of_nonneg hM]
  exact (hB κ).trans (le_abs_self _)
