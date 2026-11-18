/-- Left-randomized canonical random DLIN columns and independent uniform base/response
columns have expectation gap at most `1-(1-1/N)³` for every `[0,1]`-valued test. Here `N`
is the finite field cardinality. This is scalar distribution glue for the direct canonical
column route to [Wee20, §2.1, p. 4]; the loss includes zero diagonal scalars.

**Proof sketch.** The augmented three-by-three matrix has determinant `ab(t-r-s)`.
When its three factors are nonzero, use the existing uniform matrix-image law through
transposition and split a uniform three-column output into its first two columns and last
column by standard finite-function equivalences. Bound the gap by one otherwise. Translate
the uniform scalar `t` by `-(r+s)` and apply the published independent-coordinate singleton
and complement probability laws to obtain exact exceptional mass `1-(1-1/N)³`. -/
theorem dlin_random_column_gap_le {K : Type} [Field K] [Fintype K] (rows : ℕ)
    (H : Matrix (Fin rows) (Fin 2) K → (Fin rows → K) → ℝ)
    (hH0 : ∀ M v, 0 ≤ H M v) (hH1 : ∀ M v, H M v ≤ 1) :
    let A : (Fin 2 → K) → Matrix (Fin 3) (Fin 2) K :=
      fun ab => ![![ab 0, 0], ![0, ab 1], ![1, 1]]
    |ProbComp.expect (ProbComp.sample (Fin 2 → K))
        (fun ab => ProbComp.expect (ProbComp.sample (Fin 2 → K))
          (fun rs => ProbComp.expect (ProbComp.sample K)
            (fun t => ProbComp.expect (ProbComp.sample (Matrix (Fin rows) (Fin 3) K))
              (fun L => H (L * A ab)
                (L *ᵥ ![ab 0 * rs 0, ab 1 * rs 1, t]))))) -
      ProbComp.expect (ProbComp.sample (Matrix (Fin rows) (Fin 2) K))
        (fun M => ProbComp.expect (ProbComp.sample (Fin rows → K))
          (fun v => H M v))| ≤
      1 - (1 - 1 / (Fintype.card K : ℝ)) ^ 3 := by
  intro A
  letI : DecidableEq K := Classical.decEq K
  let C (ab rs : Fin 2 → K) (t : K) : Matrix (Fin 3) (Fin 3) K :=
    ![![ab 0, 0, ab 0 * rs 0], ![0, ab 1, ab 1 * rs 1], ![1, 1, t]]
  let split : Matrix (Fin rows) (Fin 3) K ≃
      (Matrix (Fin rows) (Fin 2) K × (Fin rows → K)) :=
    (Equiv.arrowCongr (Equiv.refl (Fin rows)) (Fin.succFunEquiv K 2)).trans
      (Equiv.arrowProdEquivProdArrow (Fin rows) (fun _ => Fin 2 → K) (fun _ => K))
  let F (U : Matrix (Fin rows) (Fin 3) K) : ℝ := H (split U).1 (split U).2
  let P (ab rs : Fin 2 → K) (t : K) : ℝ :=
    ProbComp.expect (ProbComp.sample (Matrix (Fin rows) (Fin 3) K)) fun L =>
      H (L * A ab) (L *ᵥ ![ab 0 * rs 0, ab 1 * rs 1, t])
  let Q : ℝ :=
    ProbComp.expect (ProbComp.sample (Matrix (Fin rows) (Fin 2) K)) fun M =>
      ProbComp.expect (ProbComp.sample (Fin rows → K)) fun v => H M v
  let bad (ab rs : Fin 2 → K) (t : K) : Prop :=
    ab 0 = 0 ∨ ab 1 = 0 ∨ t = rs 0 + rs 1
  change |ProbComp.expect (ProbComp.sample (Fin 2 → K))
      (fun ab => ProbComp.expect (ProbComp.sample (Fin 2 → K))
        (fun rs => ProbComp.expect (ProbComp.sample K) (P ab rs))) - Q| ≤
    1 - (1 - 1 / (Fintype.card K : ℝ)) ^ 3
  -- Read the canonical augmented determinant with the existing three-by-three formula.
  have hDet : ∀ (ab rs : Fin 2 → K) (t : K),
      (C ab rs t).det = ab 0 * ab 1 * (t - rs 0 - rs 1) := sorry
  -- The standard finite-function equivalence separates the first two and final columns.
  have hCoords : ∀ (ab rs : Fin 2 → K) (t : K)
      (L : Matrix (Fin rows) (Fin 3) K),
      split (L * C ab rs t) =
        (L * A ab, L *ᵥ ![ab 0 * rs 0, ab 1 * rs 1, t]) := sorry
  have hSplit :
      ProbComp.expect (ProbComp.sample (Matrix (Fin rows) (Fin 3) K)) F = Q := ?_
  swap
  · dsimp only [F, Q]
    rw [ProbComp.expect_sample_equiv split (fun z => H z.1 z.2),
      ← Bridge.expect_sample_pair]
    simp only [ProbComp.expect_bind, ProbComp.expect_pure]
  -- Nonzero determinant gives surjectivity using the existing matrix-unit readers.
  have hSurj : ∀ (ab rs : Fin 2 → K) (t : K), ¬ bad ab rs t →
      Function.Surjective (Matrix.mulVec (C ab rs t)ᵀ) := ?_
  swap
  · intro ab rs t hbad
    rcases not_or.mp hbad with ⟨ha, hrest⟩
    rcases not_or.mp hrest with ⟨hb, ht⟩
    rw [Matrix.mulVec_surjective_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
      Matrix.det_transpose, hDet, isUnit_iff_ne_zero]
    apply mul_ne_zero (mul_ne_zero ha hb)
    simpa only [sub_sub, sub_ne_zero] using ht
  -- Reuse the generic uniform image through transposition; do not recount its fibers.
  have hUniform : ∀ (ab rs : Fin 2 → K) (t : K), ¬ bad ab rs t →
      ProbComp.expect (ProbComp.sample (Matrix (Fin rows) (Fin 3) K))
          (fun L => F (L * C ab rs t)) =
        ProbComp.expect (ProbComp.sample (Matrix (Fin rows) (Fin 3) K)) F := ?_
  swap
  · intro ab rs t hbad
    have hImage := expect_sample_matrix_mul_of_mulVec_surjective
      (K := K) (r := 3) (m := 3) (c := rows) (C ab rs t)ᵀ (hSurj ab rs t hbad)
      (fun V : Matrix (Fin 3) (Fin rows) K => F Vᵀ)
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose] at hImage
    have hLeft := ProbComp.expect_sample_equiv
      (Matrix.transposeAddEquiv (Fin rows) (Fin 3) K).toEquiv
      (fun S : Matrix (Fin 3) (Fin rows) K => F (Sᵀ * C ab rs t))
    have hRight := ProbComp.expect_sample_equiv
      (Matrix.transposeAddEquiv (Fin rows) (Fin 3) K).toEquiv
      (fun V : Matrix (Fin 3) (Fin rows) K => F Vᵀ)
    simp only [Matrix.transposeAddEquiv_apply, Matrix.transpose_transpose] at hLeft hRight
    exact hLeft.trans (hImage.trans hRight.symm)
  have hGood : ∀ (ab rs : Fin 2 → K) (t : K), ¬ bad ab rs t → P ab rs t = Q := ?_
  swap
  · intro ab rs t hbad
    calc
      P ab rs t = ProbComp.expect (ProbComp.sample (Matrix (Fin rows) (Fin 3) K))
          (fun L => F (L * C ab rs t)) :=
        congrArg (ProbComp.expect (ProbComp.sample (Matrix (Fin rows) (Fin 3) K)))
          (funext (fun L => (congrArg
            (fun z : Matrix (Fin rows) (Fin 2) K × (Fin rows → K) => H z.1 z.2)
            (hCoords ab rs t L)).symm))
      _ = ProbComp.expect (ProbComp.sample (Matrix (Fin rows) (Fin 3) K)) F :=
        hUniform ab rs t hbad
      _ = Q := hSplit
  -- These are averages of the supplied bounded test, on good and bad inputs alike.
  have hP0 (ab rs : Fin 2 → K) (t : K) : 0 ≤ P ab rs t :=
    ProbComp.expect_nonneg (ProbComp.sample (Matrix (Fin rows) (Fin 3) K))
      (fun L => hH0 (L * A ab) (L *ᵥ ![ab 0 * rs 0, ab 1 * rs 1, t]))
  have hP1 (ab rs : Fin 2 → K) (t : K) : P ab rs t ≤ 1 := ?_
  swap
  · calc
      P ab rs t ≤ ProbComp.expect (ProbComp.sample (Matrix (Fin rows) (Fin 3) K))
          (fun _ => 1) :=
        ProbComp.expect_mono (ProbComp.sample (Matrix (Fin rows) (Fin 3) K))
          (fun L => hH1 (L * A ab) (L *ᵥ ![ab 0 * rs 0, ab 1 * rs 1, t]))
      _ = 1 := ProbComp.expect_const (ProbComp.sample (Matrix (Fin rows) (Fin 3) K)) 1
  have hQ0 : 0 ≤ Q :=
    ProbComp.expect_nonneg (ProbComp.sample (Matrix (Fin rows) (Fin 2) K)) fun M =>
      ProbComp.expect_nonneg (ProbComp.sample (Fin rows → K)) fun v => hH0 M v
  have hQ1 : Q ≤ 1 := ?_
  swap
  · calc
      Q ≤ ProbComp.expect (ProbComp.sample (Matrix (Fin rows) (Fin 2) K))
          (fun _ => 1) :=
        ProbComp.expect_mono (ProbComp.sample (Matrix (Fin rows) (Fin 2) K)) fun M =>
          calc
            ProbComp.expect (ProbComp.sample (Fin rows → K)) (fun v => H M v) ≤
                ProbComp.expect (ProbComp.sample (Fin rows → K)) (fun _ => 1) :=
              ProbComp.expect_mono (ProbComp.sample (Fin rows → K)) (fun v => hH1 M v)
            _ = 1 := ProbComp.expect_const (ProbComp.sample (Fin rows → K)) 1
      _ = 1 := ProbComp.expect_const (ProbComp.sample (Matrix (Fin rows) (Fin 2) K)) 1
  -- Translate the uniform t by -(r+s), then reuse coordinate independence and complement.
  have hBadMass :
      ProbComp.expect (ProbComp.sample (Fin 2 → K))
          (fun ab => ProbComp.expect (ProbComp.sample (Fin 2 → K))
            (fun rs => ProbComp.expect (ProbComp.sample K)
              (fun t => if bad ab rs t then (1 : ℝ) else 0))) =
        1 - (1 - 1 / (Fintype.card K : ℝ)) ^ 3 := sorry
  have hPoint (ab rs : Fin 2 → K) (t : K) :
      |P ab rs t - Q| ≤ if bad ab rs t then (1 : ℝ) else 0 := ?_
  swap
  · by_cases hbad : bad ab rs t
    · rw [if_pos hbad, abs_le]
      constructor <;> linarith [hP0 ab rs t, hP1 ab rs t, hQ0, hQ1]
    · simpa only [if_neg hbad, hGood ab rs t hbad, sub_self, abs_zero] using
        (le_refl (0 : ℝ))
  -- Average first over t, then over its independent coefficient pair and base pair.
  have hAtT (ab rs : Fin 2 → K) :
      |ProbComp.expect (ProbComp.sample K) (P ab rs) - Q| ≤
        ProbComp.expect (ProbComp.sample K)
          (fun t => if bad ab rs t then (1 : ℝ) else 0) := ?_
  swap
  · have h := ProbComp.abs_expect_sub_le_expect (ProbComp.sample K)
      (f := P ab rs) (g := fun _ => Q)
      (h := fun t => if bad ab rs t then (1 : ℝ) else 0) (hPoint ab rs)
    rw [ProbComp.expect_const (ProbComp.sample K) Q] at h
    exact h
  have hAtRS (ab : Fin 2 → K) :
      |ProbComp.expect (ProbComp.sample (Fin 2 → K))
          (fun rs => ProbComp.expect (ProbComp.sample K) (P ab rs)) - Q| ≤
        ProbComp.expect (ProbComp.sample (Fin 2 → K))
          (fun rs => ProbComp.expect (ProbComp.sample K)
            (fun t => if bad ab rs t then (1 : ℝ) else 0)) := ?_
  swap
  · have h := ProbComp.abs_expect_sub_le_expect (ProbComp.sample (Fin 2 → K))
      (f := fun rs => ProbComp.expect (ProbComp.sample K) (P ab rs))
      (g := fun _ => Q)
      (h := fun rs => ProbComp.expect (ProbComp.sample K)
        (fun t => if bad ab rs t then (1 : ℝ) else 0)) (hAtT ab)
    rw [ProbComp.expect_const (ProbComp.sample (Fin 2 → K)) Q] at h
    exact h
  have hAverage := ProbComp.abs_expect_sub_le_expect (ProbComp.sample (Fin 2 → K))
    (f := fun ab => ProbComp.expect (ProbComp.sample (Fin 2 → K))
      (fun rs => ProbComp.expect (ProbComp.sample K) (P ab rs)))
    (g := fun _ => Q)
    (h := fun ab => ProbComp.expect (ProbComp.sample (Fin 2 → K))
      (fun rs => ProbComp.expect (ProbComp.sample K)
        (fun t => if bad ab rs t then (1 : ℝ) else 0))) hAtRS
  rw [ProbComp.expect_const (ProbComp.sample (Fin 2 → K)) Q, hBadMass] at hAverage
  exact hAverage
