/-- The two random presentations differ by at most the probability of a zero diagonal
coordinate [GJLS21, Definition 3.3, p. 18; JLS26, §1.1, p. 3]. This correction is explicit;
the source presentations are not asserted to have identical random laws.

**Proof sketch.** Condition on the diagonal scalars. Off the zero-coordinate event,
multiplication by each nonzero scalar bijects its uniform mask with a uniform response.
Use `expect_sample_equiv` for those bijections. Bound the acceptance difference by one on
the exceptional event, whose exact probability is `2/p - 1/p^2`, and average over group coins. -/
theorem dlinMatrixGame_random_gap_le (D : NUPPT) (κ : ℕ) :
    |accept (G.dlinMatrixGame D false κ) - accept (G.dlinGame D false κ)| ≤
      G.dlinMatrixSlack κ := by
  classical
  let H (pp : PublicParams G κ) (ab : Fin 2 → ZMod pp.group.order)
      (u : Fin 3 → ZMod pp.group.order) : ℝ :=
    ProbComp.prob (ProbComp.sample (D.Coins κ)) fun r =>
      D.distinguisherL κ
        (G.dlinEnc κ (G.dlinChallenge κ pp
          (pp.generator ^ (ab 0).val) (pp.generator ^ (ab 1).val)
          (pp.generator ^ (u 0).val) (pp.generator ^ (u 1).val)
          (pp.generator ^ (u 2).val))) r = true
  let P (pp : PublicParams G κ) : ℝ :=
    ProbComp.expect (ProbComp.sample (Fin 2 → ZMod pp.group.order)) fun ab =>
      ProbComp.expect (ProbComp.sample (Fin 3 → ZMod pp.group.order)) (H pp ab)
  let Q (pp : PublicParams G κ) : ℝ :=
    ProbComp.expect (ProbComp.sample (Fin 2 → ZMod pp.group.order)) fun ab =>
      ProbComp.expect (ProbComp.sample (Fin 2 → ZMod pp.group.order)) fun rs =>
        ProbComp.expect (ProbComp.sample (ZMod pp.group.order)) fun t =>
          H pp ab ![ab 0 * rs 0, ab 1 * rs 1, t]
  let loss (pp : PublicParams G κ) : ℝ :=
    2 / (pp.group.order : ℝ) - 1 / (pp.group.order : ℝ) ^ 2
  have hPoint (pp : PublicParams G κ) : |P pp - Q pp| ≤ loss pp := ?_
  swap
  · have h := dlinDiagonal_random_gap_le (H pp)
      (fun ab u => ProbComp.prob_nonneg _ _) (fun ab u => ProbComp.prob_le_one _ _)
    simpa only [ZMod.card] using h
  have hLoss : ProbComp.expect (publicParamsGen G κ) loss = G.dlinMatrixSlack κ := ?_
  swap
  · simp only [publicParamsGen_eq, ProbComp.expect_bind, ProbComp.expect_map,
      publicParamsCore_eq, loss, ProbComp.expect_const, dlinMatrixSlack_eq, G.inst_eq]
  have hAverage := ProbComp.abs_expect_sub_le_expect (publicParamsGen G κ) hPoint
  rw [hLoss] at hAverage
  simpa only [P, Q, H, accept_eq, dlinMatrixGame_eq, dlinGame_eq, dlinMatrixSample_eq,
    dlinSample_eq, ProbComp.prob_bind, ProbComp.expect_bind, ProbComp.expect_pure,
    ProbComp.prob_pure, ProbComp.prob_eq_expect, ↓reduceIte, ProbComp.expect_const,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] using hAverage
