by
    classical
    let c : ℝ := 1 / (Fintype.card K : ℝ)
    have hN : (Fintype.card K : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    have hZero :
        ProbComp.expect (ProbComp.sample K) (fun a => if a = 0 then (1 : ℝ) else 0) = c :=
      (ProbComp.prob_eq_expect (ProbComp.sample K) (fun a : K => a = 0)).symm.trans
        ((Bridge.prob_sample_eq_uprob (fun a : K => a = 0)).trans
          (TCSlib.Cryptography.OneWay.uprob_eq_one_div_card (0 : K)))
    have hInner (a : K) :
        ProbComp.expect (ProbComp.sample K)
            (fun b => if a = 0 ∨ b = 0 then (1 : ℝ) else 0) =
          c + (1 - c) * (if a = 0 then (1 : ℝ) else 0) := ?_
    swap
    · by_cases ha : a = 0
      · have hF : (fun b : K => if a = 0 ∨ b = 0 then (1 : ℝ) else 0) =
            (fun _ => 1) := funext (fun b => if_pos (Or.inl ha))
        rw [hF, ProbComp.expect_const, if_pos ha]
        ring
      · simpa only [ha, false_or, ite_false, mul_zero, add_zero] using hZero
    dsimp only [bad]
    rw [← ProbComp.expect_sample_equiv (finTwoArrowEquiv K).symm
      (fun ab : Fin 2 → K => if ab 0 = 0 ∨ ab 1 = 0 then (1 : ℝ) else 0),
      ← Bridge.expect_sample_pair]
    simp only [ProbComp.expect_bind, ProbComp.expect_pure, finTwoArrowEquiv_symm_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    simp only [hInner]
    rw [ProbComp.expect_add, ProbComp.expect_const, ProbComp.expect_const_mul, hZero]
    dsimp only [c]
    field_simp [hN] <;> ring
