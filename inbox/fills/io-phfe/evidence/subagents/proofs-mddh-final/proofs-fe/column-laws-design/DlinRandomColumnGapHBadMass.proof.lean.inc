by
    let c : ℝ := 1 / (Fintype.card K : ℝ)
    let diagGood (ab : Fin 2 → K) : Prop := ab 0 ≠ 0 ∧ ab 1 ≠ 0
    -- Reuse the public independent-coordinate law with an explicit scalar predicate.
    have hDiagMass :
        ProbComp.expect (ProbComp.sample (Fin 2 → K))
            (fun ab => if diagGood ab then (1 : ℝ) else 0) = (1 - c) ^ 2 := ?_
    swap
    · have hEvent :
          ProbComp.prob (ProbComp.sample (Fin 2 → K)) diagGood =
            ProbComp.prob (ProbComp.sample (Fin 2 → K))
              (fun ab : Fin 2 → K => ∀ i : Fin 2, ab i ≠ 0) :=
        ProbComp.prob_congr (ProbComp.sample (Fin 2 → K))
          (p := diagGood) (q := fun ab : Fin 2 → K => ∀ i : Fin 2, ab i ≠ 0)
          (fun ab => (Fin.forall_fin_two (p := fun i : Fin 2 => ab i ≠ 0)).symm)
      rw [← ProbComp.prob_eq_expect (ProbComp.sample (Fin 2 → K)) diagGood, hEvent,
        Bridge.prob_sample_eq_uprob (fun ab : Fin 2 → K => ∀ i : Fin 2, ab i ≠ 0),
        TCSlib.Cryptography.OneWay.uprob_pi_forall (ι := Fin 2) (fun x : K => x ≠ 0),
        TCSlib.Cryptography.uprob_not (fun x : K => x = 0),
        TCSlib.Cryptography.OneWay.uprob_eq_one_div_card (0 : K), Fintype.card_fin]
    -- At every coefficient pair, the uniform t misses its sum with probability 1-c.
    have hMiss (rs : Fin 2 → K) :
        ProbComp.expect (ProbComp.sample K)
            (fun t : K => if t ≠ rs 0 + rs 1 then (1 : ℝ) else 0) = 1 - c := ?_
    swap
    · rw [← ProbComp.prob_eq_expect (ProbComp.sample K)
          (fun t : K => t ≠ rs 0 + rs 1),
        ProbComp.prob_not (ProbComp.sample K) (fun t : K => t = rs 0 + rs 1),
        Bridge.prob_sample_eq_uprob (fun t : K => t = rs 0 + rs 1),
        TCSlib.Cryptography.OneWay.uprob_eq_one_div_card (rs 0 + rs 1)]
    have hGoodMass (ab rs : Fin 2 → K) :
        ProbComp.expect (ProbComp.sample K)
            (fun t : K => if ¬ bad ab rs t then (1 : ℝ) else 0) =
          (1 - c) * (if diagGood ab then (1 : ℝ) else 0) := ?_
    swap
    · have hFactor :
          (fun t : K => if ¬ bad ab rs t then (1 : ℝ) else 0) =
            (fun t : K => (if diagGood ab then (1 : ℝ) else 0) *
              (if t ≠ rs 0 + rs 1 then (1 : ℝ) else 0)) := ?_
      swap
      · funext t
        simp only [bad, diagGood, not_or, ← and_assoc, ite_and, ite_mul, one_mul, zero_mul]
      rw [hFactor, ProbComp.expect_const_mul, hMiss rs]
      exact mul_comm _ _
    -- Complement the actual bad predicate; no additional event is counted.
    have hInnerBad (ab rs : Fin 2 → K) :
        ProbComp.expect (ProbComp.sample K)
            (fun t : K => if bad ab rs t then (1 : ℝ) else 0) =
          1 - (1 - c) * (if diagGood ab then (1 : ℝ) else 0) := ?_
    swap
    · have hComp := ProbComp.prob_not (ProbComp.sample K) (bad ab rs)
      rw [ProbComp.prob_eq_expect (ProbComp.sample K) (fun t : K => ¬ bad ab rs t),
        hGoodMass ab rs, ProbComp.prob_eq_expect (ProbComp.sample K) (bad ab rs)] at hComp
      apply eq_sub_iff_add_eq.mpr
      exact (add_comm _ _).trans (eq_sub_iff_add_eq.mp hComp)
    simp only [hInnerBad, ProbComp.expect_const]
    rw [ProbComp.expect_sub (ProbComp.sample (Fin 2 → K)) (fun _ => 1)
        (fun ab => (1 - c) * (if diagGood ab then (1 : ℝ) else 0)),
      ProbComp.expect_const (ProbComp.sample (Fin 2 → K)) 1,
      ProbComp.expect_const_mul (ProbComp.sample (Fin 2 → K)) (1 - c)
        (fun ab => if diagGood ab then (1 : ℝ) else 0), hDiagMass]
    exact congrArg (fun z : ℝ => 1 - z) (pow_succ' (1 - c) 2).symm
