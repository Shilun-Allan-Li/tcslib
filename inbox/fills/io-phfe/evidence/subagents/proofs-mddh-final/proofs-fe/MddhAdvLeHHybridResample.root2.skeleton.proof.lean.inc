by
    intro κ j real
    -- Isolate just the actual-game/conditional-matrix read from uniform resampling.
    have hHybridRead : accept (hybrid κ (j.val + (if real then 1 else 0))) =
        ProbComp.expect (publicParamsGen G κ) (fun pp =>
          ProbComp.expect
            (ProbComp.sample (Matrix (Fin (ℓ.eval κ)) (Fin 2) (ZMod pp.group.order)))
            (fun M => ProbComp.expect (ProbComp.sample (SType κ pp)) (fun S =>
              ProbComp.expect (ProbComp.sample (UType κ pp)) (fun U =>
                obs κ j pp S U M (if real then Matrix.mulVec M (fun a => S a j)
                  else fun a => U a j))))) := sorry
    rw [hHybridRead]
    apply congrArg (ProbComp.expect (publicParamsGen G κ)); funext pp
    let K : Type := ZMod pp.group.order
    let cols (m : ℕ) : Matrix (Fin m) (Fin (d.eval κ)) K ≃
        (Fin (d.eval κ) → Fin m → K) :=
      Equiv.piComm (fun (_ : Fin m) (_ : Fin (d.eval κ)) => K)
    -- The observer cannot see either mask's selected column.
    have hIgnore (S S' : SType κ pp) (U U' : UType κ pp)
        (M : Matrix (Fin (ℓ.eval κ)) (Fin 2) K) (v : Fin (ℓ.eval κ) → K)
        (hS : ∀ a b, b.val ≠ j.val → S a b = S' a b)
        (hU : ∀ a b, b.val ≠ j.val → U a b = U' a b) :
        obs κ j pp S U M v = obs κ j pp S' U' M v := ?_
    swap
    · dsimp only [obs]
      apply congrArg (fun R : Matrix (Fin (ℓ.eval κ)) (Fin (d.eval κ)) K =>
        ProbComp.prob (ProbComp.sample (D.Coins κ)) (fun r =>
          D.distinguisherL κ (G.mddhEnc d ℓ κ
            ⟨pp, pp.group.expMat pp.generator M, pp.group.expMat pp.generator R⟩) r = true))
      funext a b
      split_ifs with hSel hPrior
      · rfl
      · rw [Matrix.mul_apply, Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hS i b hSel]
      · exact hU a b hSel
    have hRealColumn (M : Matrix (Fin (ℓ.eval κ)) (Fin 2) K) (U : UType κ pp) :
        ProbComp.expect (ProbComp.sample (SType κ pp))
            (fun S => obs κ j pp S U M (Matrix.mulVec M (fun a => S a j))) =
          ProbComp.expect (ProbComp.sample (SType κ pp)) (fun S =>
            ProbComp.expect (ProbComp.sample (Fin 2 → K))
              (fun rs => obs κ j pp S U M (Matrix.mulVec M rs))) := ?_
    swap
    · let F (rs : Fin 2 → K) (T : Fin (d.eval κ) → Fin 2 → K) : ℝ :=
        obs κ j pp ((cols 2).symm T) U M (Matrix.mulVec M rs)
      have hF : ∀ r r' T, F r (Function.update T j r') = F r T :=
        fun r r' T => hIgnore _ _ U U M (Matrix.mulVec M r)
          (fun a b hb => show Function.update T j r' b a = T b a from
            congrFun (Function.update_of_ne ((Fin.ne_iff_vne b j).mpr hb) r' T) a)
          (fun _ _ _ => rfl)
      have h := ProbComp.expect_sample_coord j F hF
      rw [ProbComp.expect_sample_comm F] at h
      exact (ProbComp.expect_sample_equiv (cols 2).symm
        (fun S : SType κ pp => obs κ j pp S U M
          (Matrix.mulVec M (fun a => S a j)))).symm.trans
        (h.trans (ProbComp.expect_sample_equiv (cols 2).symm
          (fun S : SType κ pp => ProbComp.expect (ProbComp.sample (Fin 2 → K))
            (fun rs => obs κ j pp S U M (Matrix.mulVec M rs)))))
    have hRandomColumn (M : Matrix (Fin (ℓ.eval κ)) (Fin 2) K) (S : SType κ pp) :
        ProbComp.expect (ProbComp.sample (UType κ pp))
            (fun U => obs κ j pp S U M (fun a => U a j)) =
          ProbComp.expect (ProbComp.sample (UType κ pp)) (fun U =>
            ProbComp.expect (ProbComp.sample (Fin (ℓ.eval κ) → K))
              (fun v => obs κ j pp S U M v)) := ?_
    swap
    · let F (v : Fin (ℓ.eval κ) → K)
          (T : Fin (d.eval κ) → Fin (ℓ.eval κ) → K) : ℝ :=
        obs κ j pp S ((cols (ℓ.eval κ)).symm T) M v
      have hF : ∀ r r' T, F r (Function.update T j r') = F r T :=
        fun r r' T => hIgnore S S _ _ M r (fun _ _ _ => rfl)
          (fun a b hb => show Function.update T j r' b a = T b a from
            congrFun (Function.update_of_ne ((Fin.ne_iff_vne b j).mpr hb) r' T) a)
      have h := ProbComp.expect_sample_coord j F hF
      rw [ProbComp.expect_sample_comm F] at h
      exact (ProbComp.expect_sample_equiv (cols (ℓ.eval κ)).symm
        (fun U : UType κ pp => obs κ j pp S U M (fun a => U a j))).symm.trans
        (h.trans (ProbComp.expect_sample_equiv (cols (ℓ.eval κ)).symm
          (fun U : UType κ pp =>
            ProbComp.expect (ProbComp.sample (Fin (ℓ.eval κ) → K))
              (fun v => obs κ j pp S U M v))))
    have hResample (M : Matrix (Fin (ℓ.eval κ)) (Fin 2) K) :
        ProbComp.expect (ProbComp.sample (SType κ pp)) (fun S =>
          ProbComp.expect (ProbComp.sample (UType κ pp)) (fun U =>
            obs κ j pp S U M (if real then Matrix.mulVec M (fun a => S a j)
              else fun a => U a j))) =
          ProbComp.expect (ProbComp.sample (SType κ pp)) (fun S =>
            ProbComp.expect (ProbComp.sample (UType κ pp)) (fun U =>
              if real then ProbComp.expect (ProbComp.sample (Fin 2 → K))
                (fun rs => obs κ j pp S U M (Matrix.mulVec M rs))
              else ProbComp.expect (ProbComp.sample (Fin (ℓ.eval κ) → K))
                (fun v => obs κ j pp S U M v))) := ?_
    swap
    · cases real with
      | false =>
        simp only [Bool.false_eq_true, if_false]
        apply congrArg (ProbComp.expect (ProbComp.sample (SType κ pp))); funext S
        exact hRandomColumn M S
      | true =>
        simp only [↓reduceIte]
        rw [ProbComp.expect_sample_comm]
        conv_rhs => rw [ProbComp.expect_sample_comm]
        apply congrArg (ProbComp.expect (ProbComp.sample (UType κ pp))); funext U
        exact hRealColumn M U
    simp_rw [hResample]
    dsimp only [ideal, idealCore]
    rw [ProbComp.expect_sample_comm]
    apply congrArg (ProbComp.expect (ProbComp.sample (SType κ pp))); funext S
    rw [ProbComp.expect_sample_comm]
