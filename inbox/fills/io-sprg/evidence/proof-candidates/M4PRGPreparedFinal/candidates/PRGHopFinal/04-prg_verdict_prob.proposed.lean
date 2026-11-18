/-- A shared-contract PRG realiser has the advised reduction's exact verdict probability;
reduction glue for [JLS26, Lemma 4.2, p. 19]. Only encoded challenges and layout-length
coins are used. The unused suffix is removed by the existing uniform restriction law.

**Proof sketch.** Reindex the realiser's coins through coinsEquivPoly, read its verdict,
read prgRed, and apply pushesUniform_restrict along the prefix injection together with
the existing ofFn_castLE_eq_take representation equation. -/
theorem Params.prg_verdict_prob (P : Params) (π : PrimeSchedule) (A : NUPPT)
    (ω : ∀ N, P.PRGAdvice π N) (B : NUPPT)
    (hB : B.RealizesOn P.prgEnc (A.coins.subst .var)
      (fun N x r => P.prgRed π A N (ω N) x r)) (N : ℕ) (x : P.PRGChal N) :
    ProbComp.prob (ProbComp.sample (B.Coins N))
        (fun r => B.distinguisherL N (P.prgEnc N x) r = true) =
      ProbComp.prob (ProbComp.sample (A.Coins (P.kappaOfN N)))
        (fun r => A.distinguisherL (P.kappaOfN N)
          (P.prgPre π N (ω N) x) r = true) := by
  classical
  have hcut : A.coinLen (P.kappaOfN N) ≤ (A.coins.subst .var).eval N := ?_
  swap
  · rw [A.coinLen_eq, PolyExpr.eval_subst, PolyExpr.eval_var]
    exact A.coins.eval_mono (P.kappaOfN_le N)
  let Q : List Bool → Prop := fun r =>
    A.runAtL (P.kappaOfN N) (P.prgPre π N (ω N) x) r = [true]
  rw [Bridge.prob_sample_eq_uprob
      (fun r : B.Coins N => B.distinguisherL N (P.prgEnc N x) r = true),
    Bridge.prob_sample_eq_uprob
      (fun r : A.Coins (P.kappaOfN N) =>
        A.distinguisherL (P.kappaOfN N) (P.prgPre π N (ω N) x) r = true)]
  trans uprob (fun r : Fin ((A.coins.subst .var).eval N) → Bool =>
    Q ((List.ofFn r).take (A.coinLen (P.kappaOfN N))))
  · calc
      uprob (fun r : B.Coins N => B.distinguisherL N (P.prgEnc N x) r = true) =
          uprob (fun r : Fin ((A.coins.subst .var).eval N) → Bool =>
            B.distinguisherL N (P.prgEnc N x)
              ((NUPPT.coinsEquivPoly hB.coins_eq N).symm r) = true) :=
        (uprob_comp_equiv (NUPPT.coinsEquivPoly hB.coins_eq N).symm
          (fun r : B.Coins N => B.distinguisherL N (P.prgEnc N x) r = true)).symm
      _ = _ := ?_
    congr 1
    funext r
    rw [hB.distinguisherL_eq, P.prgRed_eq, NUPPT.coinsEquivPoly_symm_ofFn]
    simp only [decide_eq_true_eq, Q]
  · have hp :=
      (HardcoreBit.pushesUniform_restrict (O := Bool) (Fin.castLE_injective hcut)).uprob_eq
        (fun r : Fin (A.coinLen (P.kappaOfN N)) → Bool => Q (List.ofFn r))
    simp only [OneWay.ofFn_castLE_eq_take hcut] at hp
    simpa only [Q, NUPPT.distinguisherL_eq, NUPPT.runAt_eq, decide_eq_true_eq] using hp
