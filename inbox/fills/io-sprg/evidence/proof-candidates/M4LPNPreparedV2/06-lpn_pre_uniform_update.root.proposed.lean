/-- A canonical uniform challenge gives the next chain word after the fixed seed translation.
Preprocessing glue for [JLS26, Lemma 4.2, p. 19]. The Boolean seed offset is retained.

**Proof sketch.** Read preprocessing and the chain, substitute the supplied canonical
matrix/value equations, and compare public coordinates. The selected vector is exactly
the challenged vector plus the fixed Boolean seed; all other coordinates retain their
frozen branch. Uniform translation is applied later, conditioned on this seed. -/
theorem lpn_pre_uniform_update (P : Params) (π : PrimeSchedule) (L : ℕ)
    (h : L = P.ℓ (P.kappaOf L)) (w : P.LPNAdvice π L)
    (k : Fin (P.kappaOf L)) (hk : k.val = w.hop.val)
    (M : Matrix (Fin (P.n (P.kappaOf L))) (Fin (P.ℓ (P.kappaOf L)))
      (ZMod (π (P.kappaOf L)).p))
    (v : Fin (P.n (P.kappaOf L)) → ZMod (π (P.kappaOf L)).p)
    (x : P.LPNChal π L) (hM : P.lpnMatrixAt π L h x = M)
    (hb : P.lpnValuesAt π L h x = v) :
    P.lpnPre π L w x =
      P.challengeStr (P.kappaOf L) (π (P.kappaOf L)) (w.I, w.buckets, M)
        (P.publicSeed (P.kappaOf L) (π (P.kappaOf L))
          (P.chainPublic (P.kappaOf L) (π (P.kappaOf L)) (w.I, w.buckets, M)
            w.draw (Function.update w.uniform k
              (fun i => v i + ((w.draw.1 i).toNat : ZMod (π (P.kappaOf L)).p)))
            (w.hop.val + 1)) false) w.tail := by
  classical
  rw [P.lpnPre_eq, dif_pos h, hM, hb]
  dsimp only
  congr 1
  apply congrArg (fun bs => P.publicSeed (P.kappaOf L) (π (P.kappaOf L)) bs false)
  funext q i
  by_cases hq : q = k
  · subst q
    simp only [P.chainPublic_eq, Function.update_self, hk,
      Nat.lt_succ_self, lt_self_iff_false, if_false, ite_true]
  · have hval : q.val ≠ w.hop.val := fun heq => hq (Fin.ext (heq.trans hk.symm))
    have hlt : q.val < w.hop.val + 1 ↔ q.val < w.hop.val := ?_
    swap
    · omega
    simp only [P.chainPublic_eq, Function.update_of_ne hq, if_neg hval, hlt]
