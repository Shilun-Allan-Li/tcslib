/-- For any fixed composite tape, public key and master key, the scripted real
oracle run is encryption followed by the committed keys in order and the second
machine's activation on their public view. This is the typed protocol form of
[GJLS21, Definition 4.3].

**Proof sketch.** Unroll the accepted challenge and then the bounded committed-key
queries through the published builder and handler readers. Retain the challenge
entry and the answered-key prefix in the history invariant. The ordered key law
is List.mapM; its final wire view is the published typed view. -/
theorem simulate_toSA_real {C : FnClass} {S : FEScheme.Raw C}
    (A : TwoStage) (q : PolyExpr) (kappa : ℕ) (pp : PublicParams S.G kappa)
    (pk : S.MPK kappa pp) (msk : S.MSK kappa pp) (r : List Bool) :
    Prod.fst <$> simulate (S.realSAImpl kappa pp pk msk)
        ((A.toSA (S := S) q).run kappa pp pk r) none =
      let a := A.saCommitment C q kappa r
      (S.enc kappa pp pk a.publicInput a.privateInput).bind fun ct =>
      (List.mapM (fun j => S.keyGen kappa pp msk (a.functions j))
        (List.finRange (q.eval kappa))).bind fun keys =>
        .pure (A.second.distinguisherL kappa (S.viewWord a pp pk keys ct)
          (A.secondCoins kappa r)) := by
  let a := A.saCommitment C q kappa r
  have hfirst : A.saNext (S := S) q kappa pp pk r [] =
      .query 0 (S.saChallengeQuery kappa a.publicInput a.privateInput) :=
    (A.saNext_nil (S := S) q kappa pp pk r).trans
      (S.saChallengeMove_eq kappa a.publicInput a.privateInput)
  have hcall : S.realSAImpl kappa pp pk msk 0
      (S.saChallengeQuery kappa a.publicInput a.privateInput) none =
      (S.enc kappa pp pk a.publicInput a.privateInput).bind fun ct =>
        .pure (S.saCTAnswer kappa pp (some ct),
          some (⟨a.publicInput, a.privateInput⟩ : SAChallenge C kappa)) := ?_
  swap
  · rw [S.realSAImpl_eq, S.saImpl_zero_onSpec]
    simp only [S.saSplitChallenge_fst, S.saSplitChallenge_snd,
      S.saChallengeQuery_eq, Fin.append_left, Fin.append_right]
    rw [S.realSAChallenge_none, OracleComp.bind_assoc]
    simp only [OracleComp.pure_bind]
  rw [A.toSA_run, buildComp_succ_of_query hfirst, simulate_query, hcall,
    OracleComp.map_eq_bind]
  simp only [OracleComp.bind_assoc, OracleComp.pure_bind, List.nil_append]
  apply congrArg (fun continuation =>
    (S.enc kappa pp pk a.publicInput a.privateInput).bind continuation)
  funext ct
  rw [S.viewWord_eq_viewWordBits]
  -- Remaining goal: simulate_saKeys_real with empty key history and the
  -- successful ciphertext payload, after its required native helper probes.
  sorry
