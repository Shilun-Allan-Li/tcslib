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
  let ch : SAChallenge C kappa := ⟨a.publicInput, a.privateInput⟩
  let stateMap : Unit → S.SAState kappa := fun _ => some ch
  let key : (Fin (C.fnLen.eval kappa) → Bool) →
      StateT Unit ProbComp (S.SK kappa pp) :=
    fun f => StateT.lift (S.keyGen kappa pp msk f)
  have hkey : ∀ (f : Fin (C.fnLen.eval kappa) → Bool) (state : Unit),
      S.realSAImpl kappa pp pk msk 1 f (stateMap state) =
        (key f state).bind fun ks =>
          .pure (S.saSKAnswer kappa pp (some ks.1), stateMap ks.2) := ?_
  swap
  · intro f state
    change S.realSAImpl kappa pp pk msk 1 f (some ch) =
      ((StateT.lift (S.keyGen kappa pp msk f) :
        StateT Unit ProbComp (S.SK kappa pp)).run state).bind fun ks =>
          .pure (S.saSKAnswer kappa pp (some ks.1), some ch)
    rw [S.realSAImpl_eq, S.saImpl_one_onSpec, S.saKeyFunction_eq,
      S.realSAKey_some, StateT.run_lift]
    simp only [OracleComp.bind_eq_bind, OracleComp.pure_eq_pure,
      OracleComp.bind_assoc, OracleComp.pure_bind]
  have hfirst : A.saNext (S := S) q kappa pp pk r [] =
      .query 0 (S.saChallengeQuery kappa a.publicInput a.privateInput) :=
    (A.saNext_nil (S := S) q kappa pp pk r).trans
      (S.saChallengeMove_eq kappa a.publicInput a.privateInput)
  have hcall : S.realSAImpl kappa pp pk msk 0
      (S.saChallengeQuery kappa a.publicInput a.privateInput) none =
      (S.enc kappa pp pk a.publicInput a.privateInput).bind fun ct =>
        .pure (S.saCTAnswer kappa pp (some ct), some ch) := ?_
  swap
  · rw [S.realSAImpl_eq, S.saImpl_zero_onSpec]
    simp only [S.saSplitChallenge_fst, S.saSplitChallenge_snd,
      S.saChallengeQuery_eq, Fin.append_left, Fin.append_right]
    rw [S.realSAChallenge_none, OracleComp.bind_assoc]
    simp only [OracleComp.pure_bind]
    rfl
  rw [A.toSA_run, buildComp_succ_of_query hfirst, simulate_query, hcall,
    OracleComp.map_eq_bind]
  simp only [OracleComp.bind_assoc, OracleComp.pure_bind, List.nil_append]
  apply congrArg (fun continuation =>
    (S.enc kappa pp pk a.publicInput a.privateInput).bind continuation)
  funext ct
  let entry : Sigma fun i => (S.saSpec kappa).dom i × (S.saSpec kappa).rng i :=
    ⟨0, S.saChallengeQuery kappa a.publicInput a.privateInput,
      S.saCTAnswer kappa pp (some ct)⟩
  have hct : S.saCTPayload kappa entry.1 entry.2.2 =
      some (S.encCT kappa pp ct) := ?_
  swap
  · change S.saCTPayload kappa 0 (S.saCTAnswer kappa pp (some ct)) =
      some (S.encCT kappa pp ct)
    rw [S.saCTPayload_zero, S.saCTAnswer_eq, Option.map_some,
      TCSlib.Cryptography.Composability.FixedLengthScheme.decAnswer_some,
      Fin.cons_zero, if_pos rfl, Fin.tail_cons]
  have hloop := simulate_saKeys_stateful (S := S) A q kappa pp pk r
    (S.realSAImpl kappa pp pk msk) stateMap key hkey entry []
    (S.encCT kappa pp ct) () hct (Nat.zero_le _)
  simp only [List.length_nil, Nat.sub_zero, List.drop_zero,
    List.filterMap_nil, List.nil_append] at hloop
  have hlift := stateT_mapM_lift
    (fun j : Fin (q.eval kappa) => S.keyGen kappa pp msk (a.functions j))
    (List.finRange (q.eval kappa)) ()
  rw [hlift] at hloop
  have hproject := congrArg
    (fun c : ProbComp (Bool × S.SAState kappa) => Prod.fst <$> c) hloop
  simpa only [OracleComp.map_eq_bind, OracleComp.bind_assoc, OracleComp.pure_bind,
    S.viewWord_eq_viewWordBits] using hproject
