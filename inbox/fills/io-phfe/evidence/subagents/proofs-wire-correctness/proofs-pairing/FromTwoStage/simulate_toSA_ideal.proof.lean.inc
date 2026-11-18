/-- For any fixed composite tape and initial simulator state, the scripted ideal
oracle run threads that state through encryption and all committed keys, using
exactly their allowed values. It ends with the second machine's activation on the
same public view. This is the ideal typed protocol in [GJLS21, Definition 4.3].

**Proof sketch.** Unroll the accepted challenge and ordered keys with a history
invariant that retains the current simulator state and the answered-key prefix.
Apply the stateful handler readers and existing mapM laws. Project away the state
only after the last key, and read the final canonical public view. -/
theorem simulate_toSA_ideal {C : FnClass} {S : FEScheme.Raw C}
    (Sim : FEScheme.Raw.SASimulator.Raw S) (A : TwoStage) (q : PolyExpr)
    (kappa : ℕ) (pp : PublicParams S.G kappa) (pk : S.MPK kappa pp)
    (st : Sim.St kappa pp) (r : List Bool) :
    Prod.fst <$> simulate (S.idealSAImpl Sim kappa pp)
        ((A.toSA (S := S) q).run kappa pp pk r) (st, none) =
      let a := A.saCommitment C q kappa r
      (Sim.enc kappa pp st a.publicInput).bind fun cst =>
      (List.mapM (m := StateT (Sim.St kappa pp) ProbComp)
        (fun j st' => Sim.key kappa pp st' a.publicInput (a.functions j)
          (C.eval kappa (S.cprm kappa pp) (a.functions j)
            a.publicInput a.privateInput))
        (List.finRange (q.eval kappa)) cst.2).bind fun keys =>
        .pure (A.second.distinguisherL kappa (S.viewWord a pp pk keys.1 cst.1)
          (A.secondCoins kappa r)) := by
  let a := A.saCommitment C q kappa r
  let ch : SAChallenge C kappa := ⟨a.publicInput, a.privateInput⟩
  let stateMap : Sim.St kappa pp → S.SAIdealState Sim kappa pp :=
    fun state => (state, some ch)
  let key : (Fin (C.fnLen.eval kappa) → Bool) →
      StateT (Sim.St kappa pp) ProbComp (S.SK kappa pp) :=
    fun f state => Sim.key kappa pp state a.publicInput f
      (C.eval kappa (S.cprm kappa pp) f a.publicInput a.privateInput)
  have hkey : ∀ (f : Fin (C.fnLen.eval kappa) → Bool) (state : Sim.St kappa pp),
      S.idealSAImpl Sim kappa pp 1 f (stateMap state) =
        (key f state).bind fun ks =>
          .pure (S.saSKAnswer kappa pp (some ks.1), stateMap ks.2) := ?_
  swap
  · intro f state
    change S.idealSAImpl Sim kappa pp 1 f (state, some ch) =
      (Sim.key kappa pp state a.publicInput f
        (C.eval kappa (S.cprm kappa pp) f a.publicInput a.privateInput)).bind fun ks =>
          .pure (S.saSKAnswer kappa pp (some ks.1), (ks.2, some ch))
    rw [S.idealSAImpl_eq, S.saImpl_one_onSpec, S.saKeyFunction_eq,
      S.idealSAKey_some, OracleComp.bind_assoc]
    simp only [OracleComp.pure_bind]
    rfl
  have hfirst : A.saNext (S := S) q kappa pp pk r [] =
      .query 0 (S.saChallengeQuery kappa a.publicInput a.privateInput) :=
    (A.saNext_nil (S := S) q kappa pp pk r).trans
      (S.saChallengeMove_eq kappa a.publicInput a.privateInput)
  have hcall : S.idealSAImpl Sim kappa pp 0
      (S.saChallengeQuery kappa a.publicInput a.privateInput) (st, none) =
      (Sim.enc kappa pp st a.publicInput).bind fun cst =>
        .pure (S.saCTAnswer kappa pp (some cst.1), (cst.2, some ch)) := ?_
  swap
  · rw [S.idealSAImpl_eq, S.saImpl_zero_onSpec]
    simp only [S.saSplitChallenge_fst, S.saSplitChallenge_snd,
      S.saChallengeQuery_eq, Fin.append_left, Fin.append_right]
    rw [S.idealSAChallenge_none, OracleComp.bind_assoc]
    simp only [OracleComp.pure_bind]
    rfl
  rw [A.toSA_run, buildComp_succ_of_query hfirst, simulate_query, hcall,
    OracleComp.map_eq_bind]
  simp only [OracleComp.bind_assoc, OracleComp.pure_bind, List.nil_append]
  apply congrArg (fun continuation =>
    (Sim.enc kappa pp st a.publicInput).bind continuation)
  funext cst
  rcases cst with ⟨ct, st'⟩
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
    (S.idealSAImpl Sim kappa pp) stateMap key hkey entry []
    (S.encCT kappa pp ct) st' hct (Nat.zero_le _)
  simp only [List.length_nil, Nat.sub_zero, List.drop_zero,
    List.filterMap_nil, List.nil_append] at hloop
  have hproject := congrArg
    (fun c : ProbComp (Bool × S.SAIdealState Sim kappa pp) => Prod.fst <$> c) hloop
  simpa only [OracleComp.map_eq_bind, OracleComp.bind_assoc, OracleComp.pure_bind,
    S.viewWord_eq_viewWordBits] using hproject
