/-- The remaining scripted key calls follow any stateful key law represented by the handler.
The joint conclusion retains the output and represented final state.

**Proof sketch.** Induct once on the exact remaining call count, generalizing the
history prefix and abstract state. At a query use its supplied one-call law and
the published StateT mapM recurrence, then recurse from the returned state. The
existing suffix and payload laws align the ordered final view. -/
theorem simulate_saKeys_stateful {C : FnClass} {S : FEScheme.Raw C}
    (A : TwoStage) (q : PolyExpr) (kappa : ℕ) (pp : PublicParams S.G kappa)
    (pk : S.MPK kappa pp) (r : List Bool) {sigma tau : Type}
    (impl : QueryImpl (S.saSpec kappa) tau unifSpec)
    (stateMap : sigma → tau)
    (key : (Fin (C.fnLen.eval kappa) → Bool) →
      StateT sigma ProbComp (S.SK kappa pp))
    (hkey : ∀ (f : Fin (C.fnLen.eval kappa) → Bool) (st : sigma),
      impl 1 f (stateMap st) =
        (key f st).bind fun ks =>
          .pure (S.saSKAnswer kappa pp (some ks.1), stateMap ks.2))
    (e : Sigma fun i => (S.saSpec kappa).dom i × (S.saSpec kappa).rng i)
    (es : QueryLog (S.saSpec kappa))
    (ctBits : Fin (S.ctLen.eval kappa) → Bool) (st : sigma)
    (hct : S.saCTPayload kappa e.1 e.2.2 = some ctBits)
    (hlen : es.length ≤ q.eval kappa) :
    let a := A.saCommitment C q kappa r
    simulate impl
        (buildComp (A.saNext (S := S) q kappa pp pk r) false
          (q.eval kappa - es.length) (e :: es)) (stateMap st) =
      ((List.mapM (m := StateT sigma ProbComp)
        (fun j => key (a.functions j))
        ((List.finRange (q.eval kappa)).drop es.length)).run st).bind fun keys =>
        .pure (A.second.distinguisherL kappa
          (S.viewWordBits a pp (S.encMPK kappa pp pk)
            ((es.filterMap fun entry => S.saSKPayload kappa entry.1 entry.2.2) ++
              keys.1.map (S.encSK kappa pp)) ctBits)
          (A.secondCoins kappa r), stateMap keys.2) := by
  let a := A.saCommitment C q kappa r
  let next := A.saNext (S := S) q kappa pp pk r
  let call : Fin (q.eval kappa) → StateT sigma ProbComp (S.SK kappa pp) :=
    fun j => key (a.functions j)
  let payload : (Sigma fun i => (S.saSpec kappa).dom i × (S.saSpec kappa).rng i) →
      Option (Fin (S.skLen.eval kappa) → Bool) :=
    fun entry => S.saSKPayload kappa entry.1 entry.2.2
  change simulate impl
      (buildComp next false (q.eval kappa - es.length) (e :: es)) (stateMap st) =
    ((List.mapM (m := StateT sigma ProbComp) call
      ((List.finRange (q.eval kappa)).drop es.length)).run st).bind fun keys =>
      .pure (A.second.distinguisherL kappa
        (S.viewWordBits a pp (S.encMPK kappa pp pk)
          (es.filterMap payload ++ keys.1.map (S.encSK kappa pp)) ctBits)
        (A.secondCoins kappa r), stateMap keys.2)
  generalize hremaining : q.eval kappa - es.length = remaining
  induction remaining generalizing es st with
  | zero =>
      have hdone : es.length = q.eval kappa :=
        Nat.le_antisymm hlen (Nat.sub_eq_zero_iff_le.mp hremaining)
      have hn := A.saNext_cons (S := S) q kappa pp pk r e es
      simp only [hct, dif_neg (not_lt_of_ge (le_of_eq hdone.symm))] at hn
      change next (e :: es) = .ret (A.second.distinguisherL kappa
        (S.viewWordBits a pp (S.encMPK kappa pp pk) (es.filterMap payload) ctBits)
        (A.secondCoins kappa r)) at hn
      have hdrop : (List.finRange (q.eval kappa)).drop es.length = [] :=
        List.drop_of_length_le
          (le_trans (le_of_eq List.length_finRange) (le_of_eq hdone.symm))
      rw [buildComp_zero_of_ret (next := next) hn, simulate_pure]
      simp only [hdrop, List.mapM_nil, StateT.run_pure,
        OracleComp.pure_eq_pure, OracleComp.pure_bind, List.map_nil, List.append_nil]
  | succ remaining ih =>
      have hmore : es.length < q.eval kappa := Nat.lt_of_sub_eq_succ hremaining
      let j : Fin (q.eval kappa) := ⟨es.length, hmore⟩
      have hn := A.saNext_cons (S := S) q kappa pp pk r e es
      simp only [hct, dif_pos hmore] at hn
      rw [S.saKeyMove_eq] at hn
      change next (e :: es) = .query 1 (a.functions j) at hn
      have hi : es.length < (List.finRange (q.eval kappa)).length :=
        lt_of_lt_of_eq hmore List.length_finRange.symm
      have hindex : (List.finRange (q.eval kappa))[es.length]'hi = j :=
        (List.getElem_finRange hi).trans (Fin.ext rfl)
      have hdrop : (List.finRange (q.eval kappa)).drop es.length =
          j :: (List.finRange (q.eval kappa)).drop (es.length + 1) :=
        (List.drop_eq_getElem_cons hi).trans
          (congrArg (fun index : Fin (q.eval kappa) =>
            index :: (List.finRange (q.eval kappa)).drop (es.length + 1)) hindex)
      rw [buildComp_succ_of_query (next := next) hn, simulate_query, hkey,
        hdrop, List.mapM_cons]
      simp only [StateT.run_bind, StateT.run_pure,
        OracleComp.bind_eq_bind, OracleComp.pure_eq_pure,
        OracleComp.bind_assoc, OracleComp.pure_bind, List.cons_append]
      apply congrArg (fun continuation => ((call j).run st).bind continuation)
      funext ks
      rcases ks with ⟨sk, st'⟩
      let entry : Sigma fun i => (S.saSpec kappa).dom i × (S.saSpec kappa).rng i :=
        ⟨1, a.functions j, S.saSKAnswer kappa pp (some sk)⟩
      let es' := es ++ [entry]
      have hsize : es'.length = es.length + 1 := List.length_append
      have hlen' : es'.length ≤ q.eval kappa :=
        le_trans (le_of_eq hsize) (Nat.succ_le_of_lt hmore)
      have hremaining' : q.eval kappa - es'.length = remaining := ?_
      swap
      · rw [hsize, Nat.sub_succ, hremaining, Nat.pred_succ]
      have hsk : payload entry = some (S.encSK kappa pp sk) := ?_
      swap
      · change S.saSKPayload kappa 1 (S.saSKAnswer kappa pp (some sk)) =
          some (S.encSK kappa pp sk)
        rw [S.saSKPayload_one, S.saSKAnswer_eq, Option.map_some,
          TCSlib.Cryptography.Composability.FixedLengthScheme.decAnswer_some,
          Fin.cons_zero, if_pos rfl, Fin.tail_cons]
      have hprefix : es'.filterMap payload =
          es.filterMap payload ++ [S.encSK kappa pp sk] := ?_
      swap
      · change (es ++ [entry]).filterMap payload =
          es.filterMap payload ++ [S.encSK kappa pp sk]
        rw [List.filterMap_append, List.filterMap_cons_some hsk, List.filterMap_nil]
      have hstep := ih (es := es') (st := st')
        (hlen := hlen') (hremaining := hremaining')
      rw [hsize] at hstep
      change simulate impl
        (buildComp next false remaining (e :: es')) (stateMap st') = _
      rw [hstep]
      apply congrArg (fun continuation =>
        ((List.mapM (m := StateT sigma ProbComp) call
          ((List.finRange (q.eval kappa)).drop (es.length + 1))).run st').bind
            continuation)
      funext keys
      simp only [hprefix, List.map_cons, List.append_assoc,
        List.cons_append, List.nil_append]
