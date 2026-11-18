/-- The remaining scripted real key calls traverse the unqueried committed suffix.
Previously collected wire payloads are retained, and no challenge is queried again.

**Proof sketch.** Induct on the exact remaining call count. At zero, read the
final return. At a positive count, read the next key call, its successful answer,
and the first element of the dropped finRange. The induction hypothesis consumes
the remaining suffix, and the published mapM and filterMap laws join the payloads. -/
theorem simulate_saKeys_real {C : FnClass} {S : FEScheme.Raw C}
    (A : TwoStage) (q : PolyExpr) (kappa : ℕ) (pp : PublicParams S.G kappa)
    (pk : S.MPK kappa pp) (msk : S.MSK kappa pp) (r : List Bool)
    (e : Sigma fun i => (S.saSpec kappa).dom i × (S.saSpec kappa).rng i)
    (es : QueryLog (S.saSpec kappa))
    (ctBits : Fin (S.ctLen.eval kappa) → Bool) (ch : SAChallenge C kappa)
    (hct : S.saCTPayload kappa e.1 e.2.2 = some ctBits)
    (hlen : es.length ≤ q.eval kappa) :
    let a := A.saCommitment C q kappa r
    Prod.fst <$> simulate (S.realSAImpl kappa pp pk msk)
        (buildComp (A.saNext (S := S) q kappa pp pk r) false
          (q.eval kappa - es.length) (e :: es)) (some ch) =
      (List.mapM (fun j => S.keyGen kappa pp msk (a.functions j))
        ((List.finRange (q.eval kappa)).drop es.length)).bind fun keys =>
        .pure (A.second.distinguisherL kappa
          (S.viewWordBits a pp (S.encMPK kappa pp pk)
            ((es.filterMap fun entry => S.saSKPayload kappa entry.1 entry.2.2) ++
              keys.map (S.encSK kappa pp)) ctBits)
          (A.secondCoins kappa r)) := by
  let a := A.saCommitment C q kappa r
  let next := A.saNext (S := S) q kappa pp pk r
  let key : Fin (q.eval kappa) → ProbComp (S.SK kappa pp) :=
    fun j => S.keyGen kappa pp msk (a.functions j)
  let payload : (Sigma fun i => (S.saSpec kappa).dom i × (S.saSpec kappa).rng i) →
      Option (Fin (S.skLen.eval kappa) → Bool) :=
    fun entry => S.saSKPayload kappa entry.1 entry.2.2
  change Prod.fst <$> simulate (S.realSAImpl kappa pp pk msk)
      (buildComp next false (q.eval kappa - es.length) (e :: es)) (some ch) =
    (List.mapM key ((List.finRange (q.eval kappa)).drop es.length)).bind fun keys =>
      .pure (A.second.distinguisherL kappa
        (S.viewWordBits a pp (S.encMPK kappa pp pk)
          (es.filterMap payload ++ keys.map (S.encSK kappa pp)) ctBits)
        (A.secondCoins kappa r))
  generalize hremaining : q.eval kappa - es.length = remaining
  induction remaining generalizing es with
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
      simp only [OracleComp.map_eq_bind, OracleComp.pure_bind, hdrop,
        List.mapM_nil, OracleComp.pure_eq_pure, List.map_nil, List.append_nil]
  | succ remaining ih =>
      have hmore : es.length < q.eval kappa := Nat.lt_of_sub_eq_succ hremaining
      let j : Fin (q.eval kappa) := ⟨es.length, hmore⟩
      have hn := A.saNext_cons (S := S) q kappa pp pk r e es
      simp only [hct, dif_pos hmore] at hn
      rw [S.saKeyMove_eq] at hn
      change next (e :: es) = .query 1 (a.functions j) at hn
      have hcall : S.realSAImpl kappa pp pk msk 1 (a.functions j) (some ch) =
          (key j).bind fun sk => .pure (S.saSKAnswer kappa pp (some sk), some ch) := ?_
      swap
      · rw [S.realSAImpl_eq, S.saImpl_one_onSpec, S.saKeyFunction_eq,
          S.realSAKey_some, OracleComp.bind_assoc]
        simp only [OracleComp.pure_bind]
      have hi : es.length < (List.finRange (q.eval kappa)).length :=
        lt_of_lt_of_eq hmore List.length_finRange.symm
      have hindex : (List.finRange (q.eval kappa))[es.length]'hi = j :=
        (List.getElem_finRange hi).trans (Fin.ext rfl)
      have hdrop : (List.finRange (q.eval kappa)).drop es.length =
          j :: (List.finRange (q.eval kappa)).drop (es.length + 1) :=
        (List.drop_eq_getElem_cons hi).trans
          (congrArg (fun index : Fin (q.eval kappa) =>
            index :: (List.finRange (q.eval kappa)).drop (es.length + 1)) hindex)
      rw [buildComp_succ_of_query (next := next) hn, simulate_query, hcall,
        OracleComp.map_eq_bind, hdrop, List.mapM_cons]
      simp only [OracleComp.bind_eq_bind, OracleComp.pure_eq_pure,
        OracleComp.bind_assoc, OracleComp.pure_bind, List.cons_append]
      apply congrArg (fun continuation => (key j).bind continuation)
      funext sk
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
      have hstep := ih es' hlen' hremaining'
      rw [hsize] at hstep
      rw [← OracleComp.map_eq_bind]
      change Prod.fst <$> simulate (S.realSAImpl kappa pp pk msk)
        (buildComp next false remaining (e :: es')) (some ch) = _
      rw [hstep]
      apply congrArg (fun continuation =>
        (List.mapM key ((List.finRange (q.eval kappa)).drop (es.length + 1))).bind
          continuation)
      funext keys
      simp only [hprefix, List.map_cons, List.append_assoc,
        List.cons_append, List.nil_append]
