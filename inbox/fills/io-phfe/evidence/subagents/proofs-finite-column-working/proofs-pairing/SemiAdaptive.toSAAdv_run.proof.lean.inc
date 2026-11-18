/-- The typed run is exactly toCompOn with bitCodec, followed by reading its one bit.

**Proof sketch.** Read toCompOn_eq and runAt_eq. Induct on the remaining budget;
both computations use the same encoded history. Query branches append the same
entry; return and timeout branches differ only by reading the final bit. -/
theorem toSAAdv_run {C : FnClass} {S : FEScheme.Raw C}
    (A : NUPPT) (q : PolyExpr) (kappa : ℕ) (pp : PublicParams S.G kappa)
    (pk : S.MPK kappa pp) (r : A.Coins kappa) :
    (toSAAdv (S := S) A q).run kappa pp pk (List.ofFn r) =
      (fun b => b 0) <$> A.toCompOn
        (bitCodec (S.saIn kappa) (S.saOut kappa) 1)
        kappa (q.eval kappa) (S.saInputWord kappa pp pk) r := by
  rw [FEScheme.Raw.SAAdv.run_eq, toSAAdv_budget, NUPPT.toCompOn_eq,
    ← S.saCodec_eq kappa]
  let typedNext : QueryLog (S.saSpec kappa) → Move (S.saSpec kappa) Bool :=
    (toSAAdv (S := S) A q).next kappa pp pk (List.ofFn r)
  let wordNext : QueryLog (S.saSpec kappa) → Move (S.saSpec kappa) (Fin 1 → Bool) :=
    fun hist => (S.saCodec kappa).decodeMove
      (A.runAt kappa (pairEncode (S.saInputWord kappa pp pk)
        ((S.saCodec kappa).encodeLog hist)) r)
  change buildComp typedNext false (q.eval kappa) [] =
    (fun b : Fin 1 → Bool => b 0) <$>
      buildComp wordNext (S.saCodec kappa).timeout (q.eval kappa) []
  generalize hbudget : q.eval kappa = budget
  generalize hhist : ([] : QueryLog (S.saSpec kappa)) = hist
  clear hbudget hhist
  induction budget generalizing hist with
  | zero =>
      have hread := toSAAdv_next (S := S) A q kappa pp pk (List.ofFn r) hist
      rw [FEScheme.Raw.saReadMove_eq, ← NUPPT.runAt_eq] at hread
      change typedNext hist = (match wordNext hist with
        | .ret b => .ret (b 0)
        | .query i x => .query i x) at hread
      cases hm : wordNext hist with
      | ret b =>
          simp only [hm] at hread
          rw [buildComp_zero_of_ret (next := typedNext) hread,
            buildComp_zero_of_ret (next := wordNext) hm,
            OracleComp.map_eq_bind, OracleComp.pure_bind]
      | query i x =>
          simp only [hm] at hread
          rw [buildComp_zero_of_query (next := typedNext) hread,
            buildComp_zero_of_query (next := wordNext) hm,
            OracleComp.map_eq_bind, OracleComp.pure_bind,
            S.saCodec_eq kappa, bitCodec_timeout, zeroBits_apply]
  | succ budget ih =>
      have hread := toSAAdv_next (S := S) A q kappa pp pk (List.ofFn r) hist
      rw [FEScheme.Raw.saReadMove_eq, ← NUPPT.runAt_eq] at hread
      change typedNext hist = (match wordNext hist with
        | .ret b => .ret (b 0)
        | .query i x => .query i x) at hread
      cases hm : wordNext hist with
      | ret b =>
          simp only [hm] at hread
          rw [buildComp_succ_of_ret (next := typedNext) hread,
            buildComp_succ_of_ret (next := wordNext) hm,
            OracleComp.map_eq_bind, OracleComp.pure_bind]
      | query i x =>
          simp only [hm] at hread
          rw [buildComp_succ_of_query (next := typedNext) hread,
            buildComp_succ_of_query (next := wordNext) hm,
            OracleComp.map_eq_bind, OracleComp.query_bind]
          apply congrArg (OracleComp.query (spec := S.saSpec kappa) i x)
          funext answer
          simpa only [OracleComp.map_eq_bind] using
            ih (hist ++ [⟨i, x, answer⟩])
