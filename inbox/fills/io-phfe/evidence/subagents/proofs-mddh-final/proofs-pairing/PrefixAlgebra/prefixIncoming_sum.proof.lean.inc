/-- Every nonempty prefix has exactly one incoming prefix edge, and the empty
prefix has none. Summing values at the child endpoints therefore gives the node
value off the root and zero at the root. This is finite-prefix indexing glue for
the path-sum specialization of [AGW20, Appendix A, (28)–(32), pp.37–38].

**Proof sketch.** The child map is the published dependent sigma map induced by
Fin.succ and identity tuple maps, hence is injective. At depth zero its image is
excluded by Fin.succ_ne_zero. At positive depth use the corresponding predecessor
edge and the published supported-sum formula. -/
theorem prefixIncoming_sum {I R : Type*} [Fintype I] [DecidableEq I]
    [AddCommMonoid R] (d : ℕ)
    (value : (Σ k : Fin (d + 1), Fin k.val → I) → R)
    (u : Σ k : Fin (d + 1), Fin k.val → I) :
    (∑ e : (Σ k : Fin d, Fin (k.val + 1) → I),
      if (⟨e.1.succ, e.2⟩ : Σ k : Fin (d + 1), Fin k.val → I) = u then
        value ⟨e.1.succ, e.2⟩ else 0) =
      if u = (⟨⟨0, Nat.zero_lt_succ d⟩, Fin.elim0⟩ :
          Σ k : Fin (d + 1), Fin k.val → I) then 0 else value u := by
  let child : (Σ k : Fin d, Fin (k.val + 1) → I) →
      (Σ k : Fin (d + 1), Fin k.val → I) :=
    Sigma.map Fin.succ (fun _ tau => tau)
  let emptyPrefix : (Σ k : Fin (d + 1), Fin k.val → I) :=
    ⟨⟨0, Nat.zero_lt_succ d⟩, Fin.elim0⟩
  -- Reuse injectivity of dependent sigma maps and the successor-depth exclusion.
  have hchild : Function.Injective child :=
    (Fin.succ_injective d).sigma_map (fun _ => Function.injective_id)
  have hroot : ∀ e, child e ≠ emptyPrefix :=
    fun e h => Fin.succ_ne_zero e.1
      (show e.1.succ = 0 from congrArg Sigma.fst h)
  change (∑ e, if child e = u then value (child e) else 0) =
    if u = emptyPrefix then 0 else value u
  rcases u with ⟨k, tau⟩
  cases k using Fin.cases with
  | zero =>
    have htuple : tau = Fin.elim0 :=
      @Subsingleton.elim (Fin 0 → I) inferInstance tau Fin.elim0
    subst tau
    change (∑ e, if child e = emptyPrefix then value (child e) else 0) =
      if emptyPrefix = emptyPrefix then 0 else value emptyPrefix
    simp only [hroot, eq_self, if_true, if_false, Finset.sum_const_zero]
  | succ k =>
    -- The predecessor depth and the same tuple supply the unique incoming edge.
    let e0 : (Σ k : Fin d, Fin (k.val + 1) → I) := ⟨k, tau⟩
    change (∑ e, if child e = child e0 then value (child e) else 0) =
      if child e0 = emptyPrefix then 0 else value (child e0)
    simp only [hchild.eq_iff, Fintype.sum_ite_eq', hroot, if_false]
