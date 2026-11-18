/-- The edges with a fixed parent are precisely the one-label extensions of
that prefix when its depth is below d; there are no such edges at maximal depth.
This is finite-prefix indexing glue for [AGW20, Appendix A, (32), p.38].

**Proof sketch.** Use the published sigma-product distribution and snoc tuple
equivalence to reindex edges as predecessor prefixes and final labels. The
castSucc prefix embedding is injective, so the supported prefix sum selects the
queried nonterminal prefix. At maximal depth no embedded prefix can match. -/
theorem prefixOutgoing_sum {I R : Type*} [Fintype I] [DecidableEq I]
    [AddCommMonoid R] (d : ℕ)
    (flow : (Σ k : Fin d, Fin (k.val + 1) → I) → R)
    (u : Σ k : Fin (d + 1), Fin k.val → I) :
    (∑ e : (Σ k : Fin d, Fin (k.val + 1) → I),
      if (⟨e.1.castSucc, Fin.init e.2⟩ :
          Σ k : Fin (d + 1), Fin k.val → I) = u then flow e else 0) =
      if h : u.1.val < d then
        ∑ a : I, flow ⟨⟨u.1.val, h⟩, Fin.snoc (α := fun _ => I) u.2 a⟩
      else 0 := by
  let edgeEquiv : ((Σ k : Fin d, Fin k.val → I) × I) ≃
      (Σ k : Fin d, Fin (k.val + 1) → I) :=
    (Equiv.sigmaProdDistrib (fun k : Fin d => Fin k.val → I) I).trans
      (Equiv.sigmaCongrRight (fun k : Fin d =>
        (Equiv.prodComm (Fin k.val → I) I).trans
          (Fin.snocEquiv (fun _ : Fin (k.val + 1) => I))))
  let prefixEmbed : (Σ k : Fin d, Fin k.val → I) →
      (Σ k : Fin (d + 1), Fin k.val → I) :=
    Sigma.map Fin.castSucc (fun _ tau => tau)
  have hinj : Function.Injective prefixEmbed :=
    (Fin.castSucc_injective d).sigma_map (fun _ => Function.injective_id)
  -- Reindex all edges by their initial tuple and final label.
  rw [← edgeEquiv.sum_comp (fun e =>
    if (⟨e.1.castSucc, Fin.init e.2⟩ :
        Σ k : Fin (d + 1), Fin k.val → I) = u then flow e else 0),
    Fintype.sum_prod_type_right]
  change (∑ a : I, ∑ q : (Σ k : Fin d, Fin k.val → I),
    if (⟨q.1.castSucc, Fin.init (Fin.snoc (α := fun _ => I) q.2 a)⟩ :
        Σ k : Fin (d + 1), Fin k.val → I) = u then
      flow ⟨q.1, Fin.snoc (α := fun _ => I) q.2 a⟩ else 0) = _
  simp only [Fin.init_snoc]
  change (∑ a : I, ∑ q : (Σ k : Fin d, Fin k.val → I),
    if prefixEmbed q = u then
      flow ⟨q.1, Fin.snoc (α := fun _ => I) q.2 a⟩ else 0) = _
  rcases u with ⟨k, tau⟩
  cases k using Fin.lastCases with
  | last =>
    -- A castSucc depth cannot be the terminal depth.
    have hmax : ∀ q, prefixEmbed q ≠
        (⟨Fin.last d, tau⟩ : Σ k : Fin (d + 1), Fin k.val → I) :=
      fun q h => Fin.castSucc_ne_last q.1
        (show q.1.castSucc = Fin.last d from congrArg Sigma.fst h)
    rw [dif_neg (show ¬ (Fin.last d).val < d from Nat.lt_irrefl d)]
    simp only [hmax, if_false, Finset.sum_const_zero]
  | cast k =>
    -- At the queried prefix, injectivity collapses the inner supported sum.
    let q0 : (Σ k : Fin d, Fin k.val → I) := ⟨k, tau⟩
    rw [dif_pos (show
      (⟨k.castSucc, tau⟩ : Σ k : Fin (d + 1), Fin k.val → I).1.val < d from k.isLt)]
    change (∑ a : I, ∑ q : (Σ k : Fin d, Fin k.val → I),
      if prefixEmbed q = prefixEmbed q0 then
        flow ⟨q.1, Fin.snoc (α := fun _ => I) q.2 a⟩ else 0) =
      ∑ a : I, flow ⟨q0.1, Fin.snoc (α := fun _ => I) q0.2 a⟩
    simp only [hinj.eq_iff, Fintype.sum_ite_eq']
