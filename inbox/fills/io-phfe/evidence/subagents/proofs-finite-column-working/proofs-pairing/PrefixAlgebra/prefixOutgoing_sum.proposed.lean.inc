/-- The edges with a fixed parent are precisely the one-label extensions of
that prefix when its depth is below d; there are no such edges at maximal depth.
This is finite-prefix indexing glue for [AGW20, Appendix A, (32), p.38].

**Proof sketch.** Split the finite sigma sum by its predecessor depth. At the
matching depth, reindex tuples by Fin.snocEquiv and evaluate the supported initial
tuple sum. At maximal depth, Fin.castSucc_ne_last excludes all edges. -/
theorem prefixOutgoing_sum {I R : Type*} [Fintype I] [DecidableEq I]
    [AddCommMonoid R] (d : ℕ)
    (flow : (Σ k : Fin d, Fin (k.val + 1) → I) → R)
    (u : Σ k : Fin (d + 1), Fin k.val → I) :
    (∑ e : (Σ k : Fin d, Fin (k.val + 1) → I),
      if (⟨e.1.castSucc, Fin.init e.2⟩ :
          Σ k : Fin (d + 1), Fin k.val → I) = u then flow e else 0) =
      if h : u.1.val < d then
        ∑ a : I, flow ⟨⟨u.1.val, h⟩, Fin.snoc (α := fun _ => I) u.2 a⟩
      else 0 := sorry
