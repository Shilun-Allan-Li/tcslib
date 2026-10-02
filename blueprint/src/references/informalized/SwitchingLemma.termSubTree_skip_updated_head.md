<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/CanonicalDTree.lean :: termSubTree_skip_updated_head -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# `termSubTree` skips a head literal that was just assigned

**Claim.** If `l.var = v`, then
`termSubTree (l :: rest_lits) (Function.update ρ v (some b)) cont =
termSubTree rest_lits (Function.update ρ v (some b)) cont`. Once `v` has been
given the value `b`, it is no longer free, so `termSubTree` does not branch on
the head literal again. `private`.

**Proof.**

1. `apply termSubTree_cons_nonfree`, reducing to
   `l.var ∉ (Function.update ρ v (some b)).freeVars`.
2. `rw [← hv_eq]` replaces `l.var` by `v`, and unfolding
   `Restriction.freeVars` (`Finset.mem_filter`, `Option.isNone_iff_eq_none`)
   together with `Function.update_apply` leaves the goal
   `¬(some b = none)`, closed by `simp`.

**Note.** No other declaration in `TCSlib/` currently references this lemma,
despite the docstring billing it as "Auxiliary (ii)".
