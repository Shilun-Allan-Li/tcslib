<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/CanonicalDTree.lean :: termSubTree_deepPath_split -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Deepest path of `termSubTree` is a prefix followed by the continuation's path

**Claim.** For `lits` with pairwise distinct variables there exist a list
`prefix_dp` and a restriction `ρ'` with
`(termSubTree lits ρ cont).deepPath = prefix_dp ++ (cont ρ').deepPath`,
`prefix_dp.length = (lits.filter (fun l => decide (l.var ∈ ρ.freeVars))).length`,
and `ρ' v = ρ v` for every `v` outside `(lits.map Literal.var).toFinset`. This is
the list-level form of `termSubTree_deepPath_append`, which records only lengths.

**Proof.** `induction' lits` generalizing `ρ`, `cont`.

1. `nil`: take `prefix_dp := []`, `ρ' := ρ` — `⟨[], ρ, rfl, rfl, fun _ _ => rfl⟩`.
2. `cons l lits`: `by_cases hfree : l.var ∈ ρ.freeVars`.
   - Free: `termSubTree_deepPath_head_free` gives `b` with
     `deepPath = (l.var, b) :: _`. Apply `ih` at
     `Function.update ρ l.var (some b)` (tail pairwiseness via
     `List.pairwise_cons`) and take `(l.var, b) :: prefix_dp` with the same `ρ'`.
     The prefix-length goal matches after `filter_free_update_eq`, whose
     side condition `x.var ≠ l.var` is `hdistinct.1`.
   - Not free: `termSubTree_cons_nonfree` rewrites the tree to the tail's and
     `ih ρ cont` transfers all three components unchanged.

**Note.** Currently unreferenced elsewhere in `TCSlib/`; the analogous splitting
step for `canonicalDTree` is done inline in
`TCSlib/BooleanAnalysis/Switching.lean` (`hdp_drop`).
