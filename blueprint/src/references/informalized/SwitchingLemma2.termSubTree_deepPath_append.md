<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/CanonicalDTree.lean :: termSubTree_deepPath_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Deepest-path length of `termSubTree` splits as free literals plus continuation

**Claim.** For `lits` with pairwise distinct variables, there is a restriction
`ρ'` such that (i) `ρ' v = ρ v` for every `v` outside
`(lits.map Literal.var).toFinset`, and (ii)
`(termSubTree lits ρ cont).deepPath.length` equals
`(lits.filter (fun l => decide (l.var ∈ ρ.freeVars))).length + (cont ρ').deepPath.length`.
So the deepest path spends exactly one query per free literal and then continues
inside `cont ρ'`. Length-level statement only.

**Proof.** `induction' lits` generalizing `ρ`, `cont`.

1. `nil`: take `ρ' := ρ`; the filter is empty and `termSubTree [] ρ cont = cont ρ`
   (`⟨ρ, fun _ => rfl, rfl⟩`).
2. `cons l lits`: `by_cases hfree : l.var ∈ ρ.freeVars`.
   - Free: `termSubTree_deepPath_head_free` gives `b` with
     `deepPath = (l.var, b) :: _`, so the length grows by one. Apply `ih` at
     `Function.update ρ l.var (some b)` (tail pairwiseness via
     `List.Pairwise.tail`) and reuse its `ρ'`; the arithmetic is
     `add_right_comm`, and `filter_free_update_eq` (with
     `hdistinct.1` supplying `x.var ≠ l.var`) identifies the two filtered
     lists. The agreement condition weakens correctly because `l.var` is in the
     variable set.
   - Not free: `termSubTree_cons_nonfree` drops `l` from the tree, the filter
     drops it too, and `ih ρ cont` finishes.

**Note.** No other declaration in `TCSlib/` currently references this lemma;
`termSubTree_deepPath_split` proves the stronger list-level version.
