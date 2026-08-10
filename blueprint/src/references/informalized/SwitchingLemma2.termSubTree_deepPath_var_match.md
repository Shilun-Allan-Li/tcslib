<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/CanonicalDTree.lean :: termSubTree_deepPath_var_match -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The deepest path queries the free literals in order

**Claim.** Let `lits` have pairwise distinct variables. For every `k` that is in
range both for `lits.filter (l.var ∈ ρ.freeVars)` and for
`(termSubTree lits ρ cont).deepPath`, the `k`-th variable queried on the deepest
path equals the variable of the `k`-th free literal:
`((termSubTree lits ρ cont).deepPath[k]).1 =
(lits.filter (fun l => decide (l.var ∈ ρ.freeVars))[k]).var`.

**Proof.** `induction' lits` generalizing `ρ`, `cont`, `k`, simplifying with
`List.filter_cons`.

1. `nil`: the filtered list is empty, so `hk : k < 0` is a `contradiction`.
2. `cons l rest`: `by_cases hfree : l.var ∈ ρ.freeVars`.
   - Free: `termSubTree_deepPath_head_free` gives `b` with
     `deepPath = (l.var, b) :: _`, and the filtered list is `l :: _`.
     `rcases k`:
     * `k = 0`: both sides are `l.var`.
     * `k+1`: `convert ih (Function.update ρ l.var (some b)) cont _ k _`. The
       index hypotheses go through by `linarith`; the two filtered lists agree
       because `filter_free_update_eq` (and, for the residual goal,
       `List.filter_congr` plus `hdistinct.1`) shows updating `l.var` does not
       change freeness of the other, distinct variables. Tail pairwiseness comes
       from `List.pairwise_cons`.
   - Not free: `termSubTree_cons_nonfree` rewrites the tree to the tail's, the
     filter drops `l`, and `ih` applies directly.

One remark: distinctness is what keeps the index alignment stable — without it,
updating one variable could change another literal's freeness.
