<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/CanonicalDTree.lean :: termSubTree_skip_nonfree_prefix' -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# `termSubTree` ignores a wholly non-free prefix

**Claim.** If every literal of `prefix_lits` has its variable already fixed by
`ρ` (`l.var ∉ Restriction.freeVars ρ`), then
`termSubTree (prefix_lits ++ rest) ρ cont = termSubTree rest ρ cont`. `private`;
a granular bookkeeping helper.

**Proof.** Induction on `prefix_lits`.

1. `nil`: `[] ++ rest = rest`, closed by `simp`.
2. `cons l rest'`: `rw [List.cons_append]`, then
   `termSubTree_cons_nonfree l _ ρ cont (hnonfree l List.mem_cons_self)` strips
   the head (its variable is not free, so `termSubTree` takes the skip branch),
   and `ih` applies with the hypothesis weakened along
   `List.mem_cons_of_mem`.

**Note.** No other declaration in `TCSlib/` currently references this lemma.
