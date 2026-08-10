<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: processClauseLits_freeLits_pairwise_var -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The free literals of a clause have pairwise distinct variables

**Claim.** Let `t : Term n` be `Nodup` (`ht_nodup`) and assume any two literals
of `t` with the same variable are equal (`hnd`). Then
`(t.zipIdx).filter (fun p => p.1.var ∈ ρ₀.freeVars)` is `Pairwise` for the
relation `p.1.var ≠ q.1.var`.

**Proof.** Transport pairwise-distinctness from `t` to the indexed, filtered list.

1. `ht_var_pairwise`: `t` itself has pairwise distinct variables. Via
   `List.pairwise_iff_getElem`, if `t[i].var = t[j].var` with `i < j` then `hnd`
   gives `t[i] = t[j]`, contradicting `List.nodup_iff_getElem?_ne_getElem?`.
2. `hzip_var_pairwise`: the same for `t.zipIdx`, again through
   `List.pairwise_iff_getElem` — `List.getElem_zipIdx` says the first component
   at position `i` is `t[i]`, and `List.length_zipIdx` transports the bounds, so
   step 1 applies verbatim.
3. `List.Pairwise.filter` keeps the property under the free-variable filter.

(The proof also derives `hzip_pairwise`, distinctness of the *index* components
of `t.zipIdx`; it is not needed for the conclusion.)

**Used in.** `razborovEncode_go_numFree_invariant`, as the `hdistinct_pcl`
hypothesis of `processClauseLits_numFree_σ` — the counting step needs each
processed literal to fix a *different* variable.
