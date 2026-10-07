<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: zipIdx_filter_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Filtering an indexed term does not change how many literals survive

**Claim.** For a term `t : Term n` (a list of literals) and a predicate
`p : Literal n → Bool`,
`(t.zipIdx.filter (fun x => p x.1)).length = (t.filter p).length`. Attaching
positions with `List.zipIdx` and then filtering on the literal component keeps
exactly as many entries as filtering the bare term.

**Proof.** Immediate by reverse induction on `t`
(`induction' t using List.reverseRecOn`): the base case is `rfl`, and the
`t ++ [a]` step is closed by `grind`, which unfolds `List.zipIdx`/`List.filter`
on the appended element (the appended entry survives in one list exactly when it
survives in the other).

**Used in.** `canonicalDTree_deepPath_match_freeLits` and
`canonicalPath_preserve_processClauseLits` (both private, same file), where the
free-literal list is defined via `t.zipIdx` but the canonical decision tree's
descent is stated in terms of `t.filter`, so the two lengths must be identified.
