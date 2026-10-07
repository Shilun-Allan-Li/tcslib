<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: zipIdx_filter_getElem_fst -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Filtering commutes with indexing, entrywise

**Claim.** For a term `t : Term n`, a predicate `p : Literal n → Bool`, an index
`k`, and bounds `hk1 : k < (t.zipIdx.filter (fun x => p x.1)).length` and
`hk2 : k < (t.filter p).length`, the literal component of the `k`-th surviving
indexed entry equals the `k`-th surviving literal:
`((t.zipIdx.filter (fun x => p x.1))[k]).1 = (t.filter p)[k]`.

**Proof.** Entrywise companion to `zipIdx_filter_length`.

1. A `have h_zipIdx` establishes the list-level statement
   `(t.zipIdx.filter (fun x => p x.1)).map (fun x => x.1) = t.filter p`, proved
   by `induction' t using List.reverseRecOn` — `rfl` in the base case, `grind`
   for the `t ++ [a]` step.
2. `grind` then reads off the `k`-th entry from that equality of lists (via
   `List.getElem_map`), yielding the goal.

**Used in.** `canonicalDTree_deepPath_match_freeLits` and
`canonicalPath_preserve_processClauseLits` (both private, same file), to convert
"the `k`-th free literal of the clause, with its position" into "the `k`-th free
literal", which is the form the `termSubTree` descent lemmas expect.
