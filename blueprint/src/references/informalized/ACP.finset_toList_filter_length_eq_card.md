<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/CircuitDegree.lean :: finset_toList_filter_length_eq_card -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# `Finset.toList` preserves filtered cardinalities

**Claim.** For a finset `s : Finset α` and a decidable predicate `q` on `α`,
`(s.toList.filter q).length = (s.filter q).card`.

**Proof.** After `classical`:

1. `htf : (s.toList.filter q).toFinset = s.filter q`, by `ext a; simp` — an
   element is in the filtered list iff it is in `s` and satisfies `q`.
2. A two-step `calc`. First `(s.toList.filter q).length = ((s.toList.filter q).toFinset).card`
   by `List.toFinset_card_of_nodup`, whose nodup hypothesis is
   `(Finset.nodup_toList s).filter q` — `s.toList` has no duplicates and
   filtering cannot create any, so no element is double-counted.
3. Then `rw [htf]` turns that cardinality into `(s.filter q).card`.

**Remark.** A granular bridging helper between the list and finset counting
worlds. Used in `exists_poly_list_for_circuit_one` (composed with
`list_filter_map_length`) to convert the `Finset.filter`-based bad-seed bound of
`exists_poly_distribution_for_circuit_one` into a statement about the length of a
filtered list.
