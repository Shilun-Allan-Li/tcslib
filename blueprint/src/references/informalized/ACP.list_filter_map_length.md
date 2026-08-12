<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/CircuitDegree.lean :: list_filter_map_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Filtering a mapped list counts the pulled-back predicate

**Claim.** For a list `l : List α`, a map `f : α → β` and a decidable predicate
`P` on `β`, `((l.map f).filter P).length = (l.filter (fun a => P (f a))).length`.

**Proof.** `induction l`:

- `nil` — both sides are `0`, by `simp`.
- `cons a l ih` — `by_cases h : P (f a) <;> simp [h, ih]`. In either case `simp`
  peels one `List.map`/`List.filter` step off both sides and closes the goal with
  the induction hypothesis; when `P (f a)` holds both lengths gain `1`, otherwise
  both are unchanged.

**Remark.** A granular list-bookkeeping helper (no circuit content). It is used in
`exists_poly_list_for_circuit_one` to move from a filter on a list of
*polynomials* `map P s` to a filter on the underlying list of *seeds*, which is
where the counting bound lives. Note that lengths — not `toFinset` cardinalities
— are compared, so multiplicities are preserved even when `P` maps several seeds
to the same polynomial.
