<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitCompression.lean :: cnf_concat_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Concatenating CNFs computes their conjunction

**Claim.** For a list of CNFs `cnfs : List (CNF n)` and an input `x`,

`CNF.eval (listConcat cnfs) x = cnfs.all (fun ψ => CNF.eval ψ x)`

where `listConcat` flattens a list of clause lists into one clause list.

**Proof.** Induction on `cnfs` (`induction cnfs with`).

- `nil`: `simp [listConcat, CNF.eval]` — the empty clause list evaluates to
  `true` by `List.all`, as does `List.all` of the empty list.
- `cons`: `simp only [listConcat, List.all_append, CNF.eval]` splits the
  `List.all` over the append `head ++ listConcat tail`; `simp_all [CNF.eval]`
  then closes it with the inductive hypothesis.

**Remark.** This is the whole reason CNF concatenation is the right merge
operation: a CNF is a conjunction of clauses, so appending clause lists
conjoins the formulas — which is what lets an AND gate one layer above absorb
its CNF children.

**Used in.** `compression_and_of_cnfs` (same file), paired with
`cnf_concat_width_le` for the width side.
