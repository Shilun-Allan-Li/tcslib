<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitCompression.lean :: listConcat -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Flattening a list of lists

**Definition.** `listConcat : List (List α) → List α` sends the empty list to
`[]` and `l :: ls` to `l ++ listConcat ls` — i.e. the concatenation of all the
inner lists, in order.

Since `CNF n` and `DNF n` are both abbreviations for `List (Term n)`,
`listConcat` applied to a `List (CNF n)` is exactly the CNF whose clause list is
all clauses of all the input CNFs; dually for DNFs. That is how Step 6 of the LMN
argument merges two adjacent layers of the same gate type into one:

- `listConcat` of CNFs computes the conjunction of all of them
  (`cnf_concat_eval`) with width the max of their widths
  (`cnf_concat_width_le`);
- `listConcat` of DNFs computes their disjunction (`dnf_concat_eval`,
  `dnf_concat_width_le`).

The docstring records it as a version-compatibility shim — a hand-rolled stand-in
for `List.flatten`/`List.join`, whose name has moved between Lean/Mathlib
releases. Being a plain structural recursion, it is definitionally transparent,
so the downstream proofs unfold it with `simp [listConcat]`.

**Used in.** `cnf_concat_width_le`, `cnf_concat_eval`, `dnf_concat_width_le`,
`dnf_concat_eval`, and the two compression theorems
`compression_and_of_cnfs` / `compression_or_of_dnfs`.
