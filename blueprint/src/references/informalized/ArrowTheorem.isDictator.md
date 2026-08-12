<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ArrowTheorem.lean :: isDictator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Being a dictatorship

**Definition.** For `f : BooleanFunc n`,

`isDictator f ↔ ∃ i : Fin n, f = dictator i`,

where `dictator i = fun x => boolToSign (x i)` (from `BooleanAnalysis.Basic`).
So some single voter `i` exists whose ballot alone is society's verdict, at every
input.

**Remark.** Two things to note about the strength of this phrasing.

- It asserts equality of *functions*, not agreement on some subfamily of
  profiles; the consumer proof discharges it with `use j₀; ext x`.
- It asks for `f = dictator i` exactly, with no sign option. The textbook
  degree-1 classification only gives "a dictator **or** a negated dictator"
  (`f = ±dictator i`); the negated branch is ruled out here by unanimity, so
  this stronger form is available.

A plain `Prop`-valued definition; no proof.

**Used in.** The conclusion of `degree_one_implies_dictator` and hence of
`arrow_theorem`. Nothing else in the repository refers to it.
