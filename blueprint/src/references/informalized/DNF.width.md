<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: DNF.width -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Width of a DNF formula

**Definition.** For `d : DNF n` — where `DNF n` is the abbreviation `List (Term n)` and
`Term n` is `List (Literal n)` — the width `DNF.width d` is the largest term width
occurring in `d`, computed as `(d.map Term.width).foldr max 0`. Since `Term.width` is just
`List.length`, this is the maximum number of literals in any term of the disjunction, and
it is `0` for the empty formula (as well as for a formula all of whose terms are empty).

**Remark.** The `foldr max 0` form, rather than a `Finset.sup` or `List.maximum`, is what
downstream width lemmas rewrite against. `CNF.width` is defined by the identical expression
on `CNF n` (also an abbreviation for `List (Term n)`), so the two are the same function up
to the abbreviation.

**Used in.** The switching-lemma development, wherever a DNF is required to have bounded
width.
