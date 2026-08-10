<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: Term.width -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Width of a term

**Definition.** A term on `n` variables is literally a list of literals
(`abbrev Term (n : ℕ) := List (Literal n)`), and
`Term.width (t : Term n) : ℕ` is defined to be `t.length` — the number of
literals occurring in `t`.

No deduplication or consistency requirement is imposed: a term containing both
`xᵢ` and `¬xᵢ`, or the same literal twice, has width equal to its raw list
length, not the number of distinct variables it mentions.

**Remark.** This is a one-line wrapper around `List.length` and exists only so
that the widths of DNF and CNF formulas can be phrased uniformly: both
`DNF.width` and `CNF.width` are `(·.map Term.width).foldr max 0`.

**Used in.** `DNF.width` and `CNF.width`, and through them the width hypotheses
of the switching-lemma development (`TCSlib/BooleanAnalysis/Switching.lean`) and
the LMN layer-compression files (`LMN/CircuitCompression.lean`,
`LMN/CircuitHelpers.lean`), where the fold is traded for a pointwise bound
`∀ t ∈ ts, t.width ≤ l`.
