<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/CircuitDegree.lean :: piEquivAt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Splitting off one coordinate of a dependent function

**Definition.** For `ι` with decidable equality, a family `β : ι → Type*` and an
index `i : ι`, `piEquivAt i` is the equivalence

`((j : ι) → β j) ≃ β i × ((j : {j : ι // j ≠ i}) → β j.1)`.

Forward it sends `f` to `(f i, fun j => f j.1)`; backward it glues a value at `i`
and a function on the complement, deciding `j = i` with `dif` and transporting by
`subst` in the equal case.

**Remark.** The two round-trip obligations are discharged by `by_cases h : j = i`
followed by `simp` (`left_inv`) and by `ext j` with `simp [j.2]` (`right_inv`).
The definition is `noncomputable` only because of the `subst`-based transport; it
is a plain reindexing with no arithmetic content.

**Used in.** `pi_coordinate_bad_mul_le`, where it turns a dependent product of
seed spaces into "the seed at node `i`" times "all other seeds", so that a bound
at one coordinate can be multiplied by the number of remaining configurations.
