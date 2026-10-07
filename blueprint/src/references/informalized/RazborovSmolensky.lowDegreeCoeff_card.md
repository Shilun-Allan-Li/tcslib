<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/LowDegreeObstruction.lean :: lowDegreeCoeff_card -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Counting the coefficient families of a degree-`≤ D` squarefree polynomial

**Claim.** For a finite type `K₀`,

`Fintype.card (LowDegreeSupport n D → K₀) = Fintype.card K₀ ^ Fintype.card (LowDegreeSupport n D)`.

**Proof.** Immediate from `Fintype.card_fun` after `classical`; the proof is a single
`simpa using (Fintype.card_fun : …)` whose only job is to make the statement fire against
the file's `noncomputable` `lowDegreeSupportFintype` instance.

**Remark.** A deliberately granular wrapper: it exists so that later counting steps can
rewrite with a lemma whose `Fintype` instances already match the ones in scope, rather than
re-deriving them. Combined with `lowDegreeSupport_card_le_binomial_sum` it bounds the number
of degree-`≤ D` squarefree candidates by `|K₀| ^ (∑ t ≤ D, n.choose t)`.
