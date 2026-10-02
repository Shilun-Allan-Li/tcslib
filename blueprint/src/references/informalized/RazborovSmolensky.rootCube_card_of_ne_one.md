<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/LowDegreeObstruction.lean :: rootCube_card_of_ne_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The root cube has `2^n` points

**Claim.** For a finite field `K`, `ω : K` with `ω ≠ 1`, and any `n`,
`Fintype.card (rootCube ω n) = 2 ^ n`.

**Proof.** A two-step `calc`.
- Transport along the equivalence of `rootCubeEquivFinTwo` using `Fintype.card_congr`, giving
  `Fintype.card (Fin n → Fin 2)`.
- `simpa [Fintype.card_fun]` evaluates that to `2 ^ n`.

**Remark.** The `[Fintype K]` hypothesis only supplies the ambient finiteness instance; the
count itself does not depend on `|K|`, since the cube is the two-element set `{1, ω}` in
each of `n` coordinates.

**Used in.** `rootCube_function_card_of_ne_one` and the ball-size rewriting inside
`rootCube_counting_obstruction_lowDegreeSquarefree`.
