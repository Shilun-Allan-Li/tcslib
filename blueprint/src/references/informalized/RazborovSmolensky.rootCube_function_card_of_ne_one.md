<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/LowDegreeObstruction.lean :: rootCube_function_card_of_ne_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Number of functions on the root cube

**Claim.** For a finite field `K`, `ω : K` with `ω ≠ 1`, and any `n`,
`Fintype.card (rootCube ω n → K) = Fintype.card K ^ (2 ^ n)`.

**Proof.**
- Install the intended finiteness instances: `letI := rootCubeFintypeOfFintype` for the cube,
  then `change` the goal so the function-space cardinality is the `Pi.instFintype` one (this
  is exactly why that instance is defined as a `Pi`-fintype rather than via `Fintype.ofFinite`).
- `rw [Fintype.card_fun]` turns the goal into `Fintype.card K ^ Fintype.card (rootCube ω n)`.
- `rw [rootCube_card_of_ne_one hω]` replaces the exponent by `2 ^ n`.

**Used in.** `rootCube_counting_obstruction_lowDegreeSquarefree`, as the size of the family
of all target functions that the low-degree candidates must cover.
