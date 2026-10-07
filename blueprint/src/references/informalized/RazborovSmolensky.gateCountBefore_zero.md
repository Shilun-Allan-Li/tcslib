<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/CircuitDegree.lean :: gateCountBefore_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The gate count of the input layer is zero

**Claim.** For `F : FeedForward (Fin 2) (Fin n) out` with finite layers and any
`hd : 0 ≤ F.depth`, `gateCountBefore F 0 hd = 0`. Equivalently: layer `0` is the
input layer and contributes no gates to the count, whatever the depth of `F` and
whatever proof `hd` is supplied (the statement is uniform in `hd` by proof
irrelevance).

**Proof.** Immediate from `simp [gateCountBefore]` — this is the base case of
the defining recursion.

**Remark.** A granular helper, tagged `@[simp]` so that the zero error term at
the input layer is discharged automatically; it is what forces the bad-seed bound
in `inputLayerFamily` to be "the bad set is empty" rather than merely small,
since the right-hand side there is `gateCountBefore F 0 hd * Fintype.card Seed = 0`.
