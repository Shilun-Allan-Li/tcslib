<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DualHardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.dualHardSample_dualHardSample -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Involutivity of hard-sample dualization

**Claim.** Dualizing a hard sample twice returns the original hard sample.

**Proof.** Write the sample as $(T,x_T,y_T,	ext{other})$. After two dualizations, reversing the distinguished coordinate twice restores $T$, and swapping the two distinguished bits twice restores $x_T$ and $y_T$. At each other coordinate, the coordinate index is reversed twice and its assignment is swapped twice. The latter operation is an involution (`DisjointCoordinate.swap_swap`), so the assignment function is restored pointwise. All fields therefore agree with those of the original sample.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.DisjointCoordinate.swap_swap`.
