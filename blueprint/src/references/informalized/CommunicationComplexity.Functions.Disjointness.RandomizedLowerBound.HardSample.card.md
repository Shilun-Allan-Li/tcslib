<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.HardSample.card -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hard-sample cardinality

**Claim.** The hard-distribution sample space has cardinality $n\cdot4\cdot3^n$.

**Proof.** A hard sample is in bijection with a tuple consisting of a distinguished coordinate in $\mathrm{Fin}(n)$, two Boolean bits, and a function from the $n$ coordinates to the three disjoint-coordinate states. The tuple space has $n$ choices for the distinguished coordinate and $2\cdot2=4$ choices for the two bits. By the cardinality formula for functions between finite types, the function component has $3^n$ choices, using that the disjoint-coordinate type has cardinality three (\texttt{CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.DisjointCoordinate.card}). Multiplying these independent counts gives $n\cdot4\cdot3^n$.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.DisjointCoordinate.card`.
