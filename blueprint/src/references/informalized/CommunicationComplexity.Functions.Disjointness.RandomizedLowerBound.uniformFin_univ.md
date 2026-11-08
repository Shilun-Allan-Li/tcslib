<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformFin_univ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total mass of a finite uniform law

**Claim.** The uniform law on $	ext{Fin }n$ assigns mass one to the entire space.

**Proof.** Apply `uniformFin_real` to the whole space. Its subtype of elements has cardinality $n$, equal to the cardinality of $	ext{Fin }n$. The measure is thus $n/n=1$.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformFin_real`.
