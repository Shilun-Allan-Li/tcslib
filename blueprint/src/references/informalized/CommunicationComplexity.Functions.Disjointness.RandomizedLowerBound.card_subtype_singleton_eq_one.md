<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.card_subtype_singleton_eq_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cardinality of a Singleton Subtype

**Claim.** For any type $\alpha$ and element $a\in\alpha$, the subtype consisting of elements belonging to $\{a\}$ has cardinality $1$.

**Proof.** The element $a$ together with the proof $a\in\{a\}$ gives a point of this subtype. Every point has underlying element equal to $a$, since membership in the singleton forces that equality; hence every point of the subtype equals the one just exhibited. A finite type with exactly one element has cardinality $1$.
