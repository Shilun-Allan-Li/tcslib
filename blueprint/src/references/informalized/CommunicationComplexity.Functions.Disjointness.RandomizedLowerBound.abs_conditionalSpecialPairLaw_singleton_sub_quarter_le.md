<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/Headline.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.abs_conditionalSpecialPairLaw_singleton_sub_quarter_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Singleton probability bound

**Claim.** If the conditional special-coordinate pair law is within $2\gamma$ in total variation of the uniform law on bit pairs, then each singleton probability differs from $1/4$ by at most $2\gamma$.

**Proof.** Fix a bit pair $b$. The total-variation bound on measurable sets, applied to the singleton $\{b\}$, bounds the absolute difference between its probabilities under the conditional law and the uniform law by their total-variation distance (`TVDistance.abs_measureReal_sub_le_tvDistance`). Under the uniform law on the four bit pairs, the singleton has probability $1/4$ (`uniformBoolPair_singleton`). Finally, goodness says that the total-variation distance is at most $2\gamma$, giving the claimed bound.

**Key facts.** `CommunicationComplexity.TVDistance.abs_measureReal_sub_le_tvDistance`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformBoolPair_singleton`.
