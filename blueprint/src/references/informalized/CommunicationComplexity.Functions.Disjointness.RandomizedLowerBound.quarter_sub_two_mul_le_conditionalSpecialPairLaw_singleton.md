<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/Headline.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.quarter_sub_two_mul_le_conditionalSpecialPairLaw_singleton -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mass of a Pair Under a Good Law

**Claim.** For a good statistic value, every special-bit pair has conditional probability at least $1/4-2\gamma$.

**Proof.** Goodness bounds the total variation distance between the conditional pair law and the uniform law by $2\gamma$. The resulting singleton estimate says that the absolute difference between the conditional mass of any pair and its uniform mass $1/4$ is at most $2\gamma$ (\texttt{abs_conditionalSpecialPairLaw_singleton_sub_quarter_le}). In particular, the conditional mass is no smaller than $1/4-2\gamma$, as required.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.abs_conditionalSpecialPairLaw_singleton_sub_quarter_le`.
