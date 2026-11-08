<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/Headline.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.quarter_sub_two_mul_le_zFiberMeasure_protocolErrorEvent -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Error on a Statistic Fiber

**Claim.** For a good statistic value $z$, the conditional probability of protocol error on its fiber is at least $1/4-2\gamma$.

**Proof.** Let $b$ be the protocol’s output on the inputs determined by the statistic value $z$. The conditional special-bit pair has mass at least $1/4-2\gamma$ at the diagonal pair $(b,b)$, by the singleton lower bound for a good conditional law (\texttt{quarter_sub_two_mul_le_conditionalSpecialPairLaw_singleton}). On the fiber where the statistic equals $z$, every sample with special pair $(b,b)$ is an error (\texttt{zFiber_inter_diag_specialPair_subset_protocolErrorEvent}): the shared transcript forces the same output, while the pair $(b,b)$ has the opposite disjointness value. Therefore this pair event is contained in the error event, and monotonicity of measure bounds the error mass below by its mass. The pair-event mass under the fiber measure is identified with the singleton mass under the conditional pair law (\texttt{conditionalSpecialPairLaw_singleton}); restricting to the fiber itself does not change that measure (\texttt{zFiberMeasure_inter_fiber}). This gives the claimed lower bound.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.quarter_sub_two_mul_le_conditionalSpecialPairLaw_singleton`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.zFiber_inter_diag_specialPair_subset_protocolErrorEvent`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.zFiberMeasure_inter_fiber`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.conditionalSpecialPairLaw_singleton`.
