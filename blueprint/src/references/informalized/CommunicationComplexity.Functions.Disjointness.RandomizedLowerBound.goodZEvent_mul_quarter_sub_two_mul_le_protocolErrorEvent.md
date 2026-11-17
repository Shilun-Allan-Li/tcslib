<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/Headline.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.goodZEvent_mul_quarter_sub_two_mul_le_protocolErrorEvent -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Good-Sample Mass Versus Error-Event Mass

**Claim.** For every real $\gamma$, the measure of the good-sample event multiplied by $\frac14-2\gamma$ is at most the measure of the protocol error event.

**Proof.** Decompose the error-event measure by the fibers of the finite-valued observation $Z$. The finite conditional-fiber decomposition expresses it as a sum over observations $z$ of the mass of the fiber at $z$ times the conditional error mass within that fiber (\texttt{FiniteMeasureSpace.measureReal\_eq\_sum\_cond\_fiber\_real}). Separately, the measure of the good-sample event is the sum of the masses of precisely those fibers whose observation satisfies the good condition (\texttt{FiniteMeasureSpace.measureReal\_preimage\_eq\_sum\_fibers}). Distribute the factor $\frac14-2\gamma$ over this finite sum and compare terms. For a good observation, the conditional error mass is at least $\frac14-2\gamma$ by the fiberwise error bound (\texttt{quarter\_sub\_two\_mul\_le\_zFiberMeasure\_protocolErrorEvent}); multiplying by the nonnegative fiber mass preserves the inequality. For an observation that is not good, the good-event contribution is zero, while the corresponding error contribution is nonnegative. Summing these termwise comparisons proves the result.

**Key facts.** `CommunicationComplexity.FiniteMeasureSpace.measureReal_eq_sum_cond_fiber_real`, `CommunicationComplexity.FiniteMeasureSpace.measureReal_preimage_eq_sum_fibers`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.quarter_sub_two_mul_le_zFiberMeasure_protocolErrorEvent`.

**Caveat.** The informal statement supplied for this index describes a different information-theoretic claim. This account follows the formal statement and proof source, which concern the good-sample event and the protocol error event.
