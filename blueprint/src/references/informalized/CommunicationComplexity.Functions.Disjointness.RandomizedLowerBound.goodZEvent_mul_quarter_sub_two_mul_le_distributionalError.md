<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/Headline.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.goodZEvent_mul_quarter_sub_two_mul_le_distributionalError -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Good-Sample Mass Bound

**Claim.** The measure of the good-sample event multiplied by $\frac14-2\gamma$ is at most the protocol's distributional error under the input distribution induced by the hard distribution.

**Proof.** First identify the distributional error under the induced input distribution with the measure of the protocol error event (\texttt{distributionalError\_inputDist\_eq\_protocolErrorEvent}). The claimed inequality then follows directly from the bound relating the good-sample mass to the measure of that error event (\texttt{goodZEvent\_mul\_quarter\_sub\_two\_mul\_le\_protocolErrorEvent}).

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.distributionalError_inputDist_eq_protocolErrorEvent`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.goodZEvent_mul_quarter_sub_two_mul_le_protocolErrorEvent`.
