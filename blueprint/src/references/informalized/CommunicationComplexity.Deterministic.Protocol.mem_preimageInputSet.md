<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/DetRectangle.lean :: CommunicationComplexity.Deterministic.Protocol.mem_preimageInputSet -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership in a pulled-back input set

**Claim.** A pair $(x',y')$ belongs to the pullback of $R$ along the coordinate maps if and only if $(f_X(x'),f_Y(y'))$ belongs to $R$.

**Proof.** By definition, the pullback consists exactly of those pairs whose image under the coordinate maps belongs to $R$. Thus the two membership statements are identical.
