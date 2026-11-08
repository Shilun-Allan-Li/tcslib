<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/FiniteMessage.lean :: CommunicationComplexity.Deterministic.FiniteMessage.Protocol.comap_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution under pullback

**Claim.** For any protocol and maps into its input types, running the pulled-back protocol on the original inputs gives the same output as running the original protocol on the mapped inputs.

**Proof.** Proceed by structural induction on the protocol. For an output node, both executions return its fixed output. At an Alice node, the pulled-back query sends $f(f_X(x'))$, exactly the message sent by the original query on $f_X(x')$; the induction hypothesis applied to the selected continuation then gives equality of outputs. At a Bob node the same reasoning uses $f_Y(y')$: both executions select the same continuation, to which the induction hypothesis applies.
