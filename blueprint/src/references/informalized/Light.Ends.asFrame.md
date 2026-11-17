<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Frames.lean :: Light.Ends.asFrame -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution from Refreshed Locals

**Claim.** If the original local-variable function agrees with the frame obtained by refreshing the specified entries of $l$, then any bounded execution with postcondition $Q$ from that refreshed state is also such an execution from the state with locals $loc$ and the same memory.

**Proof.** The hypothesis on the locals gives the equality $loc=\mathrm{frame}(\mathrm{refreshLocals}(l,loc,xs))$ ( `Light.LocalsBut.eq_frame`). Thus the state with locals $loc$ and memory $\mu$ is exactly the state used in the assumed execution. The same execution, cost bound, and postcondition therefore establish the conclusion.

**Key facts.** `Light.LocalsBut.eq_frame`.
