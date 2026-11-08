<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMKit.lean :: Complexity.LogProg.nsem_call₃_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Three-Argument Oracle Call

**Claim.** When the oracle answers true on the nested paired input formed from $x$ and the three register values, the semantics at the true-answer successor imply the same semantics at the call configuration.

**Proof.** The whole-input encoding identity for three arguments (`vword_whole₃`) identifies the call's virtual input with the stated nested pairing. The assumed true oracle answer therefore makes the deterministic call step move to $l_1$, leaving the register assignment and result unchanged. The deterministic-step semantics rule (`NSem.det`), with the given guard at the call configuration, now transfers termination and the acceptance equivalence from that successor.

**Key facts.** `Complexity.LogProg.vword_whole₃`, `Complexity.LogProg.NSem.det`.
