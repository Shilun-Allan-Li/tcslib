<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMKit.lean :: Complexity.LogProg.nsem_call₃_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negative Three-Argument Oracle Call

**Claim.** When the oracle answers false on the nested paired input formed from $x$ and the three register values, the semantics at the false-answer successor imply the same semantics at the call configuration.

**Proof.** The call is deterministic, and its virtual input is the stated nested pairing by the whole-input, three-argument encoding identity (`vword_whole₃`). Since the oracle answers false, the next configuration is at $l_0$ with the register values unchanged. The deterministic-step semantics rule (`NSem.det`) transfers the successor's termination and acceptance equivalence to the call configuration, using the assumed guard there.

**Key facts.** `Complexity.LogProg.vword_whole₃`, `Complexity.LogProg.NSem.det`.
