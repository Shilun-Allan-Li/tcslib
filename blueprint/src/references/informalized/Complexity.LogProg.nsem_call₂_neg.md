<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMKit.lean :: Complexity.LogProg.nsem_call₂_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negative Two-Argument Oracle Call

**Claim.** When the oracle answers false on the paired input formed from $x$ and the two register values, the semantics at the false-answer successor imply the same semantics at the call configuration.

**Proof.** The deterministic call instruction takes one step to its false-answer successor because the oracle value on the virtual input is false. The virtual-word identity for a whole-input call with two arguments (`vword_whole₂`) identifies that input with the stated nested pairing of $x$ and the two register words. Thus the one-step successor configuration is exactly the configuration at $l_0$ with the same registers and result field. The deterministic-step semantics rule (`NSem.det`), using the assumed guard at the call configuration, transfers termination and the acceptance equivalence from that successor to the call configuration.

**Key facts.** `Complexity.LogProg.vword_whole₂`, `Complexity.LogProg.NSem.det`.
