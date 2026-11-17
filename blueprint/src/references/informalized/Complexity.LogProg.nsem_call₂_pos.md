<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMKit.lean :: Complexity.LogProg.nsem_call₂_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Two-Argument Oracle Call

**Claim.** When the oracle answers true on the paired input formed from $x$ and the two register values, the semantics at the true-answer successor imply the same semantics at the call configuration.

**Proof.** The deterministic call instruction takes one step to its true-answer successor because the oracle value on the virtual input is true. By the virtual-word identity for a whole-input call with two arguments (`vword_whole₂`), that input is precisely the stated nested pairing. Hence the successor configuration is the one at $l_1$, with registers and result unchanged. Apply the deterministic-step semantics rule (`NSem.det`) together with the guard at the call configuration to obtain the same terminating semantics and acceptance equivalence at the call.

**Key facts.** `Complexity.LogProg.vword_whole₂`, `Complexity.LogProg.NSem.det`.
