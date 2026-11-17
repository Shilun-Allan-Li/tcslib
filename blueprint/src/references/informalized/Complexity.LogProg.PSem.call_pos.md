<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMPSem.lean :: Complexity.LogProg.PSem.call_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Oracle Call

**Claim.** If a whole-input oracle call on the encoding of $x$ paired with the binary representation of register $r$ receives a positive answer, semantics at its positive successor implies the same semantics at the call state.

**Proof.** The virtual input for this whole-input call is the encoding of $x$ paired with the binary representation of $v(r)$ (`vword_whole₁`). Since the oracle answers positively, the deterministic call moves to $l_1$, preserving the registers and the absence of a result. The positive-successor semantics in the hypothesis is therefore the call's one-step successor semantics. The deterministic-step preservation result (`PSem.det`), together with the guard at the call state, yields the conclusion.

**Key facts.** `Complexity.LogProg.PSem.det`, `Complexity.LogProg.vword_whole₁`.
