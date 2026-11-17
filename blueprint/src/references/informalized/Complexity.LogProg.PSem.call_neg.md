<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMPSem.lean :: Complexity.LogProg.PSem.call_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negative Oracle Call

**Claim.** If a whole-input oracle call on the encoding of $x$ paired with the binary representation of register $r$ receives a negative answer, semantics at its negative successor implies the same semantics at the call state.

**Proof.** A deterministic instruction preserves semantics from its successor back to the current configuration, provided the guard holds there (`PSem.det`). The virtual input for a whole-input call with the single register $r$ is exactly the encoding of $x$ paired with the binary word of $v(r)$ (`vword_whole₁`). By the assumed negative oracle answer, the call therefore steps to $l_0$ without changing the registers or result. The successor semantics in the hypothesis is thus the required one-step semantics, and the deterministic-step result applies.

**Key facts.** `Complexity.LogProg.PSem.det`, `Complexity.LogProg.vword_whole₁`.
