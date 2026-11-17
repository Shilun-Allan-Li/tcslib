<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UHaltMachine.lean :: Complexity.not_decidesInTime_UHALT -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Undecidability of Unary Halting

**Claim.** No finite-state Turing machine decides the unary language encoding whether a decoded machine halts, even when an arbitrary time bound is allowed.

**Proof.** Assume a machine decides the unary halting language within the proposed time bound. The theorem `HALT_computable_of_decidesInTime_UHALT` shows that such a decider would make the halting predicate computable: encode each halting instance as the corresponding unary input and use the decider's answer. But `HALT_not_computable` states that the halting predicate for this effective machine coding is not computable. These conclusions contradict each other, so no such decider exists.

**Key facts.** `Complexity.HALT_computable_of_decidesInTime_UHALT`, `Complexity.HALT_not_computable`.
