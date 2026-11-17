<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionValid.lean :: BoolCircuit.CktSatReduction.S_o -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output in the absorbing state

**Claim.** For every finite bit string $r$, the transducer started in state $o$ outputs exactly $r$.

**Proof.** Induct on the length of $r$. The empty string produces no output. If $r$ begins with a bit $b$, state $o$ emits $b$ and, by the transition rule, remains in state $o$. The one-bit output formula (`S_cons`) therefore gives $[b]$ followed by the output on the remaining string from $o$. By induction that remaining output is the suffix, so the result is all of $r$.

**Key facts.** `BoolCircuit.CktSatReduction.S_cons`.
