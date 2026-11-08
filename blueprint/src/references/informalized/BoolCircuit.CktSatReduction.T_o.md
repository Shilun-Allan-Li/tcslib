<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionValid.lean :: BoolCircuit.CktSatReduction.T_o -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Identity in the Output State

**Claim.** For every finite bit string $r$, processing $r$ from state $o$ returns $r$ unchanged.

**Proof.** Induct on the string. The empty string produces no output. For a string beginning with a bit $b$, the transducer's next state from $o$ is again $o$, and its output on $b$ is $b$. The induction hypothesis says the remaining suffix is also copied, so the whole string is unchanged (`T_cons`).

**Key facts.** `BoolCircuit.CktSatReduction.T_cons`.
