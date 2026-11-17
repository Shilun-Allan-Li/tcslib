<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassOracle/Classes.lean :: Complexity.negOut_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Output Complementation

**Claim.** One step of the machine whose ordinary transitions complement their output bits, starting from a configuration whose existing output bits are complemented, equals the result of one original-machine step followed by complementing every output bit.

**Proof.** If the configuration is already halted, both machines leave it unchanged, so the equality follows directly. Otherwise write its state as $q$. If $q$ is the oracle-query state, both machines make the same oracle query and choose the same successor state; the configuration’s only modified component is its output, which remains complemented. If $q$ is not the query state, both machines consult the same transition using the same input symbol and work-tape symbols, since complementing the output does not affect them. The modified transition complements the emitted output bit. Thus its output is the old complemented output followed by the complemented new output, which is exactly the complement of the original output list with the original transition’s output appended. All other configuration components agree as well.
