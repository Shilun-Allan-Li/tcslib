<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/AlgCircuit.lean :: Randomized.AlgCircuit.abs_eval_le_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sharper circuit output bound

**Claim.** If every integer input has magnitude at most $X$ for $X\ge2$, then the output of a circuit with $|G|$ gates has magnitude at most $X^{2^{|G|}}$.

**Proof.** The run bound states that every position in the values produced by a list of gates, including an absent position interpreted as zero, has magnitude at most $X^{2^{|G|}}$. Apply it to the circuit’s gate list and to the index used to define the circuit output. That value is precisely the circuit evaluation, and the list length is the circuit size.

**Key facts.** `Randomized.AlgCircuit.abs_run_le`.
