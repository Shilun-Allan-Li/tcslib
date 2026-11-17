<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Cryptography/MPC/ArithmeticCircuit.lean :: TCSlib.MPC.Circuit.eval_smul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of Scalar Multiplication

**Claim.** For every circuit $a$ and scalar $c$, the circuit obtained by multiplying $a$ by the public constant $c$ evaluates to $c$ times the value of $a$.

**Proof.** By the definition of circuit evaluation, a scalar multiplication gate labeled by $c$ evaluates to $c$ multiplied by the evaluation of its input circuit $a$.
