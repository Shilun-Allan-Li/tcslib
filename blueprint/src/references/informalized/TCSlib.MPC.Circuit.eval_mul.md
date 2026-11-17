<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Cryptography/MPC/ArithmeticCircuit.lean :: TCSlib.MPC.Circuit.eval_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a Multiplication Gate

**Claim.** For any arithmetic circuits $a$ and $b$, the circuit formed by multiplying them evaluates to the product of their evaluations: $(ab)(v)=a(v)b(v)$.

**Proof.** By the definition of circuit evaluation, the multiplication gate with inputs $a$ and $b$ evaluates to the product of the values of its two input circuits. Thus its value is $a(v)b(v)$.
