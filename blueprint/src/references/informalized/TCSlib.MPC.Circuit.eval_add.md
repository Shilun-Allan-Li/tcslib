<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Cryptography/MPC/ArithmeticCircuit.lean :: TCSlib.MPC.Circuit.eval_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of an Addition Gate

**Claim.** For a commutative ring $F$, evaluating the circuit formed by adding $a$ and $b$ gives the sum of their evaluations: $(a+b)(v)=a(v)+b(v)$.

**Proof.** By the defining clause for ordinary circuit evaluation at an addition gate, the value of the gate is the sum of the values of its two input circuits.
