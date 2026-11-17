<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Cryptography/MPC/BGW/Protocol.lean :: TCSlib.MPC.BGW.bgwEval_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# BGW Evaluation at a Multiplication Gate

**Claim.** For any input assignment and circuits $a,b$, BGW evaluation of the circuit multiplying $a$ and $b$ is the degree-reduced pointwise product of their evaluations.

**Proof.** By the defining clause for BGW evaluation at a multiplication gate, its value is exactly the degree-reduction procedure applied to the pointwise product of the evaluations of $a$ and $b$.
