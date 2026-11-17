<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Cryptography/MPC/BGW/Protocol.lean :: TCSlib.MPC.BGW.bgwEval_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a Constant Circuit

**Claim.** For any input assignment and constant $c\in F$, evaluating the constant circuit yields the constant function on parties with value $c$.

**Proof.** By the recursive definition of circuit evaluation, a constant circuit evaluates to the function that assigns $c$ to every party. This is exactly the asserted identity.
