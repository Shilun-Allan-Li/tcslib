<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Cryptography/MPC/BGW/Protocol.lean :: TCSlib.MPC.BGW.bgwEval_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation Preserves Addition

**Claim.** For any input assignment and circuits $a,b$, evaluating the circuit that adds $a$ and $b$ gives the pointwise sum of their partywise evaluations.

**Proof.** By the recursive definition of circuit evaluation, the evaluation of an addition gate is defined to be the sum of the evaluations of its two input circuits. Therefore the asserted equality holds directly, as an equality of functions on parties.
