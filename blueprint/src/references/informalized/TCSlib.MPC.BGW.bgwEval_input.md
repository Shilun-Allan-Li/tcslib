<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Cryptography/MPC/BGW/Protocol.lean :: TCSlib.MPC.BGW.bgwEval_input -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of an Input Circuit

**Claim.** For any input assignment and input wire $i$, evaluating that input circuit yields the function assigning each party its input value at $i$.

**Proof.** By the recursive definition of circuit evaluation, the input circuit labeled by $i$ evaluates to the input assignment at $i$. This is the claimed function on parties.
