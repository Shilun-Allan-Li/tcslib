<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Cryptography/MPC/BGW/Protocol.lean :: TCSlib.MPC.BGW.bgwEval_smul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scalar Multiplication of Circuit Shares

**Claim.** At every party, BGW evaluation of the circuit obtained by multiplying $a$ by the public scalar $c$ equals $c$ times that party's BGW evaluation of $a$.

**Proof.** This is the defining clause for BGW evaluation at a public-scalar gate: at each party, the gate returns the scalar multiplied by the child's share.
