<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ProductHypercontractivity.lean :: FABL.signNoiseOperator_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Identity at Full Noise Parameter

**Claim.** For every real-valued function on the sign set, the sign noise operator with parameter $1$ is the identity.

**Proof.** Fix a sign $x$. By the definition of the noise operator, its value at parameter $1$ is the even coefficient of $f$ plus its odd coefficient times the sign value of $x$. The affine reconstruction formula for functions on the two-point sign set says this is exactly $f(x)$ (`sign_affine_reconstruct`). Since the values agree at every sign, the two functions are equal.

**Key facts.** `FABL.sign_affine_reconstruct`.
