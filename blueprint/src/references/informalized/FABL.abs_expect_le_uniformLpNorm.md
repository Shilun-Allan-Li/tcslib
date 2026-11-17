<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/OneBitHypercontractivity.lean :: FABL.abs_expect_le_uniformLpNorm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation Bounded by Uniform $L^q$ Norm

**Claim.** For a finite nonempty set $\Omega$, a real $q\ge1$, and a real-valued function $f$ on $\Omega$, the absolute value of the uniform average of $f$ is at most its uniform $L^q$ norm.

**Proof.** The absolute value of the average of $f$ is at most the average of $|f|$. Apply the weighted $L^q$ mean inequality to the uniform weights, which are nonnegative, and to the nonnegative function $|f|$. The weights average to $1$, so the inequality bounds the average of $|f|$ by $(\mathbb E_x |f(x)|^q)^{1/q}$, the stated uniform $L^q$ norm.
