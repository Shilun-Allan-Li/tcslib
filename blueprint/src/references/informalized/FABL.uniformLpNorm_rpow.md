<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractiveApplications.lean :: FABL.uniformLpNorm_rpow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Power of the uniform norm

**Claim.** For a finite set $\Omega$, $q>0$, and $f:\Omega\to\mathbb R$, the $q$th power of the uniform $L^q$ norm equals the uniform mean of $|f|^q$.

**Proof.** The mean of $|f(x)|^q$ is nonnegative, since every term is a real power of a nonnegative number. By definition, the norm is this mean raised to the power $1/q$. Raising that result to the power $q$ combines the exponents into $(1/q)q=1$; this exponent multiplication is valid for the nonnegative base. Since $q>0$, the exponents cancel, leaving the original mean.
