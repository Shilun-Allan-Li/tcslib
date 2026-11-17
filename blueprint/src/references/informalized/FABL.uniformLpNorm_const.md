<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/NoiseOperatorExercises.lean :: FABL.uniformLpNorm_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform norm of a constant function

**Claim.** For a finite nonempty set $\Omega$, a real number $q>0$, and a real constant $c$, the uniform $L^q$ quantity of the constant function with value $c$ is $|c|$.

**Proof.** Write the constant function as $c$ times the constant function with value $1$. The scaling law for the uniform norm (`FABL.uniformLpNorm_const_mul`) says its norm is $|c|$ times the norm of the latter function. For the constant function $1$, every term in the defining expectation is $1$, so the expectation and its $q^{-1}$ power are both $1$. The desired value is therefore $|c|$.

**Key facts.** `FABL.uniformLpNorm_const_mul`.
