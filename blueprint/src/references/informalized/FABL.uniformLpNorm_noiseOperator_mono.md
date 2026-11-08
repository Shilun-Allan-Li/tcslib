<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/NoiseOperatorExercises.lean :: FABL.uniformLpNorm_noiseOperator_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity in the noise parameter

**Claim.** If $0\le\rho\le\sigma\le1$ and $p\ge1$, then the uniform $L^p$ norm of the noise-operator image at parameter $\rho$ is at most that of the image at parameter $\sigma$.

**Proof.** First handle the case $\sigma=0$. The inequalities $0\le\rho\le\sigma$ force $\rho=0$, so both sides are equal. Otherwise, $\sigma>0$; set $\tau=\rho/\sigma$. The assumptions imply $0\le\tau\le1$. Apply noise-operator contraction at parameter $\tau$ to the function already obtained by applying the noise operator at parameter $\sigma$. The composition identity for noise operators (noiseOperator_comp) says that this result is the noise operator at parameter $\tau\sigma$, and the definition of $\tau$ gives $\tau\sigma=\rho$. Thus contraction is precisely the desired comparison.

**Key facts.** `FABL.uniformLpNorm_noiseOperator_le`, `FABL.noiseOperator_comp`.
