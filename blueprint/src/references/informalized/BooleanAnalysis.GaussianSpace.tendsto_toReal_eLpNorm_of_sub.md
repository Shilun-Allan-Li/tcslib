<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/LpBounds.lean :: BooleanAnalysis.GaussianSpace.tendsto_toReal_eLpNorm_of_sub -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Convergence of real-valued $L^p$ norms

**Claim.** If $F_m$ and $f$ belong to $L^p(\mu)$ and the $L^p$ norm of $F_m-f$ tends to zero, then the real-valued $L^p$ norms of $F_m$ converge to the real-valued $L^p$ norm of $f$.

**Proof.** Regard $F_m$ and $f$ as elements of the normed space $L^p(\mu)$. The $L^p$ convergence criterion says that convergence in this space is equivalent to the eLp norm of the difference tending to zero. The hypothesis therefore gives convergence of the classes of $F_m$ to the class of $f$ in $L^p$. The norm is continuous, so their norms converge. The norm of an $L^p$ class is its eLp norm, and taking the real-valued norms gives exactly the asserted convergence.
