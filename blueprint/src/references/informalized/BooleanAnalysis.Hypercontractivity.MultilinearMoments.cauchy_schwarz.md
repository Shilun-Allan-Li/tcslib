<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Polynomial.lean :: BooleanAnalysis.Hypercontractivity.MultilinearMoments.cauchy_schwarz -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cauchy–Schwarz for Fourth Moments

**Claim.** For $A,D\in L^4(\mu)$, the square of $\int A^2D^2\,d\mu$ is at most the product of $\int A^4\,d\mu$ and $\int D^4\,d\mu$.

**Proof.** The $L^4$ assumptions imply that $A^2$ and $D^2$ belong to $L^2$. Apply the integral Cauchy–Schwarz inequality to these nonnegative functions. It gives
\[
\int A^2D^2\,d\mu\leq \left(\int A^4\,d\mu\right)^{1/2}\left(\int D^4\,d\mu\right)^{1/2}.
\]
The left side is nonnegative, as are the two fourth-moment integrals. Squaring preserves the inequality, and the squares of the square roots are the respective integrals, yielding the claim.
