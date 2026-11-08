<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/GaussianQuadrantAsymptotics.lean :: FABL.tendsto_log_standardGaussianUpperTail_div_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Tail Logarithmic Rate

**Claim.** The logarithm of the standard Gaussian upper tail, divided by $t^2$, tends to $-1/2$ as $t$ tends to infinity.

**Proof.** The upstream asymptotic equivalence says that $\log(1/\Pr[Z>t])$ is asymptotic to $t^2/2$ for a standard Gaussian $Z$ (`log_inv_standardGaussianUpperTail_isEquivalent_sq`). By the characterization of asymptotic equivalence as a ratio tending to $1$, the quotient of these two quantities tends to $1$. Multiplying by $-1/2$ gives a limit of $-1/2$. Since $\log(\Pr[Z>t])=-\log(1/\Pr[Z>t])$ whenever the tail is nonzero, and $t^2/2$ is nonzero for all sufficiently large $t$, this scaled quotient agrees eventually with the expression in the claim.

**Key facts.** `FABL.log_inv_standardGaussianUpperTail_isEquivalent_sq`.
