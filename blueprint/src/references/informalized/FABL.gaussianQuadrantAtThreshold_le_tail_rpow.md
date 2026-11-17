<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/GaussianQuadrantAsymptotics.lean :: FABL.gaussianQuadrantAtThreshold_le_tail_rpow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Quadrant Tail Bound

**Claim.** For $0<\rho<1$, the Gaussian quadrant probability at threshold $t$ is at most the standard Gaussian upper tail at $t$ raised to the power $2/(1+\rho)$.

**Proof.** Set $a=2/(1+\rho)$. For each dimension $m+1$, the Hamming upper-tail indicator takes only the values $0$ and $1$, and its mean is its measure. The small-set expansion inequality therefore bounds its noise stability by its mean raised to $a$ (\texttt{smallSetExpansion}). As $m\to\infty$, these noise stabilities converge to the Gaussian quadrant probability at threshold $t$ (\texttt{tendsto\_noiseStability\_hammingUpperTailIndicator}), while the means converge to the standard Gaussian upper tail (\texttt{tendsto\_expect\_hammingUpperTailIndicator}). Since that tail is positive (\texttt{standardGaussianUpperTail\_pos}), continuity of the real power function shows that the powered means converge to the tail raised to $a$. Passing the pointwise inequalities to these limits proves the claim.

**Key facts.** `FABL.smallSetExpansion`, `FABL.tendsto_noiseStability_hammingUpperTailIndicator`, `FABL.tendsto_expect_hammingUpperTailIndicator`, `FABL.standardGaussianUpperTail_pos`.
