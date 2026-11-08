<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/OneBitHypercontractivity.lean :: FABL.uniformLInfinityNorm_affineSign -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Affine sign supremum norm

**Claim.** For real numbers $a$ and $b$, the supremum of $|a+bs|$ over the two integer signs $s\in\{-1,1\}$ is $\max\{|a+b|,|a-b|\}$.

**Proof.** The integer units are exactly $1$ and $-1$. At these two inputs, the affine function $a+bs$ takes the values $a+b$ and $a-b$, respectively. The supremum of their absolute values is therefore $\max\{|a+b|,|a-b|\}$.
