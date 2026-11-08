<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/OneBitHypercontractivity.lean :: FABL.uniformLpNorm_affineSign -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform norm of an affine sign function

**Claim.** For real numbers $p,a,b$, the uniform $L^p$ quantity of the function sending a sign $s$ to $a+bs$ is $\left((|a+b|^p+|a-b|^p)/2\right)^{1/p}$.

**Proof.** Unfold the definition of the uniform norm and express the expectation over the two signs as a sum divided by the cardinality of the sign set, which is two. The sign values are $1$ and $-1$, so the two function values are respectively $a+b$ and $a-b$. Substituting their absolute-value powers into the average gives $(|a+b|^p+|a-b|^p)/2$; taking the outer power $p^{-1}$ yields the stated formula.
