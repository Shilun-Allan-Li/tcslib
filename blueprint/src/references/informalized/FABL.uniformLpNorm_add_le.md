<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/OneBitHypercontractivity.lean :: FABL.uniformLpNorm_add_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Triangle inequality for the uniform norm

**Claim.** For a finite nonempty set $\Omega$, a real number $q\ge 1$, and functions $f,g:\Omega\to\mathbb R$, the uniform $L^q$ quantity of $f+g$ is at most the sum of the uniform $L^q$ quantities of $f$ and $g$.

**Proof.** Let $N=|\Omega|$, which is positive. Express each expectation as the corresponding sum divided by $N$. The three sums of $q$th powers of absolute values are nonnegative, so the real-power rule for a quotient lets us move the common factor $N^{-1}$ through the exponent $q^{-1}$. The finite-sum $L^q$ triangle inequality (`Real.Lp_add_le`) bounds $\left(\sum_x |f(x)+g(x)|^q\right)^{1/q}$ by the sum of the corresponding expressions for $f$ and $g$. Dividing this inequality by the nonnegative number $N^{1/q}$ preserves its direction. Distributing that common denominator across the sum gives exactly the two normalized quantities on the right, proving the result.
