<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/SmallSetExpansion.lean :: FABL.uniformLpNorm_four_pow_eq_expect_fourth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourth moment identity

**Claim.** For a finite set $\Omega$ and $f:\Omega\to\mathbb R$, the fourth power of the uniform $L^4$ norm of $f$ is the uniform mean of $x\mapsto f(x)^4$.

**Proof.** Unfold the norm. First identify the fourth absolute moment with the fourth moment: at each point where $f(x)=0$ both expressions vanish; otherwise, write the fourth real power of $|f(x)|$ as the product of two second powers, and use $|f(x)|^2=f(x)^2$ to obtain $f(x)^4$. Averaging this pointwise identity gives the equality of moments. That mean is nonnegative, since every summand is a fourth power. The rule for raising a nonnegative real power to a positive integer power then cancels the outer exponent $1/4$ and yields the claimed identity.
