<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/Centered.lean :: BooleanAnalysis.Hypercontractivity.CenteredContraction.norm_le_of_scalar -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Centered norm contraction

**Claim.** Under the scalar inequality, a mean-zero random variable contracts the real-valued $L^q$ norm when the constant part is changed from $a+X$ to $a-cX$.

**Proof.** Since $q>0$, both affine random variables belong to $L^q$: this follows from the assumed membership of $X$ and closure under addition and scalar multiplication. Their powered absolute values are therefore integrable, and $X$ itself is integrable because $q\ge 2$ on a probability space. Apply the affine scalar estimate pointwise with $x=X(\omega)$. It gives
\[
|a-cX(\omega)|^q\le |a+X(\omega)|^q-bX(\omega),\qquad b=\frac{q(1+c)|a|^q}{a}.
\]
Integrating is valid by the integrability just noted. The correction term has integral $b\int X\,d\mu=0$ by the mean-zero hypothesis, so the $q$th-power integral on the left is at most the one on the right. Finally, the real-valued $L^q$ norm raised to the power $q$ equals the integral of the absolute value to that power (the identity `rvLpNorm_rpow`). Since both norms are nonnegative and $q>0$, taking the increasing $q$th root yields the desired norm inequality.

**Key facts.** `BooleanAnalysis.Hypercontractivity.CenteredContraction.scalar_affine`, `BooleanAnalysis.Hypercontractivity.rvLpNorm_rpow`.
