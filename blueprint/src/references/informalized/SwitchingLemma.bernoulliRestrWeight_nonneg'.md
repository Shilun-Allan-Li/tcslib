<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/BernoulliRestriction.lean :: SwitchingLemma.bernoulliRestrWeight_nonneg' -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Nonnegativity of the Bernoulli restriction weight

**Claim.** Fix a real number $p$ with $0 \le p \le 1$, and let $\rho$ be a restriction on $n$ variables, exactly $f$ of which it leaves free. Then the Bernoulli weight assigned to $\rho$, namely $p^{f}\,\bigl(\tfrac{1-p}{2}\bigr)^{\,n-f}$, is nonnegative.

**Proof.** The weight is, by definition, the product of two factors, $p^{f}$ and $\bigl(\tfrac{1-p}{2}\bigr)^{\,n-f}$, where $f$ is the number of free variables of $\rho$. A product of two nonnegative reals is nonnegative, so it suffices to show each factor is nonnegative.

The first factor is a power of $p$. Since $p \ge 0$ by hypothesis and any power of a nonnegative real is again nonnegative, we get $p^{f} \ge 0$.

The second factor is a power of the base $\tfrac{1-p}{2}$. This base is a quotient of two nonnegative reals: its numerator $1-p$ is nonnegative because $p \le 1$, and its denominator $2$ is positive. A quotient of nonnegatives is nonnegative, so $\tfrac{1-p}{2} \ge 0$, and hence so is its $(n-f)$-th power.

Multiplying the two nonnegative factors yields $0 \le p^{f}\,\bigl(\tfrac{1-p}{2}\bigr)^{\,n-f}$, which is the claim. (The exponent $n-f$ is truncated natural-number subtraction, but this plays no role: a nonnegative base raised to any natural power stays nonnegative.)
