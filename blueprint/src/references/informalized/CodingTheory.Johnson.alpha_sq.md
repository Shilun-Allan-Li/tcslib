<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/JohnsonBound.lean :: CodingTheory.Johnson.alpha_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# The Square of the Johnson Shift Parameter

**Claim.** Let $n$ and $d$ be natural numbers with $n > 0$ and $2d \le n$. The shift parameter is defined by $\alpha(n,d) = \sqrt{(n - 2d)/n}$. We show that squaring it recovers the radicand exactly, i.e.
\[
\alpha(n,d)^2 = \frac{n - 2d}{n}.
\]

**Proof.** Since $\alpha(n,d)$ is by definition the real square root $\sqrt{(n-2d)/n}$, the claim is just the identity $(\sqrt{x})^2 = x$. In $\mathbb{R}$ this holds only when $x \ge 0$ (for negative $x$ the real square root is set to $0$, and squaring then gives $0 \ne x$), so the one thing to verify is that the radicand is nonnegative.

That nonnegativity is where both hypotheses are spent. From $n > 0$ we get $(n : \mathbb{R}) > 0$ after casting to the reals, so the denominator is positive. From $2d \le n$, cast to an inequality $2d \le n$ over $\mathbb{R}$, the numerator satisfies $n - 2d \ge 0$. A nonnegative number divided by a positive number is nonnegative, so $(n - 2d)/n \ge 0$.

With the radicand known to be nonnegative, the identity $(\sqrt{x})^2 = x$ for $x \ge 0$ (Mathlib's `Real.sq_sqrt`) applies with $x = (n-2d)/n$, giving
\[
\alpha(n,d)^2 = \left(\sqrt{\tfrac{n-2d}{n}}\right)^2 = \frac{n - 2d}{n},
\]
which is the claim. Unfolding the definition of $\alpha$ is the only remaining bookkeeping.
