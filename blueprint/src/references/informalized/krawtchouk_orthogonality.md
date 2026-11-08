<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/MRRW.lean :: krawtchouk_orthogonality -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Krawtchouk orthogonality

**Claim.** For $r,s\le n$, the binomially weighted inner product of the degree-$r$ and degree-$s$ Krawtchouk polynomials is zero when $r\ne s$, and is $2^n\binom{n}{r}$ when $r=s$.

**Proof.** For real $z,w$, sum the product of the two generating functions over $x$ with weight $\binom{n}{x}$. The binomial theorem evaluates this sum as $\big((1+z)(1+w)+(1-z)(1-w)\big)^n=2^n(1+zw)^n$. On the other hand, expanding both generating functions and interchanging finite sums expresses the result as a bivariate polynomial whose coefficient of $z^j w^k$ is the weighted inner product of the degree-$j$ and degree-$k$ polynomials. The right-hand expression has only diagonal terms, with coefficient $2^n\binom{n}{j}$ at $z^j w^j$. Equality of the polynomials implies equality of each coefficient: this follows by first fixing $w$ and comparing coefficients in $z$, then comparing coefficients in $w$. Taking $(j,k)=(r,s)$ proves the assertion. The generating-function identity used here is the Krawtchouk generating function (`krawtchouk_generating_function`).

**Key facts.** `krawtchouk_generating_function`.
