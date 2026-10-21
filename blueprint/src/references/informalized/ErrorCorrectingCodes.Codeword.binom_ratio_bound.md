<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/ListDecoding.lean :: ErrorCorrectingCodes.Codeword.binom_ratio_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# A ratio bound for binomial coefficients

**Claim.** For natural numbers $N$, $M$, and $k$ with $k \le M \le N$, the binomial coefficients satisfy
\[
\frac{\binom{N-k}{M-k}}{\binom{N}{M}} \;\le\; \left(\frac{M}{N}\right)^{k},
\]
the comparison being made in the real numbers. Intuitively, the left-hand side is the probability that a random $M$-subset of an $N$-set contains a fixed $k$-set, and this probability is at most $(M/N)^k$.

**Proof.** The proof rewrites the ratio as a product of $k$ simple fractions, bounds each factor by $M/N$, and multiplies the bounds together.

1. **The ratio is a product of falling fractions.** The central claim is the identity
\[
\frac{\binom{N-k}{M-k}}{\binom{N}{M}} \;=\; \prod_{i=0}^{k-1} \frac{M-i}{N-i}.
\]
Since $M \le N$, the denominator $\binom{N}{M}$ is a positive integer ($\binom{N}{M} > 0$ when $M \le N$, `Nat.choose_pos`), so it is legitimate to clear it and work with the equivalent product identity.

2. **The subset-of-a-subset identity.** The link between the two sides is the "committee–chair" identity
\[
\binom{N-k}{M-k}\,\binom{N}{k} \;=\; \binom{N}{M}\,\binom{M}{k}
\]
(`Nat.choose_mul`): choosing an $M$-element committee from $N$ people and then a $k$-element subcommittee from it is the same as first choosing the $k$-element subcommittee from all $N$ people and then completing it with $M-k$ of the remaining $N-k$. Rearranged, this says
\[
\frac{\binom{N-k}{M-k}}{\binom{N}{M}} \;=\; \frac{\binom{M}{k}}{\binom{N}{k}}.
\]

3. **Expanding the two binomial coefficients as falling factorials.** Writing each $\binom{\cdot}{k}$ through its falling factorial, $\binom{n}{k} = n^{\underline{k}}/k!$ with $n^{\underline{k}} = \prod_{i=0}^{k-1}(n-i)$ (the Lean combines `Nat.descFactorial_eq_factorial_mul_choose` with `Nat.descFactorial_eq_prod_range`), gives
\[
\binom{M}{k} = \frac{\prod_{i=0}^{k-1}(M-i)}{k!}, \qquad \binom{N}{k} = \frac{\prod_{i=0}^{k-1}(N-i)}{k!}.
\]
Because every index satisfies $i < k \le M \le N$, each factor $N-i$ is at least $N-(k-1) \ge 1 > 0$, so $\prod_{i<k}(N-i) \neq 0$ and the quotient is well defined (the Lean dispatches the vacuous "product is zero" alternative by contradiction, since $\binom{N}{k} > 0$). Dividing the two expressions, the common factor $k!$ cancels and yields exactly the product in Step 1:
\[
\frac{\binom{M}{k}}{\binom{N}{k}} = \frac{\prod_{i<k}(M-i)}{\prod_{i<k}(N-i)} = \prod_{i=0}^{k-1}\frac{M-i}{N-i}.
\]

3. **Each factor is at most $M/N$.** Fix $i$ with $0 \le i < k$. Both $N-i$ and $N$ are positive, so
\[
\frac{M-i}{N-i} \le \frac{M}{N} \iff (M-i)N \le M(N-i) \iff iM \le iN,
\]
and the last inequality holds because $M \le N$ and $i \ge 0$. (The hypothesis $i+1 \le M$, available since $i < k \le M$, also guarantees $M-i > 0$, so the factor is nonnegative.)

4. **Multiplying the bounds.** All $k$ factors $\frac{M-i}{N-i}$ are nonnegative and each is bounded above by $M/N$, so monotonicity of a product of nonnegative reals (`Finset.prod_le_prod`) gives
\[
\prod_{i=0}^{k-1}\frac{M-i}{N-i} \;\le\; \prod_{i=0}^{k-1}\frac{M}{N} \;=\; \left(\frac{M}{N}\right)^{k},
\]
the final equality being the product of a constant over $k$ indices (`Finset.prod_const` with `Finset.card_range`). Combining this with the identity of Step 1 completes the proof.
