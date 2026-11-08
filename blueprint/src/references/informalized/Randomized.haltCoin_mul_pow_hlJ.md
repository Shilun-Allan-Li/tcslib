<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BiasedCoinHalting.lean :: Randomized.haltCoin_mul_pow_hlJ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting Number Approximation Bounds

**Claim.** For each Boolean string, the scaled halting coin satisfies the stated bounds according as the string belongs or does not belong to the halting language.

**Proof.** Fix an input $x$, and abbreviate its output length by $N=\mathrm{hlN}(x)$ and its logarithmic parameter by $J=\mathrm{hlJ}(x)$. The finite-prefix decomposition gives $H4^J=\operatorname{haltPrefix}(J)+\tau$, where $0\leq\tau\leq1/3$. If $J=0$, the input cannot belong to the language, whose definition requires $J\geq1$; the length-zero prefix is zero, so the decomposition gives $H\leq1/3\leq4N+1/3$.

Now suppose $J>0$ and write $J=j+1$. Membership is then equivalent to the conjunction $N=\operatorname{haltPrefix}(j)$ and the $j$th halting digit being true. In that case the digit is one, so the recurrence gives $\operatorname{haltPrefix}(J)=4N+1$. Adding the remainder yields $4N+1\leq H4^J\leq4N+4/3$.

If the input is outside the language, compare the natural numbers $N$ and $\operatorname{haltPrefix}(j)$. If $N$ is smaller, its integer gap is at least one, and the decomposition gives $H4^J\leq4N+1/3$. If they are equal, nonmembership forces the $j$th halting digit to be zero; the prefix recurrence then gives $H4^J\leq4N+1/3$. If $N$ is larger, its integer gap is at least one, and the same recurrence and nonnegative remainder give $H4^J\geq4N+4$. The bound that each halting bit is at most one (Randomized.haltBit_le_one) supplies the digit bound used in the upper estimates.

**Key facts.** `Randomized.haltCoin_mul_pow`, `Randomized.haltBit_le_one`.
