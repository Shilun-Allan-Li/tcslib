<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/MRRW.lean :: finite_n_mrrw_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite MRRW bound

**Claim.** Under the stated degree and root-location hypotheses on the Krawtchouk polynomials, and the assumed nonpositivity of the kernel on distances from $d$ through $n$, the maximum size of a binary code of length $n$ and minimum distance at least $d$ is at most $\operatorname{cdKernel}(n,t,a,0)$.

**Proof.** Apply the Delsarte linear-programming bound with coefficients $F(j)=K_j(a)/\binom{n}{j}$ for $j\le t$ and $F(j)=0$ for $j>t$. The degree condition $t+1\le n$ ensures that the evaluations needed below correspond to indices within the range of the Krawtchouk polynomials. The coefficient at zero is positive: $K_0(a)=1$ and $\binom n0=1$. For $1\le j\le n$, the coefficients are nonnegative. When $j\le t$, this follows from positivity below the smallest zero: the hypothesis that $a$ lies below every zero of $K_t$ implies $K_j(a)>0$ for all $j\le t$ (the positivity result `krawtchouk_positive_below_smallest_zero`); the binomial denominator is positive. When $j>t$, the coefficient is zero.

For each integer distance $x$ with $d\le x\le n$, the weighted Krawtchouk sum in the linear-programming bound agrees with the kernel $\operatorname{cdKernel}(n,t,a,x)$. Indeed, the polynomial evaluation identity `krawtchoukPoly_eval_nat` identifies each polynomial value at the integer $x$ with the corresponding Krawtchouk value, and the nonzero coefficients restrict the sum to indices through $t$. The assumed kernel inequality therefore makes this sum nonpositive on all required distances. The Delsarte bound now gives the code-size upper bound as the ratio of the weighted sum at zero to $F(0)$. Since $F(0)=1$, this ratio is exactly $\operatorname{cdKernel}(n,t,a,0)$.

**Key facts.** `delsarte_lp_bound`, `krawtchouk_positive_below_smallest_zero`, `krawtchoukPoly_eval_nat`.
