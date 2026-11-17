<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierOneNorm.lean :: FABL.binomialHalfOddReciprocalExpectation_eq_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binomial reciprocal expectation formula

**Claim.** For every natural number $m$, the expectation of $1/(2J+1)$ when $J$ has the binomial distribution with $m$ trials and success probability $1/2$ equals $\displaystyle\sum_{j=0}^{m}\binom{m}{j}2^{-m}\frac{1}{2j+1}$.

**Proof.** The integral formula for expectation under a binomial distribution expresses the expectation as a finite sum over $j=0,\ldots,m$, with probability weight $\binom mj(1/2)^j(1/2)^{m-j}$. For every such $j$, we have $j\le m$, so the two powers combine to $(1/2)^m=2^{-m}$. Multiplying this weight by the value $1/(2j+1)$ gives the displayed summand. Summing over the full range yields the formula.
