<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.pmfExpectation_affine_evenMoment_of_oddMoments -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Even Affine Moment from Odd Moments

**Claim.** If the odd moments of $X$ through degree $2r-1$ vanish, then the expectation of $(1+cX)^{2r}$ is the sum of its even-degree binomial terms: $\sum_{j=0}^{r}\binom{2r}{2j}c^{2j}\mathbb E_{\mathrm{law}}[X^{2j}]$.

**Proof.** For each natural number $k$, define the $k$th binomial contribution to be $\binom{2r}{k}1^{2r-k}c^k\mathbb E_{\mathrm{law}}[X^k]$. The binomial expansion for affine moments (\texttt{FABL.pmfExpectation\_affine\_pow}), applied with constant term $1$ and exponent $2r$, expresses the desired expectation as the sum of these contributions for $0\le k\le 2r$. For every $j<r$, the assumed vanishing of the $(2j+1)$st moment applies with index $j+1$, since $1\le j+1\le r$. Thus each odd-indexed contribution, at $k=2j+1$, vanishes. The finite-sum identity that removes these zero odd terms converts the sum over $0\le k\le 2r$ into the sum over even indices $k=2j$, $0\le j\le r$ (\texttt{FABL.sum\_range\_two\_mul\_add\_one\_eq\_sum\_even}). Substituting $k=2j$ leaves the stated binomial coefficient, power of $c$, and even moment.

**Key facts.** `FABL.pmfExpectation_affine_pow`, `FABL.sum_range_two_mul_add_one_eq_sum_even`.
