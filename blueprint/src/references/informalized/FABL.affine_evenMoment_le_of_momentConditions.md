<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.affine_evenMoment_le_of_momentConditions -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Even-moment bound from moment conditions

**Claim.** Under the stated vanishing odd-moment and upper even-moment conditions, together with $\rho\ge0$ and $\rho^2\le1/(2r-1)$, every affine even moment satisfies $\mathbb E_\mu[(a+\rho bX)^{2r}]\le(a^2+b^2)^r$.

**Proof.** Expand the affine moment by the binomial theorem for expectations ($\texttt{pmfExpectation_affine_pow}$). The odd powers vanish by the assumed odd-moment conditions, so the sum over all powers reduces to the even indices ($\texttt{sum_range_two_mul_add_one_eq_sum_even}$). For an even index $2j$ with $1\le j\le r$, the assumed moment bound, after multiplying by $\binom{2r}{2j}$, gives $\binom{2r}{2j}\mathbb E[X^{2j}]\le(2r-1)^j\binom rj$. The constraint on $\rho^2$ then implies $\rho^{2j}(2r-1)^j\le1$, hence $\binom{2r}{2j}\rho^{2j}\mathbb E[X^{2j}]\le\binom rj$. The factors $a^{2(r-j)}$ and $b^{2j}$ are nonnegative, so each even-index contribution is bounded by $\binom rj(a^2)^{r-j}(b^2)^j$. For $j=0$, the contribution is exactly $a^{2r}$. Summing these bounds and applying the binomial theorem gives $(a^2+b^2)^r$.

**Key facts.** `FABL.pmfExpectation_affine_pow`, `FABL.sum_range_two_mul_add_one_eq_sum_even`, `FABL.pmfExpectation_const`.
