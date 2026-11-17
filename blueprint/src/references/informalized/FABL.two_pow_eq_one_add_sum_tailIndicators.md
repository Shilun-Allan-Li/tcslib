<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFourier.lean :: FABL.two_pow_eq_one_add_sum_tailIndicators -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Truncated indicator sum for powers of two

**Claim.** If $d\le N$, then, with natural-number powers interpreted as real numbers, $2^d=1+\sum_{j=0}^{N-1}2^j\,\boldsymbol{1}_{\{j+1\le d\}}$.

**Proof.** By the finite geometric-sum identity for powers of two (\texttt{FABL.two\_pow\_eq\_one\_add\_sum\_range}), it suffices to identify the sum over $j<d$ with the indicated sum over $j<N$. Among indices below $N$, the condition $j+1\le d$ selects exactly those with $j<d$: the assumption $d\le N$ ensures every such index is below $N$. The filtered sum therefore equals the sum over $j<d$. Rewriting a filtered sum as a sum over all indices with the summand multiplied by the indicator gives the claimed formula.

**Key facts.** `FABL.two_pow_eq_one_add_sum_range`.
