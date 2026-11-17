<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ThresholdFunctionCounting.lean :: FABL.natCard_linearThresholdFunction_le_two_pow_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic-exponent threshold bound

**Claim.** For every $n\in\mathbb N$, the number of linear threshold functions is at most $2^{(n+1)^2}$, yielding in particular the stated $2^{n^2+O(n)}$ bound.

**Proof.** The family of subsets of the $n$ coordinates of size at most one has cardinality $n+1$: it consists of the empty set and the $n$ singleton sets. Apply the profile-count bound to obtain at most $(2^n+1)^{n+1}$ functions. Since $2^n+1\le 2^{n+1}$, this is at most $(2^{n+1})^{n+1}=2^{(n+1)^2}$.

**Key facts.** `FABL.card_lowDegreeFourierFamily_eq_sum_choose`, `FABL.natCard_linearThresholdFunction_le_profileCount`, `FABL.two_pow_add_one_le_next_two_pow`.
