<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.productVariance_pos_of_nonconstant -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Variance for Nonconstant Functions

**Claim.** If the marginal probability mass function assigns positive mass to every point, every nonconstant function on its finite product space has strictly positive variance.

**Proof.** The variance is nonnegative because it is the expectation of a square. Suppose it were not strictly positive; together with nonnegativity this forces it to be zero. Center the function by subtracting its mean. The inner product of this centered function with itself is exactly the variance, by the identity relating the inner product to expectation (FABL.pmfInner_eq_expect). Thus its squared norm is zero. Full support of the product law follows from full support of each marginal (FABL.productProbabilityPMF_hasFullSupport), and under a full-support law a function has zero squared norm only if it vanishes everywhere (FABL.pmfInner_self_eq_zero_iff). Hence the original function equals its mean at every point and is constant, contradicting the hypothesis. Its variance must therefore be strictly positive.

**Key facts.** `FABL.pmfExpectation_nonneg`, `FABL.pmfInner_eq_expect`, `FABL.productProbabilityPMF_hasFullSupport`, `FABL.pmfInner_self_eq_zero_iff`.
