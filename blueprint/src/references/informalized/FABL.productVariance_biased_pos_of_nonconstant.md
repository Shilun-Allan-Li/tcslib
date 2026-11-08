<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedAnalysis.lean :: FABL.productVariance_biased_pos_of_nonconstant -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive variance of nonconstant functions

**Claim.** Every nonconstant sign-valued function on the sign cube has strictly positive variance under a product law with parameter $0<p<1$.

**Proof.** The variance is nonnegative because it is the expectation of a square (\texttt{pmfExpectation\_nonneg}). Suppose it were not strictly positive; then it would equal zero. Writing the centered function as its value minus its mean, the variance is its inner product with itself, so the zero- norm criterion for a full-support law implies that this centered function vanishes at every input (\texttt{pmfInner\_self\_eq\_zero\_iff}). The product law has full support because each coordinate law does (\texttt{biasedSignPMF\_hasFullSupport} and \texttt{productProbabilityPMF\_hasFullSupport}). Hence any two inputs have function values equal to the same mean, contradicting nonconstancy. In passing from equality of the real sign values to equality of the signs, use injectivity of the sign-value map (\texttt{signValue\_injective}).

**Key facts.** `FABL.pmfExpectation_nonneg`, `FABL.pmfInner_eq_expect`, `FABL.biasedSignPMF_hasFullSupport`, `FABL.productProbabilityPMF_hasFullSupport`, `FABL.pmfInner_self_eq_zero_iff`, `FABL.signValue_injective`.
