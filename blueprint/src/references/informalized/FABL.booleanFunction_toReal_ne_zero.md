<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/SparsePolynomialApproximation.lean :: FABL.booleanFunction_toReal_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonvanishing of the Real-Valued Function

**Claim.** Viewing the outputs of a sign-valued Boolean function as real numbers gives a function that is nonzero at every input, and therefore is not the zero function.

**Proof.** Assume the real-valued function is identically zero and evaluate it at the all-positive input. Its value there must be zero. But every sign has real value either $-1$ or $1$ (the fact `FABL.signValue_eq_neg_one_or_one`), so the value of the original function at that input cannot be zero. This contradiction proves nonvanishing.

**Key facts.** `FABL.signValue_eq_neg_one_or_one`.
