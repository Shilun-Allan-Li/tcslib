<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Entropy/Basic.lean :: ProbabilityTheory.condMutualInfo_eq_zero_of_ae_eq_const_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vanishing with a constant second variable

**Claim.** If $Y=c$ almost everywhere, then $I[X:Y\mid Z;\mu]=0$.

**Proof.** Conditional mutual information is symmetric in its first two variables (`condMutualInfo_comm`). Swap $X$ and $Y$ in the expression, then apply the result that conditional mutual information vanishes when the first variable is almost everywhere constant (`condMutualInfo_eq_zero_of_ae_eq_const_left`), using the hypothesis that $Y=c$ almost everywhere.

**Key facts.** `ProbabilityTheory.condMutualInfo_eq_zero_of_ae_eq_const_left`.
