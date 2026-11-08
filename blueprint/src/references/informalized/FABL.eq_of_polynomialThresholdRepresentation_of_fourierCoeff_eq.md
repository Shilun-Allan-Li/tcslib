<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ChowTheorem.lean :: FABL.eq_of_polynomialThresholdRepresentation_of_fourierCoeff_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial threshold representation from low-degree coefficients

**Claim.** If f is represented by a polynomial threshold function p of degree at most k, p never vanishes, and g has the same Fourier coefficients as f through degree k, then g=f.

**Proof.** First compare the uniform inner products of g and f with p. By Plancherel, each is the sum over S of the product of the corresponding Fourier coefficients. For |S|≤k, the coefficients of g and f agree by assumption. For |S|>k, the coefficient of p vanishes by the degree bound (`FABL.fourierDegree_le_iff`), so those summands are zero on both sides. Plancherel (`FABL.plancherel`) therefore gives equal inner products. Now suppose, for contradiction, that g and f differ at some input x. At every input y, the threshold representation and the fact that p(y)≠0 imply g(y)p(y)≤f(y)p(y); at an input where g(y)≠f(y), the inequality is strict (`FABL.thresholdRepresentation_pointwise`). Averaging over the finite cube gives a strict inequality between the two inner products, since the pointwise inequality holds everywhere and is strict at x. This contradicts their equality, so no such input exists and g=f.

**Key facts.** `FABL.fourierDegree_le_iff`, `FABL.plancherel`, `FABL.thresholdRepresentation_pointwise`.
