<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.coefficientsOfFunction_satisfies_lowDegreeF₂SampleRows -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sample equations for function coefficients

**Claim.** If the algebraic degree of a Boolean function is at most $\ell$, then its algebraic normal form coefficients, restricted to monomials of degree at most $\ell$, satisfy every sample equation formed from inputs and the function values at those inputs.

**Proof.** Take any row in the list of sample equations. Since the list is formed from the finitely indexed samples, this row comes from some index $i$ and hence uses the sample $(x_i,f(x_i))$. The characterization of satisfaction for a sample equation says that this row is satisfied exactly when the low-degree polynomial specified by the coefficient assignment evaluates at $x_i$ to the sample's second coordinate (\(\texttt{lowDegreeF₂SampleEquation_isSatisfied_iff}\)). By the degree hypothesis, evaluating the restricted algebraic normal form coefficients agrees with evaluating $f$ everywhere (\(\texttt{lowDegreeF₂Eval_coefficientsOfFunction}\)). At $x_i$ this value is $f(x_i)$, which is the row's constant, so the row is satisfied. Since the row was arbitrary, all rows are satisfied.

**Key facts.** `FABL.lowDegreeF₂SampleEquation_isSatisfied_iff`, `FABL.lowDegreeF₂Eval_coefficientsOfFunction`.
