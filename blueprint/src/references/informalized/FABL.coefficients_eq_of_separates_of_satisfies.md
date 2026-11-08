<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.coefficients_eq_of_separates_of_satisfies -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniqueness from separating samples

**Claim.** If the sample inputs separate low-degree coefficient assignments, then any such assignment satisfying the sample equations for a degree-at-most-$\ell$ function equals that function's restricted algebraic normal form coefficient assignment.

**Proof.** By the separation hypothesis, it suffices to show that the given assignment and the function's restricted algebraic normal form coefficients have equal evaluations at every sample input. Fix an index $i$. The satisfaction assumption applied to the row belonging to $(x_i,f(x_i))$, together with the characterization of satisfaction for a sample equation (\(\texttt{lowDegreeF₂SampleEquation_isSatisfied_iff}\)), says the given assignment evaluates at $x_i$ to $f(x_i)$. The degree bound ensures that the restricted algebraic normal form coefficients also evaluate there to $f(x_i)$ (\(\texttt{lowDegreeF₂Eval_coefficientsOfFunction}\)). Thus the evaluations agree at every sample, and separation implies that the assignments themselves are equal.

**Key facts.** `FABL.lowDegreeF₂SampleEquation_isSatisfied_iff`, `FABL.lowDegreeF₂Eval_coefficientsOfFunction`.
