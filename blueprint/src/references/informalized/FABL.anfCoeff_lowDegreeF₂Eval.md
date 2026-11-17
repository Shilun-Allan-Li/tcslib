<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.anfCoeff_lowDegreeF₂Eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coefficients of a low-degree polynomial

**Claim.** The algebraic normal form coefficients of the function formed from the assigned low-degree monomial coefficients recover those assigned coefficients on sets of size at most $\ell$, and are zero on larger sets.

**Proof.** Apply the evaluation map from coefficient families to Boolean functions. Evaluating the algebraic normal form coefficients of a function recovers that function (`anfEval_anfCoeff`). Evaluating the extended assigned coefficients gives the low-degree polynomial itself (`anfEval_extendLowDegreeF₂Coefficients`). The two coefficient families therefore have the same evaluation. Since evaluation is injective (`anfEval_injective`), the families are equal, which is the desired coefficient formula.

**Key facts.** `FABL.anfEval_anfCoeff`, `FABL.anfEval_extendLowDegreeF₂Coefficients`, `FABL.anfEval_injective`.
