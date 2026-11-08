<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.deterministicGoldreichLevinHypothesis_coefficients_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coefficient Estimation Accuracy

**Claim.** For every member of the nonempty family, the rational sample estimate, viewed as a real number, differs from the corresponding Fourier coefficient by at most the family-scaled accuracy.

**Proof.** Fix a member $U$ of the family. The deterministic small-bias Fourier estimate differs from the true coefficient by at most the bias parameter of the coefficient input (`abs_deterministicSmallBiasFourierEstimate_sub_fourierCoeff_le`). The rational estimate agrees with that real-valued small-bias estimate after casting to the reals (`rationalSmallBiasFourierEstimate_cast`), so it has the same error bound. By the choice of the coefficient input, its bias is $\varepsilon/(2C)$, where $C$ is the active cap (`coefficientInput_epsilon`). The active cap is positive (`goldreichLevinActiveCap_pos`), and the family is nonempty, so its cardinality is positive and is at most $C$. Hence $\varepsilon/(2C)\leq \varepsilon/(2|\mathcal F|)$. The latter is precisely the first component of the finite-family accuracy parameter, giving the claimed estimate.

**Key facts.** `FABL.abs_deterministicSmallBiasFourierEstimate_sub_fourierCoeff_le`, `FABL.rationalSmallBiasFourierEstimate_cast`, `FABL.DeterministicGoldreichLevinInput.coefficientInput_epsilon`, `FABL.goldreichLevinActiveCap_pos`.
