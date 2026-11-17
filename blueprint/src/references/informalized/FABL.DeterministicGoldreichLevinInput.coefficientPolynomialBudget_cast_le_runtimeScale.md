<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.DeterministicGoldreichLevinInput.coefficientPolynomialBudget_cast_le_runtimeScale -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coefficient Polynomial Budget Bound

**Claim.** The coefficient input's polynomial budget is at most $2^{138}$ times the eighty-eighth power of the runtime scale.

**Proof.** The polynomial budget is $2^{18}$ times the eighth power of the generator scale plus one. The generator-scale estimate bounds that quantity before taking the eighth power by $2^{15}R^{11}$. Raising both sides to the eighth power preserves the inequality, and multiplying by $2^{18}$ gives $2^{18}(2^{15}R^{11})^8=2^{138}R^{88}$.

**Key facts.** `FABL.DeterministicGoldreichLevinInput.coefficientGeneratorScale_add_one_cast_le_runtimeScale`.
