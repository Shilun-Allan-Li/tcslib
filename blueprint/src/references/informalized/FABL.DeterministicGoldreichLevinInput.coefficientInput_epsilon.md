<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.DeterministicGoldreichLevinInput.coefficientInput_epsilon -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coefficient Input Accuracy

**Claim.** The coefficient input's accuracy is the learning parameter divided by twice the active cap.

**Proof.** The coefficient input's accuracy is obtained by dividing the original rational accuracy by the Fourier bound, while its learning parameter is that same rational accuracy. Expanding these definitions and clearing denominators reduces the claimed identity to arithmetic. The denominators are nonzero: the original accuracy denominator is positive by the input hypotheses, and the active cap is positive by the active-cap positivity result (`goldreichLevinActiveCap_pos`). Thus the algebra is valid and gives the formula.

**Key facts.** `FABL.goldreichLevinActiveCap_pos`.
