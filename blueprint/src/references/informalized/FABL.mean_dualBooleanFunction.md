<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.mean_dualBooleanFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of the Dual Function

**Claim.** Negating every input coordinate and then negating the output changes the mean of a Boolean function to its negative.

**Proof.** Write the dual’s real-valued output as the negative of the original function’s real-valued output evaluated at the coordinatewise negation of the input. The mean of a negative is the negative of the mean, so it remains to identify the mean after this input change. Coordinatewise negation is a bijection of the sign cube, hence permutes its inputs and preserves the uniform average. The resulting mean is therefore the negative of the original mean.
