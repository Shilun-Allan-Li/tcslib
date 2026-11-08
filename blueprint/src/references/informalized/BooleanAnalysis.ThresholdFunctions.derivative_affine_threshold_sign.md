<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/LinearThresholdInfluence.lean :: BooleanAnalysis.ThresholdFunctions.derivative_affine_threshold_sign -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unateness of linear threshold functions

**Claim.** For each coordinate, the discrete derivative of a linear threshold function has one sign throughout the Boolean cube: it is everywhere nonnegative or everywhere nonpositive.

**Proof.** Fix the coordinate $i$. For any point $x$, the affine form evaluated with coordinate $i$ set to $0$ is the sum of the contribution from the other coordinates and $a_i$; with coordinate $i$ set to $1$, it is that same other-coordinate contribution minus $a_i$. This decomposition is the affine-form update identity (`affine_form_update`), together with the sign values of the two bits (`boolToSign_false`, `boolToSign_true`). If $a_i\ge0$, the first input is at least the second. Monotonicity of the threshold sign (`thresholdSign_mono`) therefore orders the two function values in the same direction, making their difference, and hence the derivative, nonnegative. If $a_i<0$, the input order reverses; monotonicity gives the reverse order of the threshold values, so the derivative is nonpositive. The choice of case depends only on $a_i$, not on $x$, proving unateness.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.affine_form_update`, `BooleanAnalysis.boolToSign_false`, `BooleanAnalysis.boolToSign_true`, `BooleanAnalysis.ThresholdFunctions.thresholdSign_mono`.
