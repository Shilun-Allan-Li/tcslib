<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.monotone_bribeFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity After Coordinate Fixing

**Claim.** Fixing every coordinate in $J$ to a sign $b$ and then applying a monotone Boolean function preserves monotonicity.

**Proof.** Take inputs $x\le y$ coordinatewise. At each coordinate in $J$, both modified inputs have the same value $b$, so the order is preserved there. At each coordinate outside $J$, the modified inputs retain $x_i$ and $y_i$, and $x_i\le y_i$ by assumption. Thus the two modified inputs are ordered coordinatewise, and monotonicity of $f$ gives the desired inequality between their function values.
