<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedAnalysis.lean :: FABL.biasedSensitivity_cast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sensitivity as Indicator Sum

**Claim.** For a sign-valued function on the $n$-dimensional sign cube, its real-valued sensitivity at an input equals the sum over coordinates of the indicator that flipping that coordinate changes the function's value.

**Proof.** Sensitivity is the number of coordinates whose flip changes the function's value. Express this finite cardinality as a sum of $1$ over precisely those coordinates. The finite-sum filtering identity rewrites that restricted sum as a sum over all coordinates, with each term equal to $1$ when the flip changes the value and $0$ otherwise. This is the claimed formula.
