<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/RestrictedWeightAlgorithm.lean :: FABL.fixedCoordinateProjectionLinear_fixedCoordinateExtension -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Projection Recovers the Extension

**Claim.** Projecting the extension that assigns zero on $J$ and agrees with $z$ outside $J$ recovers $z$.

**Proof.** Fix a coordinate $q$ in the projected cube and let $i$ be the index outside $J$ corresponding to $q$. Since $i\notin J$, the extension takes its nonzero-coordinate branch at $i$, giving the value of $z$ at the image of $i$ in the projected cube. The equivalence between the indices and their finite coordinates sends $i$ back to $q$, so this value is $z(q)$. The two functions therefore agree at every coordinate.
