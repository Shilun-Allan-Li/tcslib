<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTreeFourier.lean :: FABL.F₂DecisionTree.vectorFourierCoeff_pathExpansion -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Coefficient of a Path Expansion

**Claim.** The vector Fourier coefficient of a path expansion is the sum of each path’s output multiplied by the vector Fourier coefficient of its indicator.

**Proof.** Induct on the path list. For the empty list the expansion and the sum are both zero. For a list beginning with path $p$, the path expansion is the sum of $x\mapsto p.output\,p.indicator(x)$ and the expansion of the tail (`FABL.F₂DecisionTree.pathExpansion_cons`). Fourier coefficients are additive (`FABL.vectorFourierCoeff_add`), and taking the coefficient of a constant multiple pulls that constant out (`FABL.vectorFourierCoeff_const_mul`). Apply these identities and then the induction hypothesis to obtain the stated sum.

**Key facts.** `FABL.F₂DecisionTree.pathExpansion_cons`, `FABL.vectorFourierCoeff_add`, `FABL.vectorFourierCoeff_const_mul`.
