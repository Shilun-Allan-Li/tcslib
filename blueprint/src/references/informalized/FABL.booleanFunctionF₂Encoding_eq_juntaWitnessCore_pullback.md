<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.booleanFunctionF₂Encoding_eq_juntaWitnessCore_pullback -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoding a Junta Core

**Claim.** If $g$ depends only on coordinates in $J$, its binary encoding is the pullback of the binary encoding of its core on the $|J|$-dimensional cube.

**Proof.** Fix a binary input $x$. To show the two encoded values agree, use injectivity of the binary-sign equivalence and compare the corresponding sign-valued outputs. The dependence hypothesis reduces this comparison to showing that the sign inputs agree on every coordinate $i\in J$. Regard $i$ as an element $j$ of the subtype of coordinates in $J$. The combined sign vector takes at $j$ the free coordinate supplied by the core input. By the definition of the core, this is the sign encoding of the binary input at the coordinate corresponding to $j$ in the increasing enumeration of $J$. The coordinate embedding sends that enumerated coordinate back to $i$, so this value is exactly the original sign input at $i$. Thus the sign inputs agree on $J$, and dependence of $g$ gives equality of outputs. This holds for each $x$, proving the function equality.

**Key facts.** `FABL.combineSignCube_apply_free`, `FABL.binaryCubeSignEquiv_apply`.
