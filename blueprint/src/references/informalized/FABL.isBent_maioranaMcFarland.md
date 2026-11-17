<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/BentFunctions.lean :: FABL.isBent_maioranaMcFarland -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Maiorana–McFarland bentness

**Claim.** For every $n$ and every sign-valued function $g$ on the $n$-dimensional binary cube, the Maiorana–McFarland construction on the $2n$-dimensional cube is bent, with every Fourier coefficient having absolute value $2^{-n}$.

**Proof.** Fix a frequency on the $2n$-dimensional cube and split it into two $n$-coordinate blocks $a,b$ using the block decomposition. Reassembling these blocks recovers the original frequency. The Fourier coefficient formula for the construction at this joined frequency is $(2^n)^{-1}\operatorname{signValue}(g(a))$ times a Walsh character evaluated at $a$ (`vectorFourierCoeff_maioranaMcFarland_joinF₂CubeBlocks`). The sign value has absolute value one because it is either $-1$ or $1$ (`signValue_eq_neg_one_or_one`), and the Walsh character also has absolute value one (`abs_vectorWalshCharacter`). Taking absolute values therefore leaves $(2^n)^{-1}$.

**Key facts.** `FABL.vectorFourierCoeff_maioranaMcFarland_joinF₂CubeBlocks`, `FABL.signValue_eq_neg_one_or_one`, `FABL.abs_vectorWalshCharacter`.
