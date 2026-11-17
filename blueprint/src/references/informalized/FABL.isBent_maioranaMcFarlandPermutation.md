<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/MaioranaMcFarlandPermutation.lean :: FABL.isBent_maioranaMcFarlandPermutation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bentness under a permutation

**Claim.** For every $n$, every permutation of the $n$-dimensional binary cube, and every sign-valued function $g$ on that cube, the permutation-based Maiorana–McFarland function on the $2n$-dimensional cube is bent, with every Fourier coefficient having absolute value $2^{-n}$.

**Proof.** Fix a frequency and split it into blocks $a,b$. The block decomposition recombines to the original frequency. The Fourier coefficient formula at this joined frequency is $(2^n)^{-1}\operatorname{signValue}(g(\pi^{-1}(a)))$ times a Walsh character evaluated at $\pi^{-1}(a)$ (`vectorFourierCoeff_maioranaMcFarlandPermutation_joinF₂CubeBlocks`). The sign factor has absolute value one, since every sign value is either $-1$ or $1` (`signValue_eq_neg_one_or_one`), and the Walsh character has absolute value one (`abs_vectorWalshCharacter`). Hence the coefficient has absolute value $(2^n)^{-1}$ for every frequency.

**Key facts.** `FABL.vectorFourierCoeff_maioranaMcFarlandPermutation_joinF₂CubeBlocks`, `FABL.signValue_eq_neg_one_or_one`, `FABL.abs_vectorWalshCharacter`.
