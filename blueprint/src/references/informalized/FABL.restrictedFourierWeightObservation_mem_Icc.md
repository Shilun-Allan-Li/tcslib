<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/RestrictedWeights.lean :: FABL.restrictedFourierWeightObservation_mem_Icc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restricted Fourier Observation Bounds

**Claim.** For every Boolean target, every fixed assignment outside $J$, and every two assignments on $J$, the restricted Fourier weight observation lies in $[-1,1]$.

**Proof.** At each input $x$, the Boolean target takes one of the two signs, so its real-valued version satisfies $f(x)^2=1$; this follows from the fact that every sign value is either $-1$ or $1$ (`signValue_eq_neg_one_or_one`). Also, every indexed monomial on a sign cube squares to $1$ (`indexedMonomial_sq`). Thus each restriction coefficient observation, which is a product of one target value and one indexed monomial, has square $1$. The restricted Fourier weight observation is the product of two such observations, so its square is also $1$. A real number whose square is $1$ is either $-1$ or $1$, and hence belongs to $[-1,1]$.

**Key facts.** `FABL.signValue_eq_neg_one_or_one`, `FABL.indexedMonomial_sq`.
