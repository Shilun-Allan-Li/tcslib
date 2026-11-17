<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevinAlgorithm/Adaptive.lean :: FABL.goldreichLevinActiveInvariant_sound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Soundness of the Active Family

**Claim.** Every set in the active family at stage $n$ has Fourier coefficient magnitude strictly greater than $\tau/2$.

**Proof.** The proof first notes that $\tau>0$. It then separates the case $n=0$ from positive dimension. If $n=0$, the only frequency set is empty. Parseval's identity says the sum of squares of all Fourier coefficients is $1$; since there is only this one coefficient, its square is $1$, so its magnitude is $1$. Using $\tau\le1$ gives $\tau/2<1$. If $n=k+1$, the invariant's third clause applies to any active set $U$. At stage $n$, the prefix coordinates are all coordinates (`prefixCoordinates_eq_univ`), and the restricted weight on all coordinates equals the square of the corresponding Fourier coefficient (`restrictedFourierWeight_univ_freeFrequencyPart`). Thus that clause gives $\tau^2/4<|\widehat f(U)|^2$. Since both $\tau/2$ and the magnitude are nonnegative, taking square roots yields $\tau/2<|\widehat f(U)|$.

**Key facts.** `FABL.sum_sq_fourierCoeff_eq_one`, `FABL.prefixCoordinates_eq_univ`, `FABL.restrictedFourierWeight_univ_freeFrequencyPart`.
