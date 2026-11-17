<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/BentFunctions.lean :: FABL.exists_bent_extremal_coefficient -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A large Fourier coefficient

**Claim.** For even $n$ and a sign-valued function on the binary cube, some Fourier coefficient has absolute value at least $2^{-n/2}$.

**Proof.** The square-sum bound supplies a coefficient whose square is at least $2^{-n}$. Write the even integer $n$ as $k+k$, so $n/2=k$ and $2^{-n}=(2^{-k})^2$. Since the square of a real number equals the square of its absolute value, the chosen coefficient's absolute value squared is at least $(2^{-k})^2$. Both sides being compared are nonnegative, taking square roots gives the claimed bound.

**Key facts.** `FABL.exists_inv_card_le_sq_vectorFourierCoeff`.
