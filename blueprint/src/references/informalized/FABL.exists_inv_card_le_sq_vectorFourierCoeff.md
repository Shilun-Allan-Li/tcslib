<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/BentFunctions.lean :: FABL.exists_inv_card_le_sq_vectorFourierCoeff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A large binary Fourier coefficient

**Claim.** If a real-valued function on $(\mathbb F_2)^n$ has absolute value one everywhere, then some binary Fourier coefficient has square at least $2^{-n}$.

**Proof.** There are $2^n$ vectors indexing the binary Fourier coefficients. Consequently the sum, over all such vectors, of the constant quantity $2^{-n}$ is $1$. Parseval's identity for the vector Fourier coefficients of a sign-valued function says that the sum of their squares is also $1$. If every square were strictly less than $2^{-n}$, their finite sum would be strictly less than $1$, a contradiction. Hence at least one coefficient has square at least $2^{-n}$.

**Key facts.** `FABL.sum_sq_vectorFourierCoeff_eq_one`.
