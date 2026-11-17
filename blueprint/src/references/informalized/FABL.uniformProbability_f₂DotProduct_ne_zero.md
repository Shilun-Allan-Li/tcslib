<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.uniformProbability_f₂DotProduct_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonzero Binary Dot Product Probability

**Claim.** For $\gamma\in\mathbb F_2^n$, the uniform probability that its dot product with a uniform vector is nonzero is $0$ when $\gamma=0$ and $1/2$ otherwise.

**Proof.** First compute the probability that the dot product is zero. Its indicator equals half of one plus the binary sign of the dot product (\texttt{f\u2082ZeroIndicator\_eq}); the sign is the vector Walsh character (\texttt{vectorWalshCharacter\_apply}). The mean of this character over the cube is $1$ for the zero vector $\gamma$ and $0$ otherwise (\texttt{expect\_vectorWalshCharacter}). Hence the probability of a zero dot product is $(1+1)/2=1$ if $\gamma=0$, and $(1+0)/2=1/2$ otherwise. Since the nonzero and zero events are complements, their probabilities sum to $1$. Subtracting the zero probability gives $0$ in the first case and $1/2$ in the second.

**Key facts.** `FABL.vectorWalshCharacter_apply`, `FABL.f₂ZeroIndicator_eq`, `FABL.expect_vectorWalshCharacter`.
