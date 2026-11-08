<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Coins.lean :: Randomized.vonNeumann_heads_eq_tails -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equal probabilities of either returned bit

**Claim.** For any real $\rho$ and natural number $K$, the pair rule returns true and false with equal probabilities on $2K$ independent bits.

**Proof.** The established formula for returning true (`Randomized.vonNeumann_heads`) gives probability $\bigl(1-(\rho^2+(1-\rho)^2)^K\bigr)/2$. The corresponding formula for returning false (`Randomized.vonNeumann_tails`) gives the same expression. Therefore the two probabilities are equal.

**Key facts.** `Randomized.vonNeumann_heads`, `Randomized.vonNeumann_tails`.
