<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Coins.lean :: Randomized.biasedProb_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-Step Biased Probability Expansion

**Claim.** For every natural number $K$ and predicate $A$, biased probability on strings of length $2(K+1)$ expands over the four possible first two bits, with the corresponding products of their true and false weights, and the remaining probabilities taken on strings of length $2K$.

**Proof.** Rewrite the length as $2K+1+1$. Unfold the recursive definition twice: first split according to the first bit, then split each resulting branch according to the second bit. The four branches are precisely the prefixes true-true, true-false, false-true, and false-false, with weights respectively $\rho^2$, $\rho(1-\rho)$, $(1-\rho)\rho$, and $(1-\rho)^2$, grouped as in the claimed expression.
