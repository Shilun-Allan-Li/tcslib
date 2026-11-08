<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Coins.lean :: Randomized.rhoCoinRun_isPrefixStable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prefix Stability of the Coin Run

**Claim.** For every infinite bit sequence, if the coin-run procedure returns a bit on a finite string, then it returns the same bit on every extension of that string.

**Proof.** Induct on the finite string, allowing the bit sequence to vary. For the empty string, the procedure returns no bit, so the premise that it returns a bit is impossible. For a string beginning with $b$, compare $b$ with the first bit $p(0)$. If they agree, the procedure continues on the tail using the shifted sequence $i\mapsto p(i+1)$. The hypothesis that the original string returns a bit therefore gives the induction hypothesis for its tail; applying it to the extension yields the same result after the common first bit. If $b\ne p(0)$, the procedure immediately returns $p(0)$, regardless of the remaining string. Prefixing the extension by the same $b$ leaves that first disagreement unchanged, so the result is still $p(0)$.
