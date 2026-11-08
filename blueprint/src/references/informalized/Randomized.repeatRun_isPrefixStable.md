<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ExpectedTime.lean :: Randomized.repeatRun_isPrefixStable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prefix Stability of Repeated Runs

**Claim.** If the repeated-run procedure returns a value on a bit string $w$, then it returns the same value on every extension of $w$.

**Proof.** Use strong induction on the length of $w$, with the string itself generalized. Suppose first that $w$ contains a complete block and that the block length $t$ is positive. The procedure decomposes into the left-biased choice between the result on the first block and the recursive run on the suffix (`repeatRun_of_le`). The extension $w\mathbin{++}v$ has the same first block, and its suffix after that block is the original suffix extended by $v$. If the first block already returns a value, the original run’s result is that value, and the extended run returns it as well. If the first block returns no value, the original result comes from the recursive run on the suffix; the induction hypothesis applies because dropping the complete block strictly shortens the string. It then shows that the recursive run on the extended suffix returns the same value, and hence so does the whole extended run. In the other case, the condition for a complete block fails. The definition then makes the run return no value, contradicting the assumed successful result. This proves prefix stability.

**Key facts.** `Randomized.repeatRun_of_le`.
