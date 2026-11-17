<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clLoadWords_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Next Loaded Coordinate

**Claim.** Replacing coordinate $i$ in the mixed bank—new words below $i$, old words elsewhere—with its new word gives the bank with new words below $i+1$ and old words elsewhere.

**Proof.** Compare the two banks at each coordinate $j$. If $j=i$, the update assigns the new word at $i$, and the condition $j<i+1$ also selects the new word there. If $j\ne i$, the update leaves the existing value unchanged. In this case, whether $j<i$ agrees with whether $j<i+1$, since the only natural number between these thresholds is $i$ itself. Thus both banks agree at every coordinate.
