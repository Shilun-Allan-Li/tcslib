<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardSemantics.lean :: Complexity.TQBFHard.length_readBlock -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of a read block

**Claim.** For a bit sequence $\tau$ and natural numbers $i,w$, the block of $w$ bits beginning at $i$ has length $w$.

**Proof.** The block is formed by assigning one bit to each element of the finite index set of size $w$. A list enumerating that finite index set has exactly $w$ entries, so the block has length $w.
