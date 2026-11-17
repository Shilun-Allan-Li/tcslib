<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardBridge.lean :: Complexity.TQBFHard.ofFn_drop_take -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restriction of a Boolean Sequence

**Claim.** If $i+k\le M$, dropping the first $i$ entries from the length-$M$ list of values of $\tau$ and then taking $k$ entries gives $(\tau(i),\ldots,\tau(i+k-1))$.

**Proof.** Both lists have length $k$: dropping $i$ entries from a list of length $M$ leaves length $M-i$, and taking $k$ entries therefore has length $k$ under $i+k\le M$; the right-hand list has length $k$ by `length_readBlock`. At each position $j<k$, the entry after dropping and taking is the original entry at position $i+j$, namely $\tau(i+j)$. The length and entrywise agreement establish equality of the lists.

**Key facts.** `Complexity.TQBFHard.length_readBlock`.
