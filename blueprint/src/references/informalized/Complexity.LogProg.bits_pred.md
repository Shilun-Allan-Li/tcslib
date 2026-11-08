<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/FragDec.lean :: Complexity.LogProg.bits_pred -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Expansion of a Predecessor

**Claim.** For every natural number $n$, the bit list of $n-1$, with subtraction truncated at zero, is obtained by changing each initial $0$ to $1$ until the first $1$, then deleting that $1$; if the list consists only of that $1$, the result is empty.

**Proof.** When $n=0$, both the bit list of the truncated predecessor and the result of the stated word operation are empty. For $n>0$, write $n=k+1$, so its truncated predecessor is $k$. The successor rule for binary expansion (`bits_succ`) identifies the bits of $k+1$ with the word obtained by incrementing the bits of $k`. Binary expansions are canonical in the sense that every nonempty such word ends in $1$ (`canon_bits`). On canonical words, decrementing the incremented word recovers the original word (`decW_incW`). Applying this identity to the bits of $k$ gives the claimed description.

**Key facts.** `Complexity.LogProg.bits_succ`, `Complexity.LogProg.canon_bits`, `Complexity.LogProg.decW_incW`.
