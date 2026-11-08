<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.binDigits_posWidth_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Digits at Positive Width

**Claim.** For every natural number $n$, the bits of $n+1$ listed at positions below the length of its binary expansion are exactly the binary digit list of $n+1$.

**Proof.** The two lists have the same length by the definition of the chosen width. To identify them, compare entries at any position $j$ within that length. The entry of the constructed list is the $j$th test bit of $n+1$. The theorem identifying natural-number test bits with entries of the binary digit list, together with the agreement between list indexing and integer indexing at an in-range position, shows that this is the $j$th entry of the digit list. Equal lengths and equal entries at every valid position give equality of the lists.
