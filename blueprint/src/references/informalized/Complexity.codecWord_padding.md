<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecWord_padding -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# False Padding in the Boolean Code

**Claim.** For finite $\alpha$, every natural number $L$, and every $j\ge |\alpha|$, the encoded list entry at position $j$, read with false as the default beyond the list, is false.

**Proof.** Separate whether $j<L$. If $j<L$, the encoding contains an entry there, but because $j\ge |\alpha|$, this index is outside the portion assigned to elements of $\alpha$; the definition therefore places false at that position. If $j\ge L$, the requested position is beyond the encoded list, whose default value is false. In either case the read value is false.
