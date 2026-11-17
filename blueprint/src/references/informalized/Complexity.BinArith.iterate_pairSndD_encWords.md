<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Loops.lean :: Complexity.BinArith.iterate_pairSndD_encWords -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Projection iteration on encoded words

**Claim.** Applying the total second projection $j$ times to the concatenation of the encodings $\langle w,[]\rangle$ for $w$ in a finite list $L$ gives the corresponding concatenation for the list obtained by removing the first $j$ entries of $L$.

**Proof.** Induct on $j$, generalizing over the list $L$. At zero, both sides are the original concatenation. For the successor step, apply the projection once and split on whether $L$ is empty. If it is empty, the projection iterations on the empty word remain empty by the empty-word iteration result (\(\texttt{Complexity.BinArith.iterate\_pairSndD\_nil}\)). If $L$ begins with a word $w$, the first projection removes that initial encoded word; applying the induction hypothesis to the remaining list removes its first $j$ entries. Together these remove the first $j+1$ entries of $L$, yielding the stated encoding.

**Key facts.** `Complexity.BinArith.iterate_pairSndD_nil`.
