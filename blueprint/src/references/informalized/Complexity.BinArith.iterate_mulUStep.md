<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Loops.lean :: Complexity.BinArith.iterate_mulUStep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Iteration of the multiplication step

**Claim.** Applying the multiplication step $j$ times to $\langle b,\mathrm{acc}\rangle$ gives the pair encoding of $b$ and $\mathrm{acc}$ concatenated with $j$ copies of $b$.

**Proof.** Induct on $j$. At zero, the accumulator is followed by no copies, so the claim is the original encoding. For the successor step, the induction hypothesis says the accumulator is followed by the current list of copies of $b$. One more multiplication step appends $b$ to that accumulator while retaining the first component. Concatenation therefore gives the accumulator followed by one additional copy, which is precisely the list of $j+1$ copies.
