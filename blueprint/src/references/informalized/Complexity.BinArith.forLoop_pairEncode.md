<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Loops.lean :: Complexity.BinArith.forLoop_pairEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# For-Loop Iteration on an Encoded Pair

**Claim.** Starting from the encoding of $c,d$, the for-loop transformation iterated $|\langle c,d\rangle|+1$ times yields the encoding of the empty string and $f^{|c|}(d)$.

**Proof.** The iteration formula for the for-step (`iterate_forStep`) says that after $i$ steps the state is the encoding of $c$ with its first $i$ bits removed, paired with $f^{\min(i,|c|)}(d)$. The loop uses $|\langle c,d\rangle|+1$ steps. The encoding length formula (`length_pairEncode`) shows this number exceeds $|c|$, so the remaining first component is empty and the minimum in the iterate exponent is $|c|$. Substituting these into the iteration formula gives the stated encoding.

**Key facts.** `Complexity.BinArith.iterate_forStep`, `Turing.length_pairEncode`.
