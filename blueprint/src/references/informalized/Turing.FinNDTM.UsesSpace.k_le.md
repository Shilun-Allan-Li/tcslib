<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Space.lean :: Turing.FinNDTM.UsesSpace.k_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work tape count bounded by space

**Claim.** If every input and choice word uses at most $s(|x|)$ work tape cells in total, then the machine's number $k$ of work tapes satisfies $k\le s(n)$ for every $n$.

**Proof.** Fix $n$ and apply the space bound to the input consisting of $n$ false bits and to the empty choice word. Along this run, the only visited position on each work tape is its initial head position, $0$. Thus each of the $k$ tapes contributes one visited cell, and the total space used is $k$. The assumed bound for this input, whose length is $n$, therefore gives $k\le s(n)$.
