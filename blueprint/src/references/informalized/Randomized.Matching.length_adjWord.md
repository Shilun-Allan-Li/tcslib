<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Matching.lean :: Randomized.Matching.length_adjWord -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the Adjacency Word

**Claim.** The row-by-row list of entries of an $n\times n$ Boolean matrix has length $n^2$.

**Proof.** There are $n$ rows, and mapping across each row produces a list of length $n$. Flattening the mapped rows therefore has total length $n$ times $n$, namely $n^2$.
