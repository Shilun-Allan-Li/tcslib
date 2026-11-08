<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_sparse_blanks -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sparse Tape of Blank Cells

**Claim.** A list consisting of $n$ blank entries represents the everywhere-blank tape for every natural number $n$.

**Proof.** Compare the represented tape with the everywhere-blank function at an integer position $z$. If $z$ is negative, the sparse-tape definition returns blank immediately. If $z$ is nonnegative, its list index is either below $n$, in which case the selected entry is blank, or at least $n$, in which case the list lookup is absent and hence also blank. Therefore the represented tape is blank at every position.
