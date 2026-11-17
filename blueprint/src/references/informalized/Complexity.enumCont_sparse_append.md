<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_sparse_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Appending a Sparse Tape Cell

**Claim.** Representing the list formed by appending optional symbol $b$ to $w$ gives the same tape function as representing $w$ and updating position $|w|$ to $b$.

**Proof.** Compare the two tape functions at an integer position $z$. At the position $z=|w|$, the appended list has value $b$, and the update assigns exactly that value. At any other position, the update leaves the original tape value unchanged. If $z$ is negative, both list representations give blank. If $z$ is nonnegative, its natural-number index either lies within $w$, where appending does not change the indexed entry, or lies beyond the appended list, where both values are blank. Thus the functions agree at every position.
