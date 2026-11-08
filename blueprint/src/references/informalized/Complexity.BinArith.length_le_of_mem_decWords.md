<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Words.lean :: Complexity.BinArith.length_le_of_mem_decWords -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length bound for decoded words

**Claim.** Every word produced in the recursive list of decoded words from $w$ has length at most $|w|$.

**Proof.** Proceed by induction on the list membership derivation, splitting on whether $w$ is empty. If $w$ is empty, the decoded-word list is empty, so there is no member to consider. If $w$ is nonempty, the list consists of its total first projection followed by the decoded words of its total second projection (`Complexity.BinArith.decWords_of_ne`). A member is therefore either the first projection, whose length is at most $|w|$ (`Complexity.length_pairFstD_le`), or a member decoded from the second projection. In the latter case, induction bounds its length by the length of that second projection, and strict decrease of that length for nonempty $w$ (`Complexity.BinArith.length_pairSndD_lt`) finishes the estimate.

**Key facts.** `Complexity.BinArith.decWords_of_ne`, `Complexity.length_pairFstD_le`, `Complexity.BinArith.length_pairSndD_lt`.
