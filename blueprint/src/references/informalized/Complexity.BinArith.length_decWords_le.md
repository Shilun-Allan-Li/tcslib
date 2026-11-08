<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Words.lean :: Complexity.BinArith.length_decWords_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length Bound for Recursive Decomposition

**Claim.** The recursively formed list of parsed components has length at most the length of the starting bit string.

**Proof.** If $w$ is empty, its decomposition is empty, so the bound is immediate. Otherwise, the recursive definition gives a list whose first entry is the defaulted first parsed component and whose tail is the decomposition of the defaulted second parsed component (`Complexity.BinArith.decWords_of_ne`). The second parsed component is strictly shorter than $w$ (`Complexity.BinArith.length_pairSndD_lt`), so the recursive bound applies to it. The resulting length is one plus the length of that recursive tail, and the strict decrease makes this at most $|w|$.

**Key facts.** `Complexity.BinArith.decWords_of_ne`, `Complexity.BinArith.length_pairSndD_lt`.
