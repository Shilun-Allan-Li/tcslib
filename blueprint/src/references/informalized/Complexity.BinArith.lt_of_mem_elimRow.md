<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/DetMod.lean :: Complexity.BinArith.lt_of_mem_elimRow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Range of Eliminated Row Entries

**Claim.** For positive $p$, every entry produced by eliminating the first row entry from the paired tails of $row$ and $piv$ is less than $p$.

**Proof.** By definition, the eliminated row is a `zipWith` list whose combining function returns a remainder modulo $p$. The general range result for zipped lists (`Complexity.BinArith.lt_of_mem_zipWith`) says that every entry is below $p$ whenever the combining function has that bound on every pair. Here the function's output is a natural-number remainder modulo the positive number $p$, so it is strictly less than $p$. Applying the result to the two tails gives the claim.

**Key facts.** `Complexity.BinArith.lt_of_mem_zipWith`.
