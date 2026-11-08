<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Loops.lean :: Complexity.BinArith.length_uRest_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output length bound

**Claim.** For every finite bit string $w$, the output of the specified left-to-right process, starting in state false, has length at most $|w|$.

**Proof.** Proceed by induction on the input string. The empty string produces no output. For input $b::w$, split on $b$. If $b$ is false, the initial state is false and the process emits nothing at that step; the resulting tail output is bounded by the induction hypothesis. If $b$ is true, the output is the tail output unchanged, by the characterization of the process on a true initial bit (`uRest_true_cons`). Its length is at most $|w|$, and therefore at most $1+|w|$, the length of the whole input.

**Key facts.** `Complexity.BinArith.uRest_true_cons`.
