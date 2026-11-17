<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Words.lean :: Complexity.BinArith.flatMap_listLoop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Iterated Decoding and Concatenation

**Claim.** For any output function $c$, any bit string $w$, and any $N\ge |w|$, concatenating the specified outputs from the first $N$ iterated second projections gives the concatenation of $c$ applied to the recursively decoded words of $w$.

**Proof.** Induct on $N$. When $N=0$, the length bound forces $w$ to be empty, so both concatenations are empty. For the step from $N$ to $N+1$, separate the contribution at iteration zero from the contributions at iterations $1$ through $N$. Those later terms are exactly the same construction starting from the total second projection of $w$. If $w$ is empty, its second projection is empty and its decoded-word list is empty, so both sides vanish by the induction hypothesis. If $w$ is nonempty, its second projection has strictly smaller length (the second-projection length bound, `length_pairSndD_lt`), and hence length at most $N$. Apply induction to that projection. The iteration-zero contribution is $c$ of the first projection, and the recursive decoded-word list begins with that first projection followed by the decoded words of the second projection (`decWords_of_ne`). Concatenating these pieces gives the asserted equality.

**Key facts.** `Complexity.BinArith.length_pairSndD_lt`, `Complexity.BinArith.decWords_of_ne`.
