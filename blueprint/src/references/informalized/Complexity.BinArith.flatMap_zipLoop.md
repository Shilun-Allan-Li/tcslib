<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Words.lean :: Complexity.BinArith.flatMap_zipLoop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Flattening Paired Decoding Rounds

**Claim.** For the stated bound $|l_1|\le N$, concatenating the contributions from the first $N$ paired decoding rounds equals the flattened list obtained by applying $c$ to corresponding entries of the recursively decoded-word lists, stopping when either list ends.

**Proof.** Induct on $N$. At $N=0$, the bound forces $l_1$ to be empty, and both sides are empty. In the successor step, separate the round-zero contribution; the remaining rounds are the same construction starting from the two total second projections. The second projection of $l_1$ has length at most $N$: if $l_1$ is empty this is immediate, and otherwise its length strictly decreases (`length_pairSndD_lt`). Apply induction to the two second projections. If either original string is empty, its second projection is empty, so the later-round contribution and the paired decoded-word list both stop. If both are nonempty, the first decoded word of each is its total first projection, followed by the decoded words of its second projection (`decWords_of_ne`). The round-zero contribution followed by the induction result is therefore exactly the flattened paired list.

**Key facts.** `Complexity.BinArith.length_pairSndD_lt`, `Complexity.BinArith.decWords_of_ne`.
