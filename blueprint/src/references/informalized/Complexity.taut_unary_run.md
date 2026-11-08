<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.taut_unary_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary Index Run

**Claim.** For a paired encoding whose first word begins with $k$ ones, the verifier’s unary-index evaluation state with accumulator $c$ consumes the $2k$ paired bits, keeps the work tape unchanged, and advances its work head from $h$ to $h+k$.

**Proof.** Induct on $k$. At $k=0$, no steps are taken, so the configuration is unchanged. For $k+1$, separate the first pair $11$ from the remaining encoding. The two-bit evaluation lemma processes that pair in the unary state, preserves the tape and accumulator, and advances the work head by one. Split the run into these two steps and the remaining $2k$ steps. Apply the induction hypothesis to the remaining $k$ unary pairs, with the extended prefix and head position $h+1$. The total head displacement is $1+k$, and the paired-encoding length identity ensures the positions are valid.

**Key facts.** `Complexity.taut_eval_double`, `Turing.MultiTapeTM.runFrom_add`, `Turing.universal_pair_length`.
