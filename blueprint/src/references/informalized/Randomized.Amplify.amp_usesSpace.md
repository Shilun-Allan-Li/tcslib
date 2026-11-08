<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyRun.lean :: Randomized.Amplify.amp_usesSpace -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Space Bound for the Amplified Machine

**Claim.** If $s(|x|)$ bounds the space used by $N$ on every input $x$ and every choice word, then the amplified machine uses at most $(r+1)k(2s(|x|)+1)$ space on every input $x$ and choice word.

**Proof.** Put $S=s(|x|)$. First show that every configuration reached by the amplified machine has each work-tape head within distance $S$ of the origin. The initial configuration embeds the original initial configuration (`init_eq_emb`). Along each simulated original run, the space hypothesis and `good_emb` preserve the bound represented by the predicate $\mathrm{Good}(S)$. The embedded simulation advances correctly one step at a time (`step_emb`); after an original run halts, `rewind_good` preserves the same bound through the rewind and subsequent phases. Freshness of the initial configuration (`fresh_init`) and the rewind-state characterization (`rewindAt_emb`) provide the conditions for these simulation and rewind results. The reachability composition result (`reach_comp`) therefore gives $\mathrm{Good}(S)$ for every prefix of every amplified run, hence each head position lies between $-S$ and $S$. The general space estimate from head-position ranges (`spaceUsedWith_le_of_ranges`) now bounds the visited cells on each of the $(r+1)k$ tapes by the number of integer positions in this interval, $2S+1$. Summing over the tapes gives $(r+1)k(2S+1)$, as required.

**Key facts.** `Randomized.Amplify.init_eq_emb`, `Randomized.Amplify.good_emb`, `Randomized.Amplify.step_emb`, `Randomized.Amplify.fresh_init`, `Randomized.Amplify.rewindAt_emb`, `Randomized.Amplify.rewind_good`, `Randomized.Amplify.reach_comp`, `Complexity.LogProg.spaceUsedWith_le_of_ranges`.
