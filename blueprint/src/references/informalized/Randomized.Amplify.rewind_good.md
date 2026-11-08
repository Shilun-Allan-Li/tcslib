<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyRun.lean :: Randomized.Amplify.rewind_good -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Space Bound During Rewind

**Claim.** If every run of $N$ from its initial configuration uses at most $S$ work-tape cells, then from a rewind configuration at $(j,c)$ with the later blocks fresh and all heads within distance $S$ of zero, every continuation of the amplified machine keeps all work-tape heads within distance $S$ of zero.

**Proof.** Induct on the number $i$ of runs still to be processed, where $j+i=r$. If $i=0$, then $j=r$: the rewind is at the last run. The last-rewind behavior (`rewind_last`) says that either next choice leads to the same finishing configuration, so any continuation preserves the head positions of $C$; the empty continuation does as well. The assumed bound on those positions therefore proves the claim.

For the induction step, $j<r$. The rewind behavior (`rewind_run`) provides a duration $p+2$ for the rewind and seek phase: up to that time the work-head positions are unchanged, and at exactly that duration the configuration is a restart at run $j+1$. If the choice word is no longer than this duration, the position-preservation clause immediately transfers the original bound. Otherwise, split the word after its first $p+2$ bits, using the list decomposition and run concatenation law (`runWith_append`). The prefix reaches the restart configuration. The restart identity (`restart_eq_emb`) identifies that configuration with the embedding of $N$’s initial configuration into block $j+1$.

For the remaining suffix, use the reachability composition principle (`reach_comp`) with the predicate that every work-head position has absolute value at most $S$. At every simulated configuration, the bound follows from the space hypothesis for $N$ and the embedding bound (`good_emb`). When such a simulated run halts, its embedding is a rewind configuration at $j+1$ with all later blocks still fresh (`rewindAt_emb`); the same embedding bound supplies the position bound at that point. The induction hypothesis applies there, since $(j+1)+i=r$. Thus the entire suffix preserves the bound, completing the induction.

**Key facts.** `Randomized.Amplify.rewind_last`, `Randomized.Amplify.rewind_run`, `Turing.NDTM.runWith_append`, `Randomized.Amplify.restart_eq_emb`, `Randomized.Amplify.good_emb`, `Randomized.Amplify.reach_comp`, `Randomized.Amplify.rewindAt_emb`, `Randomized.Amplify.step_emb`.
