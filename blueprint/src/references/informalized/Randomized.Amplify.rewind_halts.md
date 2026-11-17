<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyRun.lean :: Randomized.Amplify.rewind_halts -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting During Rewind

**Claim.** Under the assumption that every length-$T$ choice word halts $N$ on $x$, every length-$i(T+|x|+2)+1$ choice word halts the amplified machine from a rewind configuration at $(j,c)$ satisfying the stated freshness and empty-output conditions, whenever $j+i=r$.

**Proof.** Proceed by induction on $i$. If $i=0$, the relation $j+i=r$ puts the machine at the final run index. The first choice therefore finishes the rewind and halts, independently of that choice; once halted, any remaining choices leave the configuration unchanged. For the induction step, $j<r$. The rewind first takes at most $|x|+2$ steps to return to the left end of the input and restart at index $j+1$ with counter $c$. Freshness ensures that the restarted run is an embedding of $N$’s initial configuration (`restart_eq_emb`). By the halting hypothesis, the next $T$ choices halt that simulated run; the result is a rewind configuration for index $j+1$. The induction hypothesis applies there, since $(j+1)+i=r$, and supplies halting for the remaining $i(T+|x|+2)+1$ choices. Splitting the choice word after the rewind segment and then using the induction bound gives the claimed total length. The fact that halting persists when a word is extended (`halted_of_le`) handles any unused choices in the rewind bound.

**Key facts.** `Randomized.Amplify.rewind_last`, `Randomized.Amplify.rewind_run`, `Randomized.Amplify.restart_eq_emb`, `Randomized.Amplify.run_halts`, `Turing.NDTM.runWith_append`, `Randomized.Amplify.halted_of_le`.
