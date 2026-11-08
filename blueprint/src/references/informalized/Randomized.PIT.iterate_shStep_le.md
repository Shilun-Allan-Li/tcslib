<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPReduce.lean :: Randomized.PIT.iterate_shStep_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length bound for gate-shifting iterations

**Claim.** After $i$ iterations from the encoded state containing $M$, $w$, and an empty output, the state still encodes $M$ together with some strings $w'$ and $out'$, and their total length is at most $|w|+i(2|M|+8)$.

**Proof.** Induct on $i$. At zero, take $w'=w$ and the empty output. For a successor, apply the induction hypothesis to obtain an encoded state with the fixed first component $M$ and data $w',out'$. The one-step length estimate says either the state is unchanged, or it encodes new data whose combined length is at most $|w'|+|out'|+2|M|+8$ (`shStep_pair`). In the unchanged case the previous bound suffices; in the other case add this per-step increase to the induction bound. In either case, the result is at most $|w|+(i+1)(2|M|+8)$.

**Key facts.** `Randomized.PIT.shStep_pair`.
