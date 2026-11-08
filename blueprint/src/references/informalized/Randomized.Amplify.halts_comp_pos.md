<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplify.lean :: Randomized.Amplify.halts_comp_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting Composition with a Position Bound

**Claim.** With the stated step agreement and position-bounded halting condition for images of halting configurations, if the input-head position of $c$ plus $n$ is at most $B$ and every length-$n$ run of $N$ from $c$ halts, then every length-$(n+m)$ run of $M$ from $\varphi(c)$ halts.

**Proof.** Proceed by induction on $n$. When $n=0$, the empty choice word shows that $c$ is already halting. The position condition gives $c$’s input-head position at most $B$, so the assumed length-$m$ halting property applies directly to the whole word of length $m$.

For the successor case, first consider a starting configuration that is already halting. Take the first $m$ choices of the given word; enough choices are available because its length is $n+1+m$. The length-$m$ halting condition applies, since the position bound at the start follows from the stronger bound involving $n+1$. By the append law for runs and the fact that further choices leave a halting configuration unchanged (`runWith_append` and `runWith_of_halt`), the entire run halts.

Otherwise, write the word as its first bit followed by a suffix. After that first step, the input-head position has increased by at most one (`inputPos_stepWith_le`), so the new position plus $n$ remains at most $B$. The suffix has length $n+m$; the induction hypothesis applies from the next configuration, using step agreement to identify its image with the result of the first step of $M$. The length-$n$ halting premise for $N$ at that next configuration follows by prepending the first bit to any length-$n$ word. Hence the run of $M$ on the full word halts.

**Key facts.** `Randomized.Amplify.inputPos_stepWith_le`, `Turing.NDTM.runWith_append`, `Turing.NDTM.runWith_of_halt`, `Turing.NDTM.runWith_cons`.
