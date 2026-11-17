<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZPPHosts.lean :: Randomized.clockHost_abortDecides -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clocked Abort Decision

**Claim.** Under the stated runtime, correctness, and success-probability hypotheses, the clocked host with looping disabled halts within the given bound on every witness, never outputs an incorrect membership bit, and outputs the correct bit with probability at least $1/2$.

**Proof.** Fix an input $x$ and let $m=m(|x|)$. The startup lemma (`Turing.ClockHost.startup`) shows that after at most $T_S(|x|)+m+2$ nondeterministic bits, the host has prepared the simulation of the attempt machine. The next $m+1$ bits include the $m$-bit witness used by the attempt; the one-shot simulation lemma (`Turing.ClockHost.oneShot`) shows that the host halts then and its single-bit output agrees with the attempt's output. This gives a uniform halting bound of $T_S(|x|)+m+2+(m+1)$, and extending the available witness length preserves halting (`Turing.NDTM.HaltsWithin.mono`).

Any output bit from an attempt on a length-$m$ witness is correct by hypothesis. The correspondence between a successful attempt and a halted single-bit output (`Randomized.attemptBit_eq_some`) therefore rules out an incorrect bit from the host; extra witness bits do not change a run that has already halted (`Turing.FinNDTM.runWith_eq_runWith_take`). Finally, split a uniformly random host witness into its startup portion and the attempt portion. The random-probability product and truncation identities (`Randomized.randProb_split`, `Randomized.randProb_take`), together with the fact that an unconstrained startup portion has probability one (`Randomized.randProb_true`), reduce the probability of the correct host output to the probability that a uniform length-$m$ attempt yields the correct bit. The assumed lower bound gives at least $1/2$.

**Key facts.** `Turing.ClockHost.startup`, `Turing.ClockHost.oneShot`, `Turing.NDTM.HaltsWithin.mono`, `Randomized.attemptBit_eq_some`, `Turing.FinNDTM.runWith_eq_runWith_take`, `Turing.FinNDTM.outputProb_eq_of_haltsWithin`, `Randomized.randProb_congr`, `Randomized.randProb_split`, `Randomized.randProb_true`, `Randomized.randProb_take`.
