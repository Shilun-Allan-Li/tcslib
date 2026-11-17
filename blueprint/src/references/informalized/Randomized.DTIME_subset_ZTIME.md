<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ExpectedTime.lean :: Randomized.DTIME_subset_ZTIME -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Deterministic Time Within Zero-Error Time

**Claim.** For every time bound $T$, every language decidable by a finite deterministic machine within a constant multiple of $T$ also has a zero-error randomized decider with expected-time bound within that same constant multiple of $T$.

**Proof.** Take a deterministic decider $M$ witnessing membership in $	ext{DTIME}(T)$, with constant $c$. Regard $M$ as a nondeterministic machine that ignores its random bits. Its run on any bit string of random choices $w$ agrees with the deterministic run after $|w|$ steps (the simulation identity `MultiTapeTM.toNDTM_runWith`). The deterministic time bound supplies a halting run within $cT(|x|)$ steps, and the deterministic computation specification says its output is the indicator of membership in the language (`FinTM.computesInTime_iff`). Since the randomized simulation halts within that bound for every choice of random bits, its expected-time bound follows from the fact that a machine halting within a fixed time bound has expected time at most that bound (`FinNDTM.expTimeLe_of_haltsWithin`). Finally, the output of the deterministic machine is unchanged after it halts: if the random-bit string is shorter than the time bound, compare its output at its own halting time; if it is longer, compare the output at the time bound. In either case the halted-run output invariance (`MultiTapeTM.runFrom_output_eq_of_halt`) shows that the result is the correct membership indicator. Thus this machine witnesses membership in $	ext{ZTIME}(T)$ with constant $c$.

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.toNDTM_runWith`, `Turing.FinNDTM.expTimeLe_of_haltsWithin`, `Turing.MultiTapeTM.runFrom_output_eq_of_halt`.
