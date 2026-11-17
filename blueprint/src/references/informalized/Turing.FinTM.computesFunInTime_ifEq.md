<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Composition.lean :: Turing.FinTM.computesFunInTime_ifEq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fixed-Word Equality Test

**Claim.** For fixed Boolean words $w_0,u,v$, a finite Turing machine outputs $u$ exactly on input $w_0$ and outputs $v$ on every other input, in time bounded by a constant multiple of the input length plus one.

**Proof.** Choose the machine that tests whether the input agrees with $w_0$, and take $c=|w_0|+\max(|u|,|v|)+3$. The run lemma `ifEq_run`, applied at the initial comparison state with no symbols yet read, gives a halting run whose output is the required conditional output and whose length is at most $|w_0|+\max(|u|,|v|)+2$. This bound is at most $c(|x|+1)$ for every input $x$. The time monotonicity property `ComputesInTime.mono` extends the run to that prescribed time; the run lemma supplies halting and output, and the space witness is existential in the definition of computation in time.

**Key facts.** `Turing.FinTM.ifEq_run`, `Turing.FinTM.ComputesInTime.mono`.
