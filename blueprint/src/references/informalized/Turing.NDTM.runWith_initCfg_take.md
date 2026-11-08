<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Nondeterministic.lean :: Turing.NDTM.runWith_initCfg_take -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Runs on Truncated Inputs

**Claim.** If the choice word has length at most $m$, then the run from the initial configuration on $x$ agrees in state, input-head position, work tapes, work-tape head positions, and output with the run on the prefix of $x$ of length $m$.

**Proof.** Apply the agreement theorem for runs on truncated inputs (`Turing.NDTM.runWith_take_agree`) to the two initial configurations. They agree initially in state, work-tape contents, work-tape head positions, and output by their definitions; their input-head positions are both $1$. The theorem's length condition also holds: the initial head position is $1$, so $1+|w|\le m+1$ follows from $|w|\le m$. The theorem therefore gives equality of all five listed components after the run.

**Key facts.** `Turing.NDTM.runWith_take_agree`.
