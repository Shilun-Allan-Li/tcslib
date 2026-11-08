<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.splitBody_round -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One complete split-search round

**Claim.** Under the stated halted source run after $T$ steps, the round body has a positive stopping time bounded by $T+5|s|+3|w|+20$, avoids its anchor at every intermediate positive time, and either halts with the specified pair encoding when $|s|+|out|=|w|$, or returns to the anchor with the candidate advanced exactly when $|s|\le |w|$.

**Proof.** Write $tm$ for the round-body machine and begin with its anchor configuration $z$. Its first transition enters the prepare phase without moving the input head or changing the tapes. The preparation phase reaches the counting phase with a bound of $2(|s|+1)$ and avoids the anchor (`splitBody_prepare`). The counting phase simulates the given source run for at most $T$ steps, preserving the relevant configuration and avoiding the anchor (`splitBody_count`). At its endpoint, the check transition enters the rewind phase; the acceptance flag is true exactly when the output count plus $|s|$ equals $|w|$ (`splitCount_accept`).

The rewind phase reaches input position $1$ and its terminal state within the current input-head position plus $2$, still avoiding the anchor (`splitBody_rewind`). Since the starting position is at most $|w|+1$, this phase costs at most $|w|+3$. The proof joins the phase runs one after another, using `splitSafe_join`; each boundary transition is checked separately with `splitSafe_one`. These bounds account for the preparation, source simulation, check, and rewind portions, with anchor avoidance carried through their concatenation.

If $|s|+|out|=|w|$, the rewind endpoint dispatches to the emit phase. The emit machine outputs the doubled prefix of $w$ of length $|s|$, then $01$, then the remaining suffix, and halts after $|s|+|w|+3$ further steps (`splitEmit_run`). Its run is transported into the round body by agreement of transitions, and it avoids the anchor. Joining this final segment gives a positive total time within the stated bound and the required halted configuration.

Otherwise, the endpoint dispatches to the restoration scan at position $0$. The restoration phase reaches its return configuration, with the candidate changed according to the stated length test, within $2|s|+|w|+5$ steps and avoids the anchor (`splitBody_restore`). One final transition returns to the anchor configuration with the updated candidate. The claimed intermediate-time avoidance follows from the joined phase safety statements, and the added phase bounds give the stated overall upper bound.

**Key facts.** `Turing.FinTM.splitBody_prepare`, `Turing.FinTM.splitBody_count`, `Turing.FinTM.splitCount_accept`, `Turing.FinTM.splitBody_rewind`, `Turing.FinTM.splitSafe_join`, `Turing.FinTM.splitSafe_one`, `Turing.FinTM.splitEmit_run`, `Turing.FinTM.splitBody_restore`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
