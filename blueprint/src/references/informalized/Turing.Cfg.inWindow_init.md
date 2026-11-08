<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.Cfg.inWindow_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Configuration Lies in the Window

**Claim.** In the initial configuration on $x$ with starting state $q_0$, every work-tape head is at a position of absolute value at most $s$, and every work-tape cell at a position $z$ with $|z|>s$ is blank.

**Proof.** In the initial configuration every work-tape head is at position $0$, and every work-tape cell contains no symbol. Since $s$ is nonnegative, $|0|=0\le s$, giving the head-position bound. The blank-cell condition holds at every integer position, hence in particular whenever $|z|>s$.
