<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHostRun.lean :: Turing.ClockHost.readyAt_initCfg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Configuration Is Ready

**Claim.** The initial configuration of $A$ is ready at yard length $m$: it starts in $A$'s initial state with input-head position $1$ and empty output, and all cells at or to the left of each work-tape head minus $m$ are blank.

**Proof.** By definition, the initial configuration has state $A$'s initial state, input-head position $1$, blank work tapes, work-head positions $0$, and empty output. Thus the first three readiness conditions hold by equality. For any work tape and cell $z$ with $0-m\le z$, its content is blank because every cell of an initial work tape is blank.
