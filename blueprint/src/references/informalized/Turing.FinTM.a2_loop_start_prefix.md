<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.a2_loop_start_prefix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded heads during loop startup

**Claim.** Under the stated guard, endpoint, space, and fuel-head hypotheses, the loop-host heads stay within radius $B+2$ throughout the first $t+2$ steps from the ready configuration.

**Proof.** Rewrite the ready configuration as a loop call on the body's initial configuration, with startup enabled (`f2_loopReady_call`). Since the body is not halted at time $t$—its endpoint is the seam configuration—the live-prefix lemma shows that it remains live at every earlier time. The guard hypothesis says that the body does not visit the anchor during this prefix, so the call-prefix head bound applies. It bounds the host heads through time $t$ by radius $B$ (`a2_call_prefix`); the endpoint output has length zero, as follows from its being the specified seam configuration.

For the two steps after time $t$, each head can move by at most one per step, so the radius increases by at most two (`a2_heads_steps`). The head-bound monotonicity lemma allows the prefix bound to be enlarged to $B+2$ (`a2_heads_mono`), and `a2_heads_join` combines the prefix with the two-step continuation.

**Key facts.** `Turing.FinTM.f2_loopReady_call`, `Turing.FinTM.f2_loop_live_prefix`, `Turing.FinTM.a2_call_prefix`, `Turing.FinTM.a2_heads_steps`, `Turing.FinTM.a2_heads_mono`, `Turing.FinTM.a2_heads_join`.
