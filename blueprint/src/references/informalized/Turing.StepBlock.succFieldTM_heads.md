<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.succFieldTM_heads -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Head Positions During Successor-Field Processing

**Claim.** At each time up to the length of the optional-state encoding, the input-head position and output remain unchanged, while the source head advances by the elapsed time, the destination head advances by one fewer step when copying is enabled, and every other head remains fixed.

**Proof.** Use the intermediate-time description of the run (`succFieldTM_trace`). For positive time it expresses the configuration as the post-tag configuration followed by a unary scan of the first `t-1` symbols; the post-tag transition has already advanced the source head once. In the scan, each step advances the source head and, when copying is enabled, the destination head together with it. Thus the total source displacement is `t`, and the destination displacement is `t-1` when copying is enabled; all other heads receive no movement. The post-tag and scanning actions leave the input position and output unchanged, as does the time-zero configuration. The distinctness of the source and destination indices ensures these head updates apply to separate tapes.

**Key facts.** `Turing.StepBlock.succFieldTM_trace`.
