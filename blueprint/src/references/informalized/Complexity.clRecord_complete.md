<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRecord_complete -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completion of trajectory recording

**Claim.** The recording machine reaches the completed recorder configuration within the stated time bound, storing the source machine's configuration after $T$ steps, its movement counts and recorded rows through time $T$, and the prescribed input and retained fields.

**Proof.** Let $x$ be the packed input. First apply the preparation-time bound (`Complexity.clPrepare_first`) to reach the loader configuration. The bound also ensures that the preparation machine has not entered the state that transfers control to the recorder before this point. The prepare and record machines agree on all states visited during this preparation phase, so the state-map simulation theorem (`Turing.MultiTapeTM.runFrom_mapState_of_agreeOn`) transfers this run to the recording machine. At the endpoint, one transition dispatches into the recorder: the control action leaves the input head in place, and the prepared tape contents are exactly the recorder's initial frame (`Complexity.clRecord_prepare_frame`).

Next, the recorder's completion result (`Complexity.clRec_complete`) supplies a run of length $b$ from that initial frame to the completed state, with the source configuration, movement counts, and rows through time $T$ in place. The placement simulation theorem (`Complexity.clPlaced_run`) lifts this run to the recording machine while preserving its extra retained tapes and input. Thus the total time is the preparation time plus one dispatch step plus $b$. The recorder cost bound (`Complexity.clRec_cost_bound`) bounds $b$ by $(4\,\mathrm{field\ count}+7)(T+1)^2$; combining this with the preparation bound gives the claimed total.

**Key facts.** `Complexity.clPrepare_first`, `Turing.MultiTapeTM.runFrom_mapState_of_agreeOn`, `Complexity.clRecord_prepare_frame`, `Complexity.clRec_complete`, `Complexity.clPlaced_run`, `Complexity.clRec_cost_bound`.
