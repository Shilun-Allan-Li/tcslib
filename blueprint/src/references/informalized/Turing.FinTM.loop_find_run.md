<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loop_find_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Accepting Payload Within a Step Bound

**Claim.** Under the stated round-by-round hypotheses, the machine halts within NB steps from c(0), outputting the payload at the first accepting index below N, or the empty word if there is no such index.

**Proof.** Induct on N, allowing the configuration sequence, acceptance predicate, and payload function to vary. If N is zero, the initial configuration is c(N), so the endpoint hypothesis gives a halt with empty output in zero steps. For N+1, apply the round hypothesis at index zero and let t≤B be its time. If index zero accepts, the run is already halted with payload y(0). Its time is at most (N+1)B, and the first accepting index in the range is zero, so this is the required output. If index zero does not accept, the run at time t is exactly c(1). Apply the induction hypothesis to the shifted sequence j ↦ c(j+1), with the shifted acceptance and payload functions. It supplies a further time s≤NB at which the run from c(1) halts with the payload for the first accepting shifted index, or empty output. The run-composition law (`runFrom_add`) shows that the run from c(0) for t+s steps reaches this same halted configuration. Since t+s≤B+NB=(N+1)B and index zero was not accepting, its first accepting index and output agree with those of the shifted problem; if none accepts, the output is empty.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`.
