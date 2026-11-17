<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loop_halted_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Computation of a Boolean Disjunction

**Claim.** Under the stated endpoint and round hypotheses, the machine halts within NB steps from c(0), with output the one-bit word whose value is true exactly when some index j<N is accepted.

**Proof.** Induct on N, allowing the configuration sequence and acceptance predicate to vary. At N=0, c(0) is the endpoint configuration, so it is halted with output [false], as required for the empty disjunction. For N+1, take a round time t≤B at index zero. If zero is accepted, that round already halts with output [true], which is the disjunction over the range. If zero is not accepted, the round reaches c(1). Apply the induction hypothesis to the shifted sequence and shifted acceptance predicate to obtain a further time s≤NB at which the run halts with the disjunction over the remaining indices. By run composition (`runFrom_add`), the run from c(0) for t+s steps reaches that halted configuration. The bound t+s≤B+NB=(N+1)B holds, and because zero was not accepted, the remaining disjunction is exactly the original one. The decomposition of the range into its first element and shifted tail gives this disjunction identity.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`.
