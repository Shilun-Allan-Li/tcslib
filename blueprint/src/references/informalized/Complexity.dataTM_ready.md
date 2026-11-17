<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean :: Complexity.dataTM_ready -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The Simulator Reaches Its First Macrostep

**Claim.** For each binary word $x$, there is a time and a schedule configuration whose unary and guide tapes have the prescribed encodings, such that the simulator is in its macrostep-check phase with the initial data registers, empty output, and data-tape payloads decoding to the corresponding payloads of $M$’s initial configuration on $x$.

**Proof.** Apply the schedule-readiness result to obtain a time $t$ and schedule configuration with phase `macroCheck`, unary head at $1$, guide head at $0$, and the required unary and guide tape contents (`obliviousSchedule_ready`). The simulator’s preparation invariant at this same time supplies data registers, data tapes, and output, and identifies the simulator run with the decorated schedule run (`prepInvariant_run`). At a configuration with these head positions, the macro configuration agrees with the underlying schedule configuration (`macroCfg_self`). The preparation invariant in phase `macroCheck` forces the data registers to be their initial values and the output to be empty. Finally, the full-copy property identifies each data tape’s current payload with the corresponding payload of the initial machine configuration (`copiedPayload_full`).

**Key facts.** `Complexity.obliviousSchedule_ready`, `Complexity.prepInvariant_run`, `Complexity.macroCfg_self`, `Complexity.copiedPayload_full`.
