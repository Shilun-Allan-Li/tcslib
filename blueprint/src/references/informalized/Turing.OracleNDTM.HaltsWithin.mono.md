<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/OracleNondeterministic.lean :: Turing.OracleNDTM.HaltsWithin.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Bounded Halting

**Claim.** If every binary choice word of length $t$ makes the oracle-machine run halt, then, whenever $t\le t'$, every binary choice word of length $t'$ also makes it halt.

**Proof.** Fix a choice word $w$ of length $t'$. Its prefix of length $t$ has length exactly $t$, so the hypothesis says that the run on this prefix halts. Decompose $w$ as that prefix followed by the remaining suffix. The run on the concatenation is the run on the suffix starting from the configuration reached on the prefix (`runWith_append`). Since that intermediate configuration is halted, every further run leaves it unchanged (`runWith_of_halt`). Thus the run on all of $w$ has the same halted state.

**Key facts.** `Turing.OracleNDTM.runWith_append`, `Turing.OracleNDTM.runWith_of_halt`.
