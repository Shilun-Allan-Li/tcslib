<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Nondeterministic.lean :: Turing.NDTM.HaltsWithin.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of All-Branch Halting

**Claim.** If every choice word of length exactly $t$ halts from the initial configuration, then every choice word of length exactly $t'\ge t$ halts as well.

**Proof.** Take any choice word $w$ of length $t'$. Its prefix of length $t$ has length exactly $t$, so the hypothesis says that running this prefix from the initial configuration halts. Split $w$ into that prefix followed by its remaining suffix using the run-concatenation identity (`runWith_append`). Once a configuration is halted, every further choice word leaves it unchanged (`runWith_of_halt`). Thus the run under all of $w$ has the same halted state as the run under the prefix, proving the claim.

**Key facts.** `Turing.NDTM.runWith_append`, `Turing.NDTM.runWith_of_halt`.
