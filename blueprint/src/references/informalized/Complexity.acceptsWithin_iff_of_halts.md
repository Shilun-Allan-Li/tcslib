<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.acceptsWithin_iff_of_halts -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance Under Larger Halting Budgets

**Claim.** If every choice string of length exactly $t$ halts the machine on $x$ and $t\le t'$, then acceptance within $t'$ steps is equivalent to acceptance within $t$ steps.

**Proof.** An accepting choice string of length $t$ can be extended to any length $t'\ge t$ by appending choices; once the machine has halted, additional choices leave its configuration unchanged. This is the monotonicity of acceptance budgets (`Turing.FinNDTM.AcceptsWithin.mono`), giving one implication. For the converse, take an accepting choice string $w$ of length $t'$. The run-truncation theorem (`Turing.run_take_of_halted`) applies to the run along choice strings: its stability hypothesis follows from the fact that a halted configuration is unchanged by any further choices (`Turing.NDTM.runWith_of_halt`), together with the run concatenation identity (`Turing.NDTM.runWith_append`). Since every choice string of length $t$ halts and $t\le |w|$, the theorem says that the prefix $w.take\ t$ has length $t$, already halts, and reaches exactly the same configuration as $w$. In particular its output is still $[1]$, so it witnesses acceptance within $t$.

**Key facts.** `Turing.FinNDTM.AcceptsWithin.mono`, `Turing.NDTM.runWith_append`, `Turing.NDTM.runWith_of_halt`, `Turing.run_take_of_halted`.
