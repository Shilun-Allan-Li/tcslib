<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterMain.lean :: Complexity.UTab.tabEmit_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary Tableau Output

**Claim.** For $T\geq1$, the counter program on the specified unary-prefixed input outputs the encoding of the circuit tableau for $M$, input width $n$, suffix $z$, and time bound $T$.

**Proof.** The execution theorem `goes_emit` supplies a run of the counter program on the given input that prints exactly the tableau encoding and uses at most `runBound` steps. By `runBound_le`, this number of steps is at most $\mathrm{emitC}(M)(n+T+|z|+3)^3$. The input length is $n+T+|z|+2$, so its length plus one is $n+T+|z|+3$. Thus the run bound is no larger than the budget $\mathrm{emitC}(M)(|w|+1)^3$ used in the definition of `tabEmit`. The bounded-run principle `run_budget` therefore identifies the program's state at that budget with the state reached in `goes_emit`; in particular, its output is the stated tableau encoding.

**Key facts.** `Complexity.UTab.goes_emit`, `Complexity.UTab.runBound_le`, `Complexity.UTab.run_budget`.
