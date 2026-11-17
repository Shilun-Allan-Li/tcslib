<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.taut_machine_malformed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Verifier on Malformed Input

**Claim.** If exact-consumption parsing fails on $x$, the verifier computes output $[1]$ on the pair encoding of $x$ and $u$ within $2|x|+3$ steps.

**Proof.** The parser characterization (`Complexity.taut_syntax_parse`) says the syntax acceptor returns true exactly when parsing succeeds. Thus the syntax scan cannot finish in its accepting state. The syntax-run result (`Complexity.taut_syntax_run`) processes the doubled encoding of $x$ in $2|x|+2$ steps and consequently leaves the verifier at the true verdict state. One more transition halts and outputs true (`Complexity.taut_verdict`). The initial configuration is the specified syntax-scan configuration by `Complexity.taut_init`; combining the scan and final transition uses `Turing.MultiTapeTM.runFrom_succ_eq_step'`. Finally, the computation characterization (`Turing.FinTM.computesInTime_iff`) turns the resulting halted state and output into the claimed computation.

**Key facts.** `Complexity.taut_syntax_parse`, `Complexity.taut_syntax_run`, `Complexity.taut_verdict`, `Complexity.taut_init`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.computesInTime_iff`.
