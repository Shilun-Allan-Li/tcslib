<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean :: Complexity.dataTM_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of the oblivious simulator

**Claim.** If the clock machine computes the required time bound, the bound dominates input length, and the source machine decides the language within the stated budget, then the constructed simulator halts on each embedded binary input with the single output symbol encoding membership in the language.

**Proof.** Fix a binary input $x$, and let $B=(a+1)(T(|x|)+1)$. The bound $|x|+1\le B$ follows from $|x|\le T(|x|)$ and $a+1\ge1$. The readiness result (`dataTM_ready`) supplies a simulator configuration after some time $t$ in macrostep-check phase, with unary tape for budget $B$, guide tape of radius $3B$, and data tapes encoding the source machine's initial configuration. Iterating the one-macrostep simulation $B$ times (`dataCfg_iterates`) gives a macrostep-check configuration after $B(6(3B)+8)$ additional steps whose encoded source data and state match the source machine after $B$ steps. The unary marker is absent at coordinate $B+1$ (`unaryTape_end`), so the finish transition halts and outputs the bit stored in the data state (`dataCfg_finish`). Since $B$ exceeds the source time budget $aT(|x|)$, the source machine has halted by time $B$; its output at that budget has last bit equal to the indicator of membership in the language (`sourceAnswer_at_budget`). Thus the simulator's output is the single embedded symbol for that indicator. The characterization of computation in time (`computesInTime_iff`) translates the final run's halting state and output into the claimed computation statement, and the run concatenation and successor-step identities assemble the readiness time, the $B$ simulated macrosteps, and the final transition.

**Key facts.** `Complexity.dataTM_ready`, `Complexity.dataCfg_iterates`, `Complexity.unaryTape_end`, `Complexity.dataCfg_finish`, `Complexity.sourceAnswer_at_budget`, `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
