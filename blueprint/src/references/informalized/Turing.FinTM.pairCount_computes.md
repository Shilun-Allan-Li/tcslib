<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.pairCount_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Time Bound for the Captured-Length Checker

**Claim.** The captured-length checker computes the specified one-bit predicate—whether a valid pair encoding has second component no longer than the output of the original machine—in at most $T(|x|)+2|x|+5$ steps.

**Proof.** Fix an input $x$. The length-start lemma provides a time $t\le T(|x|)+|x|+4$ at which the checker has finished simulating the original machine and is positioned to parse the remaining input, with its output equal to $g(x)$ (`Turing.FinTM.lenStart`). Apply the length-parse lemma to the remaining suffix: it halts within $r\le |x|+1$ additional steps and outputs $1$ exactly when that suffix decodes as a pair whose second component has length at most the captured output length; malformed encodings produce $0` (`Turing.FinTM.lenParse_run`). The run-composition identity joins these two phases (`Turing.MultiTapeTM.runFrom_add`), and the computation characterization identifies the resulting halting state and output (`Turing.FinTM.computesInTime_iff`). Finally, $t+r\le T(|x|)+2|x|+5$, so monotonicity gives the stated time bound (`Turing.FinTM.ComputesInTime.mono`).

**Key facts.** `Turing.FinTM.lenStart`, `Turing.FinTM.lenParse_run`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.ComputesInTime.mono`.
