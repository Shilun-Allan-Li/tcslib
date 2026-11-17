<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.guardedScan_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Guarded scan equivalence

**Claim.** For every machine format $F$ and finite Boolean string $\alpha$, the guarded scan of $\alpha$ equals the scan of $\alpha$ in format $F$.

**Proof.** Unfold the guarded scan and split according to the result of parsing $\alpha$ into $(bits,rest)$. If parsing fails, the format scan also fails because it begins with the same parser. If parsing succeeds, the guard either rejects, in which case the guarded scan returns failure, or passes, in which case it calls the format scan. In the passing case, if the format scan fails both sides are failure. If it succeeds, the scan grammar guard says that $rest$ is long enough to meet the guard threshold, contradicting the guarded scan’s rejection condition. Thus this final case also has the guarded scan equal to the format scan.

**Key facts.** `Turing.MachineFormat.scan_grammar_guard`.
