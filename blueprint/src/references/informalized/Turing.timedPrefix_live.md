<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedPrefix_live -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parser Liveness Before Completion

**Claim.** For Boolean words $b_s,\alpha,x$, the prefix parser on $\langle\langle b_s,\alpha\rangle,x\rangle$ has not halted at any time $s<4|b_s|+2|\alpha|+6$.

**Proof.** Assume instead that the parser has halted at time $s$. The strict bound on $s$ gives $s\le 4|b_s|+2|\alpha|+5$, so write $s+d=4|b_s|+2|\alpha|+5$ for some $d\ge0$. A machine that has halted remains at the same configuration under every further step (`Turing.MultiTapeTM.runFrom_of_halt`); hence it would also be halted at time $4|b_s|+2|\alpha|+5$, using the decomposition of a run into successive segments (`Turing.MultiTapeTM.runFrom_add`). But the parser is still active at precisely that time (`Turing.timedPrefix_penultimate`), a contradiction.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_of_halt`, `Turing.timedPrefix_penultimate`.
