<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenLoop.lean :: Complexity.LogProg.ISGen.start_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initialization of the Counting Run

**Claim.** Under the input-length oracle and register-bound hypotheses, termination, the register bound, and acceptance behavior from the initial round state imply the same properties from the initial scan state.

**Proof.** The scan phase queries the oracle on the input paired with successive binary counters. By the assumed oracle behavior, it stops exactly at the input length, so it reaches the state where the length register has value $|x|$ (`Complexity.LogProg.ISGen.gscan_run`). The length fits the register bound: $|x|<2^{\operatorname{size}(|x|)+1}\le B$, using the binary-size bound (`Complexity.LogProg.ISCount.lt_two_pow_size_succ`) and the hypothesis on $B$. The subsequent halving phase repeatedly halves this counter while incrementing the logarithm register. It therefore reaches the initial round state with the counter zero and logarithm register $\operatorname{size}(|x|)+1$; these values fit the bound by the same exponential bound on $B$. The halving-run result transfers the assumed round-state semantics back to the start of this phase (`Complexity.LogProg.ISGen.ghalf_run`). The scan phase's own register increment is valid within the bound, and composing it with the halving phase via the semantics rule for an increment (`Complexity.LogProg.NSem.inc`) proves the claim. The round-state witness uses only the equality between its initialized registers and those prescribed by the halving conclusion (`Complexity.LogProg.ISGen.IG.of_eq`).

**Key facts.** `Complexity.LogProg.ISCount.lt_two_pow_size_succ`, `Complexity.LogProg.ISGen.gscan_run`, `Complexity.LogProg.ISGen.ghalf_run`, `Complexity.LogProg.NSem.inc`, `Complexity.LogProg.ISGen.IG.of_eq`.
