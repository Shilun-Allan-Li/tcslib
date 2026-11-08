<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.splitSolveTM_spaceUsed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Split Solver Space Bound

**Claim.** For all $C,e,t\in\mathbb N$ and every Boolean word $x$, the split solver’s total number of distinct work-tape cells visited by time $t$ is at most $23$ times its number of work tapes times $((C+1+5e)2^e+46)(|x|+1)^{e+1}$.

**Proof.** Use `split_sources` to identify the machine with a loop host whose body is the split body built from a source machine $M$. The source’s round-time bound, together with the length-counter fuel computation, gives the initialization and round hypotheses via `split_hyps` and `split_fuel`. The loop-host space estimate (`loopHostTM_spaceUsed_le_budget`) then bounds space by $23$ times the host’s number of work tapes times $(((C+1+5e)2^e+45)(|x|+1)^{e+1}+1)$. Set $P=(|x|+1)^{e+1}$ and $A=(C+1+5e)2^e$. Since $P\ge1$, we have $(A+45)P+1\le(A+46)P$. Substitution and arithmetic give the asserted bound.

**Key facts.** `Turing.FinTM.split_sources`, `Turing.FinTM.split_hyps`, `Turing.FinTM.loopHostTM_spaceUsed_le_budget`, `Turing.FinTM.split_fuel`.
