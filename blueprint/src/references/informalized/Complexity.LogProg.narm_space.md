<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMRun.lean :: Complexity.LogProg.narm_space -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Compiled space bound and acceptance

**Claim.** Under the stated halting and guard hypotheses, the compiled machine halts on every choice string of some fixed length, obeys the stated space bound, and has an accepting run exactly when the register program has a length-$N$ choice string yielding true.

**Proof.** Apply the run simulation theorem (`narm_run`) to the initial register configuration. It supplies a common compiled-run length $T$, bounds the compiled machine’s work-head positions throughout each run using the register-width and decider-space hypotheses, and relates compiled outputs to register-program answers. The compiled machine’s initial configuration is the corresponding encoded initial configuration (`ncompileTM_init`), so the simulation gives halting for every length-$T$ choice string. For space, apply the bound on visited tape cells from head-position ranges (`spaceUsedWith_le_of_ranges`): each register tape has head positions within an interval of width at most $W+2$, while each decider tape has positions between $-B$ and $B$, giving at most $2B+1$ cells. Summing over the $m$ register tapes and $k_D$ decider tapes yields $m(W+2)+k_D(2B+1)$. Finally, the simulation’s output correspondence gives a compiled run with output true from any length-$N$ register run yielding true; conversely, a compiled accepting run has output true and therefore corresponds to such a register run.

**Key facts.** `Complexity.LogProg.narm_run`, `Complexity.LogProg.ncompileTM_init`, `Complexity.LogProg.spaceUsedWith_le_of_ranges`.
