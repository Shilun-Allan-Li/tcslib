<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMProb.lean :: Complexity.LogProg.narm_randProb -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality of Acceptance Probabilities

**Claim.** For each Boolean value $b$, the probability that a uniformly chosen length-$T$ choice string makes the compiled machine output exactly $b$ equals the probability that a uniformly chosen length-$N$ choice string makes the register program return $b$.

**Proof.** Apply the run-probability correspondence theorem to the initial program configuration, with empty output prefix. It supplies a length $T_0$ such that every length-$T_0$ choice string halts in the compiled machine, and identifies the probability of output $[] ++ [b]$ at length $T_0$ with the probability that the original program returns $b$ at length $N$. The compiled machine also halts on every length-$T$ string by hypothesis. Extend both experiments to the common length $\max(T,T_0)$: once a computation has halted, additional choice bits leave its configuration unchanged, so the event under consideration has the same probability at the extended length as at its original length. At length $T_0$, the empty-prefix event $[] ++ [b]$ is exactly output $[b]$. Combining these equalities with the correspondence gives the desired identity.

**Key facts.** `Complexity.LogProg.narm_run_randProb`, `Complexity.LogProg.ncompileTM_init`, `Complexity.LogProg.randProb_runWith_mono`.
