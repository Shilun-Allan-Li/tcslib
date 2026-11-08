<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.computesFunInTime_cond_spaceUsed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditional Composition with a Space Bound

**Claim.** Under the stated time and space bounds for the decider and the two branch machines, a finite machine computes the conditional function in the stated time, and its space use is at most the decider's bound plus the larger branch-space bound plus a constant.

**Proof.** Choose the space-aware timed conditional machine and take $c=7+k_1+k_2$, where $k_i$ is the number of work tapes of branch machine $M_i$. The time estimate for this machine ( `f2_cond_time`) gives the claimed time bound with coefficient $5$; extending the time bound to the chosen, larger coefficient $c$ follows from time monotonicity ( `ComputesInTime.mono`). For space, the construction's conditional-space estimate ( `f2_cond_space`) bounds its use by the decider's space at time $T_0(|x|)$, plus the space of the selected branch machine, plus $2$. The branch-space identity ( `f2_branch_space`) expresses that branch use as the selected machine's space plus the other branch's tape count. The assumed space bounds control the decider and selected machine by $s_D(|x|)$ and the corresponding $s_i(|x|)$, respectively; either $s_i(|x|)$ is bounded by their maximum. The remaining tape-count and fixed overhead terms are absorbed by $c$, yielding $s_D(|x|)+\max(s_1(|x|),s_2(|x|))+c$ for every time and input.

**Key facts.** `Turing.FinTM.f2_cond_time`, `Turing.FinTM.ComputesInTime.mono`, `Turing.FinTM.f2_cond_space`, `Turing.FinTM.f2_branch_space`.
