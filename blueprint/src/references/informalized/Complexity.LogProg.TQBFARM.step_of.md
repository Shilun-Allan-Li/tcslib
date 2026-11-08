<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Machine.lean :: Complexity.LogProg.TQBFARM.step_of -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prepending a Program Step

**Claim.** If the registers of $st$ are bounded by $B$ and a guarded, bounded finite run goes from the configuration after one program step from $(l,st)$ to $c$, then such a run goes from $(l,st)$ to $c$.

**Proof.** The register bound on $st$ gives the guard at the starting configuration: `gb_of` supplies both the program precondition and the register bounds there. The general reachability principle that prepends one transition says that if the starting configuration satisfies the guard and the run from its successor satisfies the guard at every pre-endpoint configuration, then the same guarded run can be extended to start at the original configuration (`AReach.step`). Applying it to the one-step successor in the hypothesis gives the desired reachability.

**Key facts.** `Complexity.LogProg.TQBFARM.gb_of`, `Complexity.LogProg.AReach.step`.
