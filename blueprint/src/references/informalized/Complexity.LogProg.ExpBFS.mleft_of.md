<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Run.lean :: Complexity.LogProg.ExpBFS.mleft_of -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prepending a Leftward Memory Move

**Claim.** If the instruction at $l$ moves the memory head left and continues at $l'$, then any guarded reachable configuration from the corresponding post-move configuration is guarded reachable from the configuration at $l$.

**Proof.** The register bounds and the head-position bounds imply that the starting configuration at $l$ satisfies the guard ($\mathrm{g\_of}$). By the definition of a leftward memory move, one machine step from this configuration leaves the registers and memory unchanged, moves the head from $p$ to $p-1$, and enters $l'$. Thus its successor is exactly the assumed starting configuration for the given guarded reachability. Prepending this one guarded step to that reachability yields the desired reachability ($\mathrm{MReach.step}$).

**Key facts.** `Complexity.LogProg.ExpBFS.g_of`, `Complexity.LogProg.MReach.step`.
