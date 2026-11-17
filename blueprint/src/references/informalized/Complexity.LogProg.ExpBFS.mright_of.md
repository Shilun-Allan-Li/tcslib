<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Run.lean :: Complexity.LogProg.ExpBFS.mright_of -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation Across a Rightward Memory Move

**Claim.** If the instruction at $l$ moves the memory head right and continues at $l'$, then any guarded reachable configuration from the corresponding post-move configuration is guarded reachable from the configuration at $l$.

**Proof.** The register bounds and the head-position bounds imply that the starting configuration at $l$ satisfies the guard ($\mathrm{g\_of}$). By the definition of a rightward memory move, one machine step leaves the registers and memory unchanged, moves the head from $p$ to $p+1$, and enters $l'$. This is exactly the configuration from which reachability is assumed. Prepending this guarded step yields the desired reachability ($\mathrm{MReach.step}$).

**Key facts.** `Complexity.LogProg.ExpBFS.g_of`, `Complexity.LogProg.MReach.step`.
