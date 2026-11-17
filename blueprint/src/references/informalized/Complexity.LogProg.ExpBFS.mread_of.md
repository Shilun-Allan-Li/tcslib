<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Run.lean :: Complexity.LogProg.ExpBFS.mread_of -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation Across a Memory Read

**Claim.** A guarded reachable configuration from the branch selected by the memory bit at the head is guarded reachable from the configuration at the instruction that reads that bit.

**Proof.** The bounds on the registers and head position ensure that the configuration at the read instruction satisfies the guard ($\mathrm{g\_of}$). By the definition of a memory read, one step leaves the registers, memory, and head position unchanged and enters $l_1$ if $M(p)$ is true, or $l_0$ if it is false. Its successor is therefore exactly the branch configuration from which reachability is assumed. Prepending this guarded step gives the desired result ($\mathrm{MReach.step}$).

**Key facts.** `Complexity.LogProg.ExpBFS.g_of`, `Complexity.LogProg.MReach.step`.
