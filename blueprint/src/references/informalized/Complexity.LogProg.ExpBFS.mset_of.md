<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Run.lean :: Complexity.LogProg.ExpBFS.mset_of -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation Across Setting a Memory Bit

**Claim.** If the instruction at $l$ sets the memory bit at the head to true and continues at $l'$, then guarded reachability from the resulting configuration implies guarded reachability from the original configuration at $l$.

**Proof.** The register bounds and the head-position bounds ensure that the original configuration at $l$ satisfies the guard ($\mathrm{g\_of}$). By the definition of setting a memory bit, one step enters $l'$, leaves the registers and head position unchanged, and replaces the memory $M$ by the function that agrees with $M$ except that its value at $p$ is true. This is exactly the configuration from which reachability is assumed. Prepending this guarded step yields the conclusion ($\mathrm{MReach.step}$).

**Key facts.** `Complexity.LogProg.ExpBFS.g_of`, `Complexity.LogProg.MReach.step`.
