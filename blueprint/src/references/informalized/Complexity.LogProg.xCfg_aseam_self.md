<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMSim.lean :: Complexity.LogProg.xCfg_aseam_self -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Configuration Is Preserved

**Claim.** For every register index $r$, resetting the initial seam configuration's state, input-head position, and register $r$'s work-head position to their initial values leaves the configuration unchanged.

**Proof.** The reset identity for an initial seam configuration states that applying the update with state $l'$ produces the initial seam configuration with state $l'$. Take $l'=l$. The resulting configuration is therefore the original initial seam configuration, and reversing this equality gives the claimed order of the two sides.

**Key facts.** `Complexity.LogProg.xCfg_aseam`.
