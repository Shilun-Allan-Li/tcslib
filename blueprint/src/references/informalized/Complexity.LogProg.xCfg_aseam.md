<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMSim.lean :: Complexity.LogProg.xCfg_aseam -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Resetting at the Initial Seam

**Claim.** Applying the configuration update to the initial seam configuration with state $l$—setting its state to $(l',\mathrm{start})$, its input-head position to $1$, and register $r$'s work-tape head to $0$—gives the initial seam configuration with state $l'$.

**Proof.** Configurations are equal once their state, input-head position, tape contents, work-head positions, and output agree. The update sets the state and input-head position to the stipulated initial values, while preserving tape contents and output. For the work-head positions, the initial seam configuration places every head at $0$; updating register $r$ to $0$ preserves that value, and all other registers are unchanged. Hence every component agrees with the initial seam configuration for state $l'$.
