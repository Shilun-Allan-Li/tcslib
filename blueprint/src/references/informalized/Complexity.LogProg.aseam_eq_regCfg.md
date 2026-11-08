<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMSim.lean :: Complexity.LogProg.aseam_eq_regCfg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register Tape at the Seam

**Claim.** At the seam configuration encoding state $l$, register assignment $v$, and output $out$, replacing register $r$’s tape by the tape holding the binary word of $v(r)$ and setting its head position to zero leaves the configuration unchanged.

**Proof.** Compare the components of the two configurations. The state, input-head position, and output agree by construction. For the work tapes and their head positions, consider each register index: at $r$, the replacement installs exactly the tape and zero position already present in the seam configuration; at every other index, the update leaves the original component unchanged. Thus all configuration components agree.
