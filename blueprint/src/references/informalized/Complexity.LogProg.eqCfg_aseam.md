<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMSim.lean :: Complexity.LogProg.eqCfg_aseam -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Head Positions in a Seam Configuration

**Claim.** Changing a seam configuration to state $(l',\mathrm{start})$ and setting the two specified head positions to zero yields exactly the seam configuration at that new state.

**Proof.** The two configurations have the same input-head position, tape contents, and output. For each register, the nested updates set its head position to zero if its index is either of the two specified registers; otherwise the original seam head position is retained, which is already zero. Hence the head-position functions agree pointwise, and the states agree as well.
