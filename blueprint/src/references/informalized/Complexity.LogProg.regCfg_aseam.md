<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMSim.lean :: Complexity.LogProg.regCfg_aseam -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating a register in a seam configuration

**Claim.** Replacing register $r$’s tape in the seam configuration determined by $l,v,\mathrm{out}$ with the binary word for $n$, placing its head at $0$, and changing the state to $(l',\mathrm{start})$ gives the seam configuration determined by $l'$, the updated register values, and the same output word.

**Proof.** Compare the components of the two configurations. Their states, input-head positions, and output words agree by construction. For each register, split into whether it is $r$: at $r$, both tape functions are the binary tape for $n$ and both head positions are $0$; at any other register, the updates leave the original tape and head position unchanged, which are exactly those of the seam configuration with the updated value function. Thus all configuration components agree.
