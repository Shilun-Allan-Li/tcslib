<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/VirtualInput.lean :: Turing.vhostCfg_buffer_head_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on the Virtual Buffer Head

**Claim.** If the Boolean tag correctly marks the boundary of the original input head, then after any number of virtual simulation steps the added buffer-tape head lies between $-1$ and $|y|$, inclusive.

**Proof.** The virtual-run simulation theorem (`vhostEmitTM_runFrom`) supplies a tag for the reached original configuration and identifies the virtual configuration with the one built from that reached configuration. In this constructed configuration, the added buffer head is the original input-head position minus one. The original input-head position is a natural index below $|y|+2$, hence is between $0$ and $|y|+1$; subtracting one places the buffer head in $[-1,|y|]$.

**Key facts.** `Turing.vhostEmitTM_runFrom`.
