<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/VirtualInput.lean :: Turing.vhostSilentTM_spaceUsed_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Silent Simulation Space Bound

**Claim.** The silent simulation uses at most $M$'s space through time $t$, plus $|y|+2$ and the stated cap-tape bound determined by the prefix and output.

**Proof.** The silent machine's first $m+1$ tapes are the embedded tapes of the emitting virtual-host machine. For each such tape, the embedding theorem (`Turing.embedSilentTM_visitedByTapeHead`) preserves its visited-cell set and space count; the tape-layout result (`Turing.vhostSilent_layout`) identifies the sole remaining tape as the cap tape. Hence the sum over the embedded tapes is the emitting machine's total space. The cap-tape space theorem (`Turing.embedSilentTM_spaceUsedByTape_cap`) bounds its contribution by the increase in output length of the emitting machine, plus one. By run correspondence (`Turing.vhostEmitTM_runFrom`), that output at time $t$ is the prefix concatenated with $M$'s output at time $t$, while the initial encoded output includes the original output of $c$; the resulting length difference is at most the length of the prefix followed by the final output. Finally, the emitting-machine space bound (`Turing.vhostEmitTM_spaceUsed_le`) contributes at most $M$'s space plus $|y|+2$. Adding these two bounds gives the claim.

**Key facts.** `Turing.vhostSilent_layout`, `Turing.embedSilentTM_visitedByTapeHead`, `Turing.embedSilentTM_spaceUsedByTape_cap`, `Turing.vhostEmitTM_runFrom`, `Turing.vhostEmitTM_spaceUsed_le`.
