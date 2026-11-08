<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satHost_call -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Running a Module in the Host

**Claim.** A module computation that stays unhalted until time $t$ and then halts with the specified result and output is simulated by the host without reaching its loop-anchor state before $t$; at time $t$ the host is in the module's return state with the result tapes and prefixed output.

**Proof.** Let $c$ be the module's initial configuration with argument on tape zero. Padding it to the host's tape count preserves its represented tape contents, and the seam identity identifies the host entry configuration with the emitted, padded configuration having output prefix $\mathrm{pre}$ (`Complexity.satHost_seam`). For every $v\le t$, the host run from this entry is the emitted image of the padded module run at time $v`: the run simulation theorem applies because the module remains unhalted at every earlier time (`Turing.emit_run`), and padding commutes with running (`Complexity.satPad_run`). If $v<t$, the module configuration is not halted, so its emitted state is still a state tagged by module $i$ and cannot be the loop-anchor state. At $t$, the module's specified halted configuration is mapped by the seam identity to the host return state, with the same padded result tapes and output $\mathrm{pre}\,\mathrm{out}$.

**Key facts.** `Complexity.satHost_seam`, `Complexity.satPad_run`, `Turing.emit_run`.
