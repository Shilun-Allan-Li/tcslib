<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Inclusions.lean :: Complexity.b2b_trial_call -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hosted Call Trial

**Claim.** Under the stated clean-run hypothesis for the cleaned simulation of $M_V$ on $x\mathbin{++}u$, the call-phase machine reaches its exit with input-head position $1$, the first two tapes unchanged, and the third tape holding $[b]$ with its head at $1$. The exit is not reached earlier, and throughout the run every work-tape head has absolute position at most $|x|+|u|+s+1$.

**Proof.** Let $D$ be the hosted source machine and start its simulation on $y=x\mathbin{++}u$ at the input position corresponding to the boundary between $x$ and $u$. The hosted-source run result (Complexity.b2b_hostedSource_run) applies the clean-run hypothesis: at some time the source has halted with output $[b]$, and its work-tape heads throughout the run are bounded by $s$. Choose the first halting time (Turing.MultiTapeTM.exists_first_halt). This preserves the terminal configuration and ensures the source has not halted at any earlier time.

The virtual-host simulation lemma (Turing.vhostEmitTM_runFrom) transfers this source run to the call machine’s hosted simulation, while maintaining the virtual input-head tag. Embed that simulation into the call phase, using the third tape as the output sink. The sink is disjoint from the embedded source tapes; the embedded-simulation run lemma (Turing.embedSilentRetTM_run) therefore shows that the call machine follows the hosted run and reaches its designated exit exactly when the source halts. The call-shape identity (Complexity.b2b_call_shape) translates the resulting embedded configuration into the claimed tape layout: the first two tapes retain $u$ and $x\mathbin{++}u$, and the sink contains $[b]$ with head at $1$. The first-halt choice gives the assertion that the exit is not entered earlier.

For the head bound, the virtual buffer head stays between $-1$ and $|x|+|u|$, by the virtual-buffer bound (Turing.vhostCfg_buffer_head_mem). Each embedded bank head is a source head, so its position is bounded by $s$ using the hosted-source bound; the bank-visited-head identity (Turing.vhostEmitTM_visitedByTapeHead_bank) lets that bound be read in the hosted simulation. The sink head tracks the amount of output emitted so far. Output is a prefix of the final output (Turing.MultiTapeTM.output_prefix), so its length is at most one. Every unused tape remains at its initial origin position by the embedding frame property (Turing.embedSilentTM_frame). Combining these cases gives the bound $|x|+|u|+s+1$ for every tape at every time in the run.

**Key facts.** `Complexity.b2b_hostedSource_run`, `Turing.MultiTapeTM.exists_first_halt`, `Turing.vhostEmitTM_runFrom`, `Turing.embedSilentRetTM_run`, `Complexity.b2b_call_shape`, `Turing.vhostCfg_buffer_head_mem`, `Turing.vhostEmitTM_visitedByTapeHead_bank`, `Turing.MultiTapeTM.output_prefix`, `Turing.embedSilentTM_frame`.
