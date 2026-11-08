<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Constructible.lean :: Complexity.b3a_log_machine -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logarithmic-Space Length Machine

**Claim.** There are a positive constant and a finite-state machine that, on every Boolean word $x$, outputs the binary expansion of $\lfloor\log_2 |x|\rfloor+1$ and uses at most a constant multiple of $\lfloor\log_2 |x|\rfloor+2$ work-tape cells, with the stated convention for the empty input.

**Proof.** Take the counter machine from `b3a_counter`, which writes the binary expansion of the input length, and a finite-state machine that computes the binary expansion of the length of its input using space linear in that length (`computesFunInTime_lengthBits_spaceUsed`). The construction runs the counter first, then a four-step writer that changes the first bit of the counter's output to true, and finally a virtualized copy of the second machine, using the counter's output as its simulated input. The embeddings place these machines' tapes in a common tape collection; the configuration-identification lemmas `b3a_embed_cfg` and `b3a_virtual_cfg` ensure that the phases begin with the intended tape contents and head positions.

For the first switch, the counter reaches its designated exit state for the first time at its stated stopping time. The writer then reaches its done state for the first time after four steps, with buffer $y=\mathrm{true}::\mathrm{tail}(x.length.bits)$ (`b3a_overwrite`). The first-exit composition results (`seamCompTM_run_ofCfg` and `seamCompTM_firstReturn_ofCfg`) therefore justify both switches and show that the final phase runs on $y$. Its virtual-hosting property (`vhostEmitTM_runFrom`) forwards the second machine's output and halting state, so the composed machine halts with the required answer.

For space, the counter uses at most $B(|x.length.bits|+1)$ cells. Since the length of a natural number's binary expansion is at most the number itself (`length_bits_le_self`), and $|x.length.bits|\leq\log_2|x|+1$ (`length_bits_le_log`), this is bounded in terms of $\logSpace(|x|)$. The writer uses at most two cells. The hosted final phase uses at most the second machine's space plus the buffer and boundary overhead (`vhostEmitTM_spaceUsed_le`); the length identity $|y|=\logSpace(|x|)$ follows from `b3a_word_length`. Applying the embedding bounds (`b3a_embed_space`) and adding the phase ledgers (`b3a_seam_space`) gives a bound of the form $k(B+b+8)(\logSpace(|x|)+1)$, which is at most the claimed bound after choosing the positive constant $A=k(B+b+8)+1$.

**Key facts.** `Complexity.b3a_counter`, `Turing.FinTM.computesFunInTime_lengthBits_spaceUsed`, `Complexity.b3a_overwrite`, `Turing.seamCompTM_run_ofCfg`, `Turing.seamCompTM_firstReturn_ofCfg`, `Turing.vhostEmitTM_runFrom`, `Turing.length_bits_le_self`, `Complexity.LogProg.length_bits_le_log`, `Turing.vhostEmitTM_spaceUsed_le`, `Complexity.b3a_word_length`, `Complexity.b3a_embed_space`, `Complexity.b3a_seam_space`.
