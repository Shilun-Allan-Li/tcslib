<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Inclusions.lean :: Complexity.b2b_setup_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Setup Run and Head Bound

**Claim.** If $M_P$ halts on $x$ with output consisting of $Q$ true symbols and uses at most $s$ work-tape cells, then the host reaches its loop phase with the counter decrement active, input-head position $1$, the first word tape holding $Q$ false symbols, and the last tape holding $Q$ true symbols. Every work-tape head up to that time has absolute position at most $s+Q+1$.

**Proof.** First use the setup-capture result (Complexity.b2b_setup_capture) with output $w$ equal to the word of $Q$ true symbols. It gives a host configuration in the origin phase with $w$ on the designated tape and the stated head bound, up to that point. In the origin phase, the virtual rewind returns the input head to position $1$ while preserving the stored word; the phase-host simulation lemma (Turing.phaseHostTM_run) transfers this run to the host’s origin phase and redirects its exit to the counter phase. The origin-run result (Complexity.b2b_origin_run) also bounds heads during this passage by $Q+1$.

Next, the counter-phase seed run (Complexity.b2b_seed_run) sweeps across the stored word, changing the first word tape from $Q$ true symbols to $Q$ false symbols and copying the true word to the last tape. It rewinds and reaches the rewind phase, with all heads bounded by $Q+1$. The rewind-return result (Complexity.b2b_rewind_return) takes the input head back to position $1$ without moving any work-tape head. A second application of the phase-host simulation lemma redirects that exit to the loop phase with counter decrement active. The dispatch-retag identity (Complexity.b2b_dispatch_retag) identifies the resulting phase-tagged configuration with the specified host state.

Concatenate these runs using the run-composition law (Turing.MultiTapeTM.runFrom_add). For the head bound, split any time in the concatenated run among the setup, origin, seed, and rewind segments. Their respective bounds are at most $s+Q$, $Q+1$, $Q+1$, and the starting head positions in the rewind segment; each is at most $s+Q+1$. The final configuration is therefore the one claimed, with the bound holding at every preceding time as well.

**Key facts.** `Complexity.b2b_setup_capture`, `Complexity.b2b_origin_run`, `Turing.phaseHostTM_run`, `Complexity.b2b_seed_run`, `Complexity.b2b_rewind_return`, `Complexity.b2b_dispatch_retag`, `Turing.MultiTapeTM.runFrom_add`.
