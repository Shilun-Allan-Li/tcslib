<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPTIMEThreshold.lean :: Randomized.Amplify.rewind_halts_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting from a rewind configuration

**Claim.** If every length-$t$ choice word makes the original machine halt on $x$, then from a rewind configuration at run $j$, with empty output, blank later blocks, and input-head position at most $t+1$, every choice word of length $i(2t+3)+1$ makes the amplified machine halt, provided $j+i=r$.

**Proof.** We argue by induction on $i$.

1. If $i=0$, the relation $j+i=r$ says that $j=r$, so this is the last run. Every word of the required length has the form $b::w$. The last-rewind property (`rewind_last`) says that either choice on this first step takes the machine to the same finished configuration. That configuration is halted, proving the claim.

2. Suppose $i>0$. Then $j<r$. Let $p$ be the input-head position after moving one place to the left. The input-head movement formula (`moveInputPos_neg_val`) gives $p=C.inputPos-1$, so $p\le t+1$. The rewind-run property (`rewind_run_pos`) says that after exactly $p+2$ choices the amplified machine reaches the restart configuration for run $j+1$, and its work-tape head positions have not changed during this rewind.

3. At that restart, the relevant work-tape block is blank and the output is empty, by the assumptions on the rewind configuration. The restart equality (`restart_eq_emb`) therefore identifies the restart configuration with an embedding of the original machine's initial configuration. The remaining simulated original computation can now be run for $t$ choices. By the hypothesis that all length-$t$ choice words halt the original machine, this simulation reaches a halted original configuration. The embedding respects each nonhalting step, by the step-embedding property (`step_emb`). Its halted result is a rewind configuration for run $j+1$, by `rewindAt_emb`; the freshness condition needed there follows from the blankness of the later blocks.

4. Apply the induction hypothesis at run $j+1$, for the same $i-1$. The input-head position bound required there holds: the restart begins at the left end, and the $t$ simulated steps move the head by at most $t$, so its shifted position is at most $t+1$. Thus every subsequent word of length $(i-1)(2t+3)+1$ halts the amplified machine from that rewind configuration.

5. Concatenating these segments gives a halting run from $C$. The first rewind segment uses $p+2\le t+3$ choices, and the original simulation uses $t$ choices; together these use at most $2t+3$. The induction segment uses $(i-1)(2t+3)+1$ choices. Hence the run halts after at most $i(2t+3)+1$ choices. The run-on-concatenated-words identity (`runWith_append`) puts these consecutive segments together, and the extension property for halting (`halted_of_le`) upgrades halting within this length to halting for every word of exactly the required length.

**Key facts.** `Randomized.Amplify.rewind_last`, `Turing.FinTM.moveInputPos_neg_val`, `Randomized.Amplify.rewind_run_pos`, `Randomized.Amplify.restart_eq_emb`, `Randomized.Amplify.halts_comp_pos`, `Randomized.Amplify.step_emb`, `Randomized.Amplify.rewindAt_emb`, `Turing.NDTM.runWith_append`, `Randomized.Amplify.halted_of_le`.
