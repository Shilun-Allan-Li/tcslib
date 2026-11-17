<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPTIMEThreshold.lean :: Randomized.Amplify.amp_haltsWithin_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting Time with Positive Amplification

**Claim.** If $N$ halts on $x$ after every choice word of length exactly $t$, then the amplified machine halts on $x$ after every choice word of length exactly $t+r(2t+3)+1$.

**Proof.** Fix a choice word of the stated length and identify the amplified initial configuration with the embedding of the original initial configuration (`init_eq_emb`). During the first $t$ choices, each nonhalting original step is matched by one amplified step under this embedding (`step_emb`). The remaining run is handled by the composition-of-halting result `halts_comp_pos`: once the original computation has halted, the amplified machine's remaining phases halt on every choice word of the required length. For this final condition, the halted embedded configuration is a rewind configuration (`rewindAt_emb`), and `rewind_halts_pos` supplies its halting bound, using the hypothesis that all original runs of length $t$ halt. The initial configuration also meets the required input-position bound, so the composition result gives the claimed total time.

**Key facts.** `Randomized.Amplify.init_eq_emb`, `Randomized.Amplify.step_emb`, `Randomized.Amplify.rewindAt_emb`, `Randomized.Amplify.fresh_init`, `Randomized.Amplify.rewind_halts_pos`, `Randomized.Amplify.halts_comp_pos`.
