<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.dg_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simulator initialization span

**Claim.** From its initial configuration on $x$, the augmented simulator reaches the encoded initial configuration of $M$ on the retracted input after $2k+2$ steps, with frontier $-1$ and its head throughout in $[-1,k]$.

**Proof.** Let $B$ be the row of $k$ blank cells with all head flags set, and let $w$ be its encoded sweep-symbol list. Its length is $k$. The simulator first generates this row by moving right across it: the right-generation span lemma (`dgSpan_generate_right`) gives $k$ steps, ending at frontier $k$ with the generated row on the left stack in reverse order. The head stays between $0$ and $k$, and widening the interval to $[-1,k]$ preserves the span (`dgSpan_mono`). The simulator then turns around, writing a boundary marker and moving left one position; the turn identity (`sweep_turn_left`) gives this one-step transition and keeps the head in $[-1,k]$ (`dgSpan_one`). It next scans back across the $k$ generated symbols. The reverse-sweep lemma (`sweep_run_reverse`) shows that this places the row followed by a boundary marker on the left stack and brings the frontier to $-1$. The reverse-prefix bound (`dg_sweep_reverse_prefix`) locates every intermediate head position between $-1$ and $k$. At the boundary, the simulator takes one stationary step into the left-growth phase. The resulting stacks encode the initial configuration of $M$: the tape contents are blank, the heads are at zero, and the input position and output agree with the retracted initial configuration. This last transition is a one-step span (`dgSpan_one`). Composing the four spans (`dgSpan_add`) gives $k+1+k+1=2k+2$ steps and the claimed interval.

**Key facts.** `Turing.FinTM.dgSpan_generate_right`, `Turing.FinTM.dgSpan_mono`, `Turing.FinTM.sweep_turn_left`, `Turing.FinTM.dgSpan_one`, `Turing.FinTM.sweep_run_reverse`, `Turing.FinTM.dg_sweep_reverse_prefix`, `Turing.FinTM.sweepFold_id`, `Turing.FinTM.sweepRevCfg_write`, `Turing.FinTM.dgSpan_add`.
