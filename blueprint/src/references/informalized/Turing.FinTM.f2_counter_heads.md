<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_counter_heads -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counter Work-Tape Head Bound

**Claim.** For every Boolean list $x$, every natural time $u$, and the sole work tape, the counter machine's head position after $u$ steps lies between $-2(\mathrm{size}(|x|)+1)$ and $2(\mathrm{size}(|x|)+1)$.

**Proof.** Use the counting-with-space result at $i=|x|$ to reach, at some time $t$, the state-$0$ configuration whose tape contains $|x|. One more step enters state $3$ with the work-tape head at $0$; this is the state-$0$ transition when the input head is at the end of the input. From there, the output procedure halts after $|x.bits|+1$ further steps (`f2_counter_emit`), so let $T$ be this halting time. For any time $v\le T$, if $v\le t$, use the earlier-time bound supplied by `f2_counter_count_space`. Otherwise, split the run at time $t+1` and apply the one-cell-per-step head-motion bound (`f2_head_steps`) from the head position $0$. The remaining duration is at most the binary representation length plus one; the identity between that length and the size (`Nat.size_eq_bits_len`) makes this fit inside the stated interval. For a time $u>T$, the machine has already halted, so its configuration remains fixed (`runFrom_of_halt`), and its head position equals the position at time $T$, which is bounded by the preceding argument. Run composition (`runFrom_add`) justifies the splits, and `runFrom_succ_eq_step'` gives the single transition into the output phase.

**Key facts.** `Turing.FinTM.f2_counter_count_space`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.f2_counter_emit`, `Turing.FinTM.f2_head_steps`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_of_halt`.
