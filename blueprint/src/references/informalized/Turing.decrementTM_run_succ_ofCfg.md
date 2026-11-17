<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean :: Turing.decrementTM_run_succ_ofCfg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decrementing a non-underflowing word

**Claim.** Under the stated hypotheses, the decrement machine processes the non-underflowing word $w$ in $2|(w\text{ begins with false})|+2$ steps, reaches the done phase with flag true, writes the decremented word $v$ in the indicated cells, and satisfies the asserted earlier-state and head-position bounds.

**Proof.** Complement every bit of the word, obtaining $w.map\ not$. The decrement operation is related to increment on this complemented word: the complement identity for fixed-width counters says that decrementing $w$ produces $v$ exactly when incrementing the complemented word produces the complement of $v$ (`counter_dec_complement`). Likewise, complementing the tape contents changes the buffer for $w$ into the buffer for the complemented word (`counter_buffer_complement`). Therefore the complemented initial configuration satisfies the hypotheses of the increment run theorem, with the same initial run phase. Apply the increment theorem: after twice the number of leading true bits of the complemented word, plus two steps, it reaches the done phase with true flag, writes the complemented result, does not reach a done phase earlier, and obeys the head bounds. Leading true bits of the complemented word are exactly leading false bits of $w$, so the time and bounds agree. Finally, translate the resulting run back through bit complementation using the decrement-run correspondence (`counter_decrement_run`); the written symbols become $v$, and the earlier-state and head-position conclusions transfer as well.

**Key facts.** `Turing.counter_dec_complement`, `Turing.counter_buffer_complement`, `Turing.incrementTM_run_succ_ofCfg`, `Turing.counter_decrement_run`.
