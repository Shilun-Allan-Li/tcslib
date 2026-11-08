<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clReplay_forward -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Forward Replay of a Buffer Suffix

**Claim.** For every $j\le |w|$, starting in the emitting state with buffer $w$, head at $j$, and output $out$, the replay machine halts after $|w|-j+1$ steps with head at $|w|$ and output $out$ followed by the suffix of $w$ beginning at $j$.

**Proof.** Induct on the remaining distance $|w|-j$, generalizing $j$. If the distance is zero, then $j=|w|$. One transition in the emitting state halts without moving the head or changing the output; the subsequent zero-step run is the identity (`runFrom_zero`). This gives the stated one-step result, with the suffix at $j=|w|$ empty. If the remaining distance is positive, then $j<|w|$, so the buffer at the head contains $w[j]$ (`bufferTape_nat` and the list-index identity). The emitting transition appends this bit to the output and advances the head to $j+1$, leaving the buffer intact. Decompose off that first transition (`runFrom_succ_eq_step`) and apply the induction hypothesis to the shorter remaining distance and the updated output. The identity $w.drop\,j=[w[j]]\mathbin{++}w.drop(j+1)$ shows that the bits appended over the run are exactly the requested suffix.

**Key facts.** `Turing.FinTM.bufferTape_nat`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
