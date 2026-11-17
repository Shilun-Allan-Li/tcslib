<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterP2_prepare_candidate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Candidate Copying Prefix

**Claim.** For each $j\le |s|$, the first $j$ steps of the preparation run produce the stated frame: the first $j$ symbols of $s$ have been copied, the other specified tapes and heads have their claimed values, and the input position and overflow flag record whether the input has been exhausted before $j$.

**Proof.** Proceed by induction on $j$. At $j=0$, the initial frame is the asserted one: no symbols have been copied, the overflow flag is false, and the input head is at the position corresponding to zero consumed symbols. For the successor step, assume the asserted frame at $j$ and use that $j<|s|$. The input-reading lemma says that the symbol read at the split position is the $j$th input symbol when $j<|w|$, and is blank otherwise (Turing.FinTM.splitPos_read). The transition copies the current symbol from the candidate tape to the second tape and moves the two relevant heads one position forward. The overflow flag, previously recording $|w|<j$, is updated by whether the current input reading is blank; this is equivalent to $|w|<j+1$. The tape update writes $s[j]$ at position $j$: the length of $s$ truncated to its first $j$ symbols is $j$, and appending the next symbol is exactly the update at that position, by the buffer-append identity and the natural-index evaluation rule (Turing.FinTM.bufferTape_append; Turing.FinTM.bufferTape_nat). Finally, the input head advances to the position for $j+1$ symbols consumed (Turing.FinTM.splitPos_succ), and the other tape and head fields follow directly from the transition. This gives the claimed frame at $j+1$.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.splitPos_read`, `Turing.FinTM.bufferTape_append`, `Turing.FinTM.bufferTape_nat`, `Turing.FinTM.splitPos_succ`.
