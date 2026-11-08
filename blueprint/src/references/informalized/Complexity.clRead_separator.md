<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRead_separator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Consuming the separator

**Claim.** Starting at the separator `false,true` in scanning control with target head at $|w|$, after two steps the reader enters rewind control, leaves the stream unchanged, advances the stream head by two, and moves the target head to $|w|-1$.

**Proof.** At the first separator position the stream buffer is `false`. The reader stores this bit and advances the stream head, leaving the target unchanged. The next stream symbol is `true`, which does not match the stored `false`; this mismatch sends the reader into rewind control and moves the target head left once. The stream itself is never written, so it remains unchanged, and the stream head has advanced twice. The target head is therefore at $|w|-1$, with natural subtraction as stated. The two buffer values follow from `FinTM.bufferTape_nat` and list indexing at the two positions. The two-step run is expanded using `runFrom_succ_eq_step'` and `runFrom_zero`; the input head remains fixed by `moveInputPos_zero`.

**Key facts.** `Turing.FinTM.bufferTape_nat`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.moveInputPos_zero`.
