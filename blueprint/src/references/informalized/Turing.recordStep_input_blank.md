<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordStep_input_blank -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Blank Input Positions

**Claim.** The input symbol read by a configuration is absent exactly when its input head is at the left boundary, position $0$, or the right boundary, position $|x|+1$.

**Proof.** If the head is at position $0$, the definition of the input symbol returns `none` immediately. If it is not at $0$ but is at $|x|+1$, the second boundary clause returns `none`. Conversely, suppose the head is at neither boundary. Its position is then positive and strictly below $|x|+1$, since it is a valid position in a `Fin (|x|+2)`. Thus the input index one less than the head position lies within the word. The input-symbol definition therefore returns that word entry, as also expressed by the interior-position fact `inputSymbolInner`; a `some` value cannot equal `none`.

**Key facts.** `Turing.inputSymbolInner`.
