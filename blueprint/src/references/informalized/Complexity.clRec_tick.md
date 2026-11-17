<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRec_tick -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clock-Test Transition

**Claim.** When the clock-test phase sees a true symbol at clock position $t<T$, one recorder step advances the clock head to $t+1$ and enters the source-release phase, leaving the other configuration data unchanged.

**Proof.** The clock tape contains a block of $T$ true symbols, so $t<T$ ensures that its cell at position $t$ contains `true`. The clock-test transition therefore takes its successful branch: it moves the clock head one cell to the right and changes the phase to source-release, retaining the source state and tag. Its action makes no other tape writes or head movements, produces no output, and makes no input-head movement. Applying the action thus preserves the tapes and all other head positions; the input position is unchanged because a zero input movement fixes it (`moveInputPos_zero`). The clock head, previously at $t$, is now at $t+1$, giving exactly the stated recorder configuration.

**Key facts.** `Turing.moveInputPos_zero`.
