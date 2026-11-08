<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/EmitIterBody.lean :: Turing.copy_end -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Step of the Emission Loop

**Claim.** From the specified copy configuration, the emission-loop machine takes one step to the rewind-tape configuration with input head at $|x|+1$, first work-tape head at $|x|-1$, and all other components as stated.

**Proof.** The input head is at the position corresponding to the end of $x$, so the input symbol there is absent, by the input-symbol-at-position fact (Turing.FinTM.inputSymbol_at). Thus the copy-state transition takes its end-of-input branch: it enters the rewind-tape state, leaves the input head fixed, and moves the first work-tape head one cell left, leaving all other work tapes and the output unchanged. The zero-movement fact for the input head (Turing.moveInputPos_zero) confirms that its position remains $|x|+1$. On the first tape, the stored word is $x$ because the copied prefix has length $|x|$; the other tapes remain blank. Comparing the configuration components yields the claimed equality.

**Key facts.** `Turing.FinTM.inputSymbol_at`, `Turing.moveInputPos_zero`.
