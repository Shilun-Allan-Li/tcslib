<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRec_stop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exhausted Clock Dispatches to Completion

**Claim.** When the recorder is at its clock-test control with logical time $T$, one step sends it to the completion control, preserving the encoded source configuration, counts, record, and time.

**Proof.** At logical time $T$, the clock tape contains exactly the $T$ true bits placed there initially, and its head has advanced to the first blank cell. Thus the symbol scanned at the clock index is blank. The recorder's transition rule for the clock-test control sends this case to the completion control and leaves the other tapes unchanged. This is a control action with zero input-head movement; zero movement preserves the input-head position (`moveInputPos_zero`). Hence the resulting configuration has the stated completion control and retains the encoded data and time.

**Key facts.** `Turing.FinTM.controlAction_apply`, `Turing.moveInputPos_zero`.
