<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.summaryEmit_other -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Emitting from a False Summary

**Claim.** Combining the summary value false with any optional Boolean value returns the summary value false.

**Proof.** If the emitted value is absent, the definition retains the existing summary, namely false. If it is present, whether true or false, the definition returns false. Thus every case gives the claimed result.
