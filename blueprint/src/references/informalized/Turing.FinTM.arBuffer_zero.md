<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean :: Turing.FinTM.arBuffer_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empty read buffer

**Claim.** After zero reading steps, every buffer entry on every tape is blank.

**Proof.** At depth zero, no block position satisfies the condition that its value is less than zero. Thus the buffer definition selects its blank value at every tape and position.
