<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.incrementTM_run_overflow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Overflow Run of the Increment Machine

**Claim.** If incrementing the selected tape's word overflows, the machine reaches the done phase with false verdict within $2|w_i|+2$ steps, with no earlier done phase, and the selected tape then stores $|w_i|$ false bits.

**Proof.** Apply the arbitrary-configuration overflow run result (`incrementTM_run_overflow_ofCfg`) to the configuration storing the family of words. Its hypotheses hold because this configuration starts in the run phase and its selected tape agrees with the buffer for $w_i$ at every relevant position. The result gives the run at exactly $2|w_i|+2$, the absence of either done phase at every earlier time, and the false verdict. Specializing the tape-content description to this initial configuration shows that the selected tape now stores the all-false word of length $|w_i|$; all other tape contents agree with the original family. Taking this time as $T$ gives the stated bound with equality.

**Key facts.** `Turing.incrementTM_run_overflow_ofCfg`.
