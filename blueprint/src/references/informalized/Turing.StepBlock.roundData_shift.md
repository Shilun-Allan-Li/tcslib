<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.roundData_shift -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Shift of Round-Configuration Heads

**Claim.** Shifting the table and state head positions of a round configuration by $a$ and $b$ yields the round configuration with those head positions increased by $a$ and $b$.

**Proof.** Compare the configurations field by field. Their states, input positions, tape contents, and output lists are unchanged. For each of the first $k$ tapes, neither auxiliary shift applies, since these tapes are distinct from both the table and summary tapes (\texttt{mirror\_ne\_table} and \texttt{mirror\_ne\_summary}). On the table tape the shift adds $a$ and leaves the state-head offset unchanged; on the summary tape it adds $b$ and leaves the table-head offset unchanged. These are exactly the head positions specified by the round configuration on the right. Extensionality gives equality.

**Key facts.** `Turing.StepBlock.mirror_ne_table`, `Turing.StepBlock.mirror_ne_summary`.
