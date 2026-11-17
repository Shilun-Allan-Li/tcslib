<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_lift_call -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lifting a computation to a larger tape bank

**Claim.** If the larger machine simulates each transition of the smaller machine at embedded states, using the corresponding initial block of work tapes and padding the remaining tapes, then a halted computation of the smaller machine from the specified initial tape contents is reproduced at the same time with the same output.

**Proof.** The word-configuration identity (`Complexity.enumCont_pad_words`) identifies the padded encoding of the smaller machine's initial configuration with the larger machine's configuration having the same word on its first tape and blank remaining tapes. The step-by-step padding simulation (`Complexity.enumCont_pad_run`), applied for $T$ steps, then identifies the larger run with the padded encoding of the smaller run at time $T$. In that padded configuration, the state is the image of the smaller machine's state and the output is unchanged. Since the smaller machine is halted with output $y$, its state is none and its output is $y$; mapping none leaves it none. This proves both required conclusions.

**Key facts.** `Complexity.enumCont_pad_words`, `Complexity.enumCont_pad_run`.
