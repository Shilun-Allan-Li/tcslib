<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedCaptured_frame -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Interpreter Entry as a Frame

**Claim.** Under the stated buffer-content and buffer-head hypotheses, the interpreter-entry capture configuration equals the frame over the source tapes and heads of the lifted stopped interpreter entry configuration, using the source input-head position and output table together with the clock word.

**Proof.** Compare the two configurations field by field. Their states and input-head positions agree by construction, as do their external outputs. For tape contents and head positions, split the frame's indices into the source-tape block and the five added lanes. On source tapes other than the designated clock tape, both sides retain the source contents and heads. On the clock tape, the hypotheses identify the source contents with the buffer for the clock word and its head with that word's length, exactly the clock lane supplied by the lifted interpreter entry. The remaining added lanes agree directly: the table lane stores the source output with its head at the output length, and the other lanes are blank with heads at zero. These comparisons establish equality of the configurations.
