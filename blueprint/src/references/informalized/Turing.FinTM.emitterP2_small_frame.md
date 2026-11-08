<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterP2_small_frame -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Frame for Relocated Preparation

**Claim.** Embedding the three-tape preparation configuration into the host and renaming its state gives the host frame with the full candidate, width, and suffix-length word layout, input head at $1$, zero work heads, and empty output.

**Proof.** Use `emitterP2_frame` to reduce equality of configurations to componentwise checks. The embedded state is $(q,o)$, which the state map sends to $e(q,o)$; input head and output already agree with the target. For the three embedded tapes, the small embedding places the preparation machine's tapes at the host positions reserved for the candidate, width, and suffix-length words. Their tape contents and zero head positions therefore match the corresponding entries in the full host layout. Every position outside this embedded triple is blank in the supplied background frame and has head zero. Since the width and suffix words are assigned only to the first position of their respective banks, all other positions in those banks are blank; `bufferTape_nil` supplies the blank tape function for the empty assignments. Thus the selected and unselected tape data match everywhere, proving the frame equality.

**Key facts.** `Turing.FinTM.emitterP2_frame`, `Turing.FinTM.bufferTape_nil`.
