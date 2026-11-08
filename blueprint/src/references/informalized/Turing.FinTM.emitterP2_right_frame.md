<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterP2_right_frame -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Frame for a Relocated Length Call

**Claim.** Embedding the length-call configuration into the host and renaming its state produces exactly the host configuration with candidate $s$, width word $u$, suffix-length word $v$, input head at $1$, all work heads at zero, and empty output.

**Proof.** Apply the frame-identification result `emitterP2_frame`, which reduces equality of the configurations to checking the state, input position, output, the tapes and heads selected by the embedding, and the unselected host tapes. The state maps from $q$ to $e(q)$, the input head remains at $1$, and both outputs are empty. The embedded tape bank is the right-hand bank of the host: its selected tape assignments agree with the corresponding entries of the host layout, and their heads are all zero. On the remaining host positions, the provided background assignment is exactly the host's candidate-and-width layout, with zero head positions. These componentwise equalities establish the claimed frame.

**Key facts.** `Turing.FinTM.emitterP2_frame`.
