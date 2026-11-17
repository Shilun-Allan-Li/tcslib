<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalStartup.lean :: Turing.universalInput_move -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Virtual Input-Head Motion

**Claim.** Under the suffix embedding, the virtual move makes the paired-input head reach the embedding of the original machine's clamped destination, and the original head position plus the virtual move equals that destination position.

**Proof.** The marker tape determines a valid boundary tag at every input-head position (`Turing.universalInput_tag`). The correctness property of virtual motion says that, after subtracting the one-unit shift used in the tag convention, the moved position is the original clamped destination (`Turing.FinTM.virtualMove_correct`). Restoring that shift gives the integer identity between the current position plus the virtual move and the destination position. The paired input has length $2|\alpha|+2+|x|$ (`Turing.universal_pair_length`), and the embedding adds the fixed offset $2|\alpha|+2$. Hence the embedded current coordinate plus the virtual move equals the embedded destination coordinate. The definition of clamped input movement then gives equality of the corresponding finite positions as well.

**Key facts.** `Turing.FinTM.virtualMove_correct`, `Turing.universalInput_tag`, `Turing.universal_pair_length`.
