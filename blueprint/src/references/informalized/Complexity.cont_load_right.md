<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.cont_load_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Right-moving loader transition

**Claim.** Under the stated transition hypothesis, one machine step advances the loader to input position $i+2$, appends the optional bits to their buffers, and enters state $q'$.

**Proof.** First identify the symbol read by the loader at position $i+1$ with $y[i]?$, using the input-position lemma (`Complexity.cont_load_read`). The transition hypothesis then identifies the machine action as the specified right move, buffer writes, and state change. Applying this action has the effect described by the buffer-update lemma (`Complexity.cont_write_apply`): it appends each written optional bit to its buffer, moves the two buffer heads to the new right blanks, and leaves the third tape and output as prescribed. The input head moves one position to the right; since $i<|y|$, it is not already at the right boundary, so the right-move position formula gives position $i+2$ (`Turing.moveInputPos_pos_of_ne_right`). These configuration components together are exactly the claimed next loader configuration.

**Key facts.** `Complexity.cont_load_read`, `Complexity.cont_write_apply`, `Turing.moveInputPos_pos_of_ne_right`.
