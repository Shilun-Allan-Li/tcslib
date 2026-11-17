<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.b2_verify_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Relocated Verifier Step

**Claim.** A single host step under any choice bit simulates one step of a live verifier configuration, updates the boundary tag correctly, and leaves the scheduler data unchanged.

**Proof.** Since the verifier configuration is live, write its state as $q$, and let $a$ be the action selected by the verifier from state $q$, its current input symbol, and its work-tape symbols. Let $m$ be the virtual input movement obtained from $a$'s movement and the current boundary tag. The virtual-movement correctness fact (`Turing.FinTM.virtualMove_correct`) says both that this movement produces the same shifted head position as the verifier's attempted move, and that the tag updated by the prescribed rule is correct at the new position. The host's input buffer presents exactly the verifier's current input symbol (`Turing.FinTM.bufferTape_inputSymbol`), and its verifier work tapes present exactly the verifier's work-head symbols; these identifications follow by unpacking the slot arrangement. Consequently the host transition in verifier phase selects the same action data as $a$. Its action leaves the input head on the host input fixed, since the host input movement is zero (`Turing.moveInputPos_zero`), while its virtual input head moves by $m$. On the work tapes, the verifier's tapes and head positions are updated as in $a$; the scheduler tapes and heads stay fixed. If $a$ emits a bit, the host writes it to the output buffer and advances that buffer's head, and the summary is updated to represent the verifier's enlarged output (`Complexity.captureEmission_correct`); the buffer update is exactly the one-cell append identity (`Turing.FinTM.bufferTape_append`). If no bit is emitted, the output buffer and summary are unchanged. These componentwise identities give the encoded successor configuration, together with the correct updated tag.

**Key facts.** `Turing.FinTM.virtualMove_correct`, `Turing.FinTM.bufferTape_inputSymbol`, `Complexity.captureEmission_correct`, `Turing.FinTM.bufferTape_append`, `Turing.moveInputPos_zero`.
