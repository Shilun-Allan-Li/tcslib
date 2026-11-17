<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_body_reject -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rejection transition

**Claim.** From control state $3$ with false on the last tape, the body machine enters the increment-call state $(q_i,2)$, preserves the first tape, and blanks the last tape, leaving the endpoint heads at zero and all other fields unchanged.

**Proof.** The last tape is read at position zero, where it contains false. Thus the transition from state $3$ takes the non-true branch: it writes blank at the last tape's current cell and enters the clean-call state $(q_i,2)$. The tape representation of a word as a buffer function is handled by expressing $[\mathrm{false}]$ as the empty word followed by its last symbol; the buffer-append identity shows that overwriting that cell with blank makes the whole tape blank (\texttt{Turing.FinTM.bufferTape_append}). Applying the action leaves the input head fixed because its movement is zero (\texttt{Turing.moveInputPos_zero}); the componentwise configuration check then gives the preserved first tape, blank last tape, unchanged other tapes and fields, and endpoint heads still at zero.

**Key facts.** `Turing.FinTM.bufferTape_append`, `Turing.moveInputPos_zero`.
