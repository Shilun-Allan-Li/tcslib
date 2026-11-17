<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_body_depart -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Departure from the anchor

**Claim.** From the canonical seam configuration in administrative anchor state $0$, one step of the active body enters verification mode with source state $q_v$, preserving the candidate and leaving the last tape blank, with both endpoint heads at zero and output empty.

**Proof.** First identify the seam configuration with the word-based configuration having state $0$ and candidate $s$ on tape zero (\texttt{Complexity.enumCont_pair_words}). At anchor state $0$, the active body takes the control-action branch that enters the clean-call state carrying $q_v$ in mode $1$. The control-action formula changes the state and moves the input head according to its specified movement, while leaving work tapes, work-tape heads, and output unchanged (\texttt{Turing.FinTM.controlAction_apply}). Here the movement is zero, so the input-head position is also unchanged (\texttt{Turing.moveInputPos_zero}). Rewriting the resulting configuration in the canonical pair form gives the claimed verification-mode configuration.

**Key facts.** `Complexity.enumCont_pair_words`, `Turing.FinTM.controlAction_apply`, `Turing.moveInputPos_zero`.
