<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_body_check -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Increment-result branch check

**Claim.** From administrative state $4$, the body machine preserves the tape and head configuration and moves to anchor state $0$ exactly when the last tape is empty; otherwise it moves to state $5$.

**Proof.** At the given pair configuration, the reading at the last tape's head is the first symbol of $v$, if present, and is blank exactly when $v$ is empty. The transition from administrative state $4$ therefore selects the anchor in the empty case and state $5$ in the nonempty case. In either branch it is a control action: it changes only the state and input-head position. Since its input-head movement is zero, that position is unchanged, and the work-tape actions make no writes or head movements. Thus the entire remaining configuration is preserved.

**Key facts.** `Turing.FinTM.controlAction_apply`, `Turing.moveInputPos_zero`.
