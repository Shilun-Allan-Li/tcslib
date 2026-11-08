<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/InputCall.lean :: Turing.inputSeek_right_value -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rightward Input Head Position

**Claim.** If $p+r\le n+1$, then $r$ successive clamped rightward moves from position $p$ end at position $p+r$.

**Proof.** Induct on $r$. The case $r=0$ is immediate. For the successor case, the induction hypothesis gives position value $p+r$. The assumed bound $p+(r+1)\le n+1$ ensures that this value is strictly below the right boundary $n+1$. Consequently the next clamped rightward move increases the position by exactly one, by the right-move value formula (`Turing.moveInputPos_pos_of_ne_right`). The resulting value is $p+r+1$, as required.

**Key facts.** `Turing.moveInputPos_pos_of_ne_right`.
