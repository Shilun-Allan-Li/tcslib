<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Configuration.lean :: Turing.moveInputPos_leftBoundary -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Left Boundary Move

**Claim.** Moving left from position $0$ while clamping to the allowed range leaves the position at $0$.

**Proof.** A left move adds $-1$ to position $0$, giving the integer $-1$. Converting this negative integer to a natural number yields $0$, which is already in the allowed range, so clamping does not change it. The resulting position is therefore $0.
