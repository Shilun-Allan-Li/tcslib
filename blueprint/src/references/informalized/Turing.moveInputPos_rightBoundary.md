<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Configuration.lean :: Turing.moveInputPos_rightBoundary -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Right Boundary Move

**Claim.** Moving right from the rightmost allowed position $n+1$ with clamping leaves the position at $n+1$.

**Proof.** Adding one to the rightmost value $n+1$ gives $n+2$, which is outside the allowed range of values less than $n+2$. The clamping rule therefore returns the rightmost allowed position, $n+1$.
