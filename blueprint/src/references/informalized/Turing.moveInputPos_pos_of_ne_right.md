<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Configuration.lean :: Turing.moveInputPos_pos_of_ne_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Right Move Away from the Boundary

**Claim.** If $p$ is not the rightmost position $n+1$, moving right with clamping gives position $p+1$.

**Proof.** Because $p$ lies in the range of $n+2$ positions and is not $n+1$, its value satisfies $p<n+1$. Adding one therefore gives $p+1<n+2$, so this value remains within the allowed range. The clamping rule consequently returns $p+1$.
