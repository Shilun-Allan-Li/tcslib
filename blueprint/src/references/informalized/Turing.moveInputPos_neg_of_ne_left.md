<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Configuration.lean :: Turing.moveInputPos_neg_of_ne_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Left Move Away from the Boundary

**Claim.** If $p$ is a position other than $0$, moving left with clamping gives position $p-1$.

**Proof.** Since $p\ne0$, its natural-number value is positive. Adding $-1$ to that value as an integer therefore gives the natural number $p-1$. This is within the allowed range, so the clamping rule selects it, as claimed.
