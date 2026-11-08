<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Nondeterministic.lean :: Turing.NDTM.moveInputPos_val -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of the Clamped Head Movement

**Claim.** The value of the head position after a clamped movement is the minimum of the natural-number result of adding the sign to the position in the integers and the upper boundary $N+1$.

**Proof.** Write $p$ for the natural number obtained by adding the sign to $q$ in the integers and converting the result to a natural number. By definition, the moved position is $p$ when $p<N+2$, and is the boundary position $N+1$ otherwise. In the first case, $p\le N+1$, so the minimum of $p$ and $N+1$ is $p$. In the second case, $p\ge N+2$, so that minimum is $N+1$. These are exactly the two values of the moved position.
