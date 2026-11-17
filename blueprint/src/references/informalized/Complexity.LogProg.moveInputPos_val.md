<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Layout.lean :: Complexity.LogProg.moveInputPos_val -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input-Head Movement Formula

**Claim.** For $p<N+2$, the value of the resulting position after moving by sign $m$ is $p$ for a zero move, $\min(p+1,N+1)$ for a positive move, and $p-1$ for a negative move.

**Proof.** Consider the three possible movement signs. By definition, the new position is obtained by adding the sign, viewed as an integer, to $p$, converting the result to a natural number, and truncating at the largest allowed position $N+1$ if necessary. For a zero move this gives $p$, which is already in range. For a positive move the candidate is $p+1$: if it is still below $N+2$, that is the resulting value; otherwise the position is capped at $N+1$. Together these cases give $\min(p+1,N+1)$. For a negative move, the candidate is $p-1$; the condition $p<N+2$ alone permits $p=0$, but the integer-to-natural conversion then yields zero, also equal to truncated subtraction $p-1$. Thus the result is $p-1$ in natural-number subtraction.
