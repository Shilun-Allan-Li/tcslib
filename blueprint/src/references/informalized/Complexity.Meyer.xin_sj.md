<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerComplete.lean :: Complexity.Meyer.xin_sj -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Signed indexing of a Boolean list

**Claim.** For either direction flag and every natural index, the specified partial Boolean lookup agrees with the partial lookup of $x$ at the corresponding signed position.

**Proof.** Unfold the shifted lookup and the signed displacement, then split on the direction flag. In the nonnegative direction, the shifted position is $1+j$, whose list index is $j$. If $j<|x|$, the assumed agreement of $b$ and $x$ gives equality of the returned symbols; otherwise both lookups are undefined. In the negative direction, first consider $j=0$: the displacement is zero, so the lookup is at position $1$ and returns the first bit exactly when the list is nonempty, which agrees with the expression on the left. If instead $j>0$, the left side is undefined by its direction condition, and the shifted position $1-j$ is below $1$, so the right side is undefined as well.
