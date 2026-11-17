<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/Relativization.lean :: Complexity.stage_later -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Growth of Later Stage Lengths

**Claim.** For $i<j$, the fresh lengths satisfy $n_i^i+i<n_j$ and $n_i<n_j$.

**Proof.** Since $i<j$, we have $i+1\le j$. Monotonicity of the stage bounds therefore gives that the bound at stage $i+1$ is at most the bound at stage $j$. The successor-stage formula identifies the former bound as the maximum of $n_i$ and $n_i^i+i$, so it is at least each of those quantities. The fresh-length property at stage $j$ says that $n_j$ is strictly greater than the stage-$j$ bound. Combining these inequalities gives both $n_i^i+i<n_j$ and $n_i<n_j$.

**Key facts.** `Complexity.stage_bound_mono`, `Complexity.stage_bound_succ`, `Complexity.freshLen_spec`.
