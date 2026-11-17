<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Expanders/Basic.lean :: Expander.uniform_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinates of the Uniform Vector

**Claim.** For every natural number $n$ and index $i\in\text{Fin}(n)$, the $i$th coordinate of the uniform vector is $(n: \mathbb{R})^{-1}$.

**Proof.** The uniform vector is defined as the function on the index set whose every value is the real reciprocal of $n$. Evaluating that function at $i$ gives the stated coordinate.
