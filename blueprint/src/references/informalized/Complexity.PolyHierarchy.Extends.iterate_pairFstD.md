<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Normalize.lean :: Complexity.PolyHierarchy.Extends.iterate_pairFstD -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovery from Iterated Extensions

**Claim.** If a string $z$ is obtained from $w$ by $k$ successive extensions, each replacing a string by its pair encoding with another binary string, then applying the total first projection to $z$ exactly $k$ times returns $w$.

**Proof.** Proceed by induction on the number of extensions. With zero extensions, $z=w$, so zero applications of the projection leave it unchanged. For $k+1$ extensions, the definition gives a string $v$ such that $z$ is obtained by $k$ extensions from the pair encoding of $w$ and $v$. By the induction hypothesis, $k$ projections of $z$ recover that pair encoding. One further projection recovers $w$, because the total first projection sends the pair encoding of any two strings to its first component (\texttt{pairFstD\_pairEncode}).

**Key facts.** `Complexity.pairFstD_pairEncode`.
