<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Padding.lean :: Complexity.PolyHierarchy.splitAtLastTrue_marker -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Splitting at a marked final true bit

**Claim.** For every Boolean word $u$ and natural number $k$, splitting $u$ followed by a true bit and then $k$ false bits at its last true bit returns $u$.

**Proof.** Reversing the word gives $k$ false bits followed by a true bit and then the reverse of $u$. Dropping the initial run of false bits therefore leaves exactly that true bit followed by the reverse of $u$ (`Complexity.PolyHierarchy.dropWhile_replicate_false`). The split operation reverses the remaining tail, recovering $u$.

**Key facts.** `Complexity.PolyHierarchy.dropWhile_replicate_false`.
