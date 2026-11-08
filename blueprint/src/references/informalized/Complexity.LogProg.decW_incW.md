<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/FragDec.lean :: Complexity.LogProg.decW_incW -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decrement After Increment

**Claim.** If $w$ is canonical, decrementing the word obtained by incrementing $w$ returns $w$.

**Proof.** Induct on $w$. The empty word is immediate. If $w$ begins with $0$, the singleton case would be noncanonical, since a nonempty canonical word must end in $1$. Thus there is a further tail, and increment changes only the leading $0$ to $1$; decrement changes it back and leaves the tail untouched. If $w$ begins with $1$, increment changes that bit to $0$ and recursively increments the tail. Decrement reverses this leading-bit change and applies to the recursively incremented tail. The tail is canonical by the fact that every tail of a canonical word is canonical (`canon_tail`), so the induction hypothesis reduces the tail to itself.

**Key facts.** `Complexity.LogProg.canon_tail`.
