<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/VWord.lean :: Complexity.drop_add_of_drop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successive List Drops

**Claim.** If dropping the first $p$ entries of $x$ leaves $u$ followed by $r$, then dropping the first $p+|u|$ entries of $x$ leaves $r$.

**Proof.** Dropping $p$ entries and then dropping $|u|$ more is the same as dropping $p+|u|$ entries in one step. By hypothesis, the first drop leaves $u$ concatenated with $r$. Dropping the first $|u|$ entries of this concatenation removes exactly $u$, leaving $r$.
