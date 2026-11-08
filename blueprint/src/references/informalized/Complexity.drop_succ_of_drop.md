<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/VWord.lean :: Complexity.drop_succ_of_drop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successive list drop

**Claim.** If dropping the first $p$ entries of $x$ gives $b::r$, then dropping the first $p+1$ entries gives $r$.

**Proof.** The list identity that dropping one more entry is the same as taking the tail after the first drop gives $x.drop(p+1)=(x.drop(p)).tail$. Substituting the hypothesis $x.drop(p)=b::r$, the tail is $r$, as required.
