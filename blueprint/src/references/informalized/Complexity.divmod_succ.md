<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathWalk.lean :: Complexity.divmod_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Division of a Successor

**Claim.** For positive $n$, incrementing $i$ either carries one unit into the quotient when the remainder reaches $n$, or leaves the quotient fixed and increments the remainder.

**Proof.** Write $i=nq+r$ with $q=i/n$ and $r=i\%n$, using the division algorithm. In the first case, the hypothesis says $r+1=n$, so $i+1=n(q+1)+0$. In the second case, $r+1\ne n$; since $r<n$, this gives $r+1<n$, and $i+1=nq+(r+1)$. In both cases the displayed quotient and remainder follow from uniqueness of quotient and remainder for a positive divisor.
