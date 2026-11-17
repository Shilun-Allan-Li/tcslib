<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/NP.lean :: Complexity.verifier_split_bridge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality of split searches

**Claim.** For every $C,c\in\mathbb{N}$, the least-solution searches defining the two partial functions are equal.

**Proof.** The two searches range over the same candidates $i\le m$. After substituting $C+1$ for the coefficient in the first search, its tested equation is $i+(C+1)(i+1)^c=m$, exactly the equation tested by the second search. Therefore both return the same least candidate when one exists, and both are undefined when none exists.
