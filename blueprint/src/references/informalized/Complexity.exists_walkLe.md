<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathWalk.lean :: Complexity.exists_walkLe -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A finite bound for a reflexive transitive walk

**Claim.** If t is reachable from c by a finite sequence of relation steps whose endpoints lie below n, then some finite bound j witnesses a WalkLe from c to t.

**Proof.** Induct on the reflexive-transitive relation derivation. In the reflexive case c=t, and the zero-step relation `WalkLe E n 0 c t` holds. In the step case, the derivation begins with an edge c→v, with v<n and E(c,v), followed by a shorter derivation from v to t. By induction that remainder has some bound j. Increasing the bound to j+1 and placing the first edge in the recursive clause of `WalkLe` gives the desired bounded walk.
