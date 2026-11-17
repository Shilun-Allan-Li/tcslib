<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.compValues_update -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating a coordinate of the value vector

**Claim.** Updating the value vector at coordinate $r$ to $v$ replaces the entry at $r$ by $v$ and leaves every other coordinate unchanged, as expressed by the displayed vector.

**Proof.** By definition, function update assigns the new value $v$ at the chosen coordinate and preserves the original function at every other coordinate. The vector’s coordinate list is $(p,n,a,w,b,q,t,c,x,s,i,y,l,j)$, indexed from $0$ through $13$. Thus each listed entry remains unchanged unless its index equals $r$, in which case it is replaced by $v$, giving the displayed vector.
