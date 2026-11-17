<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncHash.lean :: CommunicationComplexity.Functions.Hash.collision_mem_iUnion -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Collision event decomposition

**Claim.** The event that $x$ and $y$ receive the same hash is the union, over all possible values $a$, of the pieces where both hash values equal $a$.

**Proof.** If $h(x)=h(y)$, choose their common value $a=h(x)$. At coordinate $x$ and at coordinate $y$, the function then takes the specified value $a$, while every other coordinate is unrestricted, so $h$ belongs to the collision piece for $a$. Conversely, membership in any collision piece forces both $h(x)$ and $h(y)$ to equal its indexing value $a$, and therefore they are equal. These two inclusions prove the decomposition.
