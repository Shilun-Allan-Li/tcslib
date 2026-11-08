<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPath.lean :: Complexity.symmetric_inEdge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symmetry of the encoded edge relation

**Claim.** Under the stated bit-symmetry condition, the encoded relation on vertices below $n$ is symmetric.

**Proof.** Take vertices $u,v<n$ and assume the encoded edge relation holds from $u$ to $v$. By definition, this means the bit at the index encoding $(u,v)$ is true. The hypothesis identifies that bit with the one encoding $(v,u)$, so the reverse edge holds as well. This is exactly symmetry of the relation.
