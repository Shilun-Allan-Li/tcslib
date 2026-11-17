<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Normalize.lean :: Complexity.PolyHierarchy.mem_altClass_of_uniform -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform alternating class

**Claim.** If $V$ is in polynomial time, $f$ is polynomial-time computable, and the unary representation of $\ell$ is polynomial-time computable, then the language of inputs $y$ for which the depth-$i$ alternating condition over $V$ with block length $\ell(y)$ holds on $f(y)$ belongs to the alternating class at level $i$ with initial type $b$.

**Proof.** Split on the level. At level zero, the language is the preimage of $V$ under $f$, so it lies in polynomial time by the preimage closure result (`Complexity.preimage_mem_P`). The zero-level characterization of the alternating class (`Complexity.altClass_zero`) then gives the claim.

For a positive level, write it as $i+1$. The successor characterization of the alternating condition (`Complexity.altQuant_succ`) exposes its first quantifier: it ranges over a block $U$ of length $\ell(y)$, and the remaining depth-$i$ condition is evaluated on the pair encoding of $y$ and $U$. To put this in the normal form, transform a general input $p$ by decoding its first and second components, applying $f$ to the first, and pair-encoding the result with the second. This transformation is polynomial-time computable: the projections are polynomial-time computable (`Complexity.polyTimeComputable_pairFstD`, `Complexity.polyTimeComputable_pairSndD`), and composition and pair encoding preserve polynomial-time computability (`Complexity.PolyTimeComputable.comp`, `Complexity.PolyTimeComputable.pairEncode`). Apply the normal-form membership theorem (`Complexity.PolyHierarchy.mem_altClass_of_normal`) with both block-length functions equal to $\ell$. Its defining quantifier and paired input then coincide with the successor characterization above, yielding membership at level $i+1$.

**Key facts.** `Complexity.altClass_zero`, `Complexity.preimage_mem_P`, `Complexity.PolyHierarchy.mem_altClass_of_normal`, `Complexity.polyTimeComputable_pairFstD`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.PolyTimeComputable.comp`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.altQuant_succ`.
