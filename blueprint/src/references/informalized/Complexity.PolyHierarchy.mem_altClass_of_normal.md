<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Normalize.lean :: Complexity.PolyHierarchy.mem_altClass_of_normal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Normal alternating class from polynomial data

**Claim.** The language defined by the stated first quantifier over blocks of length $\ell_1(y)$, followed by the depth-$i$ alternating condition with block length $\ell_2(y)$ on the transformed paired input, belongs to the alternating class at level $i+1$ with initial type $b$.

**Proof.** First use the unary polynomial bounds (`Complexity.PolyHierarchy.UnaryPT.bound`) to choose polynomial bounds for both $\ell_1$ and $\ell_2$. Set $B=(A_1+A_2+1)(|y|+1)^{a_1+a_2}$. The two bounds ensure that both block lengths are strictly less than $B$: the larger exponent dominates each original exponent, and the extra positive term in the coefficient leaves room for strict inequality.

Let $s$ be the canonical paired template for $y$ formed from the two unary blocks of lengths $\ell_1(y)$ and $\ell_2(y)$. Its decoded first and second components have precisely those lengths. The original first quantifier over length-$\ell_1(y)$ blocks can be replaced by a quantifier over length-$B$ blocks followed by decoding relative to the first template: every such padded block decodes to a block of the required length, and every required block has a length-$B$ padded representative by `Complexity.PolyHierarchy.exists_padDecode_eq`. The quantifier is preserved in either its existential or universal form by `Complexity.PolyHierarchy.qStep_transfer`.

For the remaining $i$ alternating levels, apply the transfer theorem (`Complexity.PolyHierarchy.altQuant_transfer`) using the decoder relative to the second template and the same padding argument. The map used in that transfer decodes each successive pair and applies $f$ at the base. Its compatibility with pair extension is exactly the recursive identity supplied by `Complexity.PolyHierarchy.tupleDecode_succ_pairEncode`. At a terminal word $z$ obtained by $i+1$ extensions from $y$, repeated projection of the first component recovers $y$ (`Complexity.PolyHierarchy.Extends.iterate_pairFstD`), with the one-step projection calculation given by `Complexity.pairFstD_pairEncode`. Hence the terminal membership condition for the preimage language agrees with the original predicate involving $f$ and the paired input.

It remains to verify that the chosen terminal language is polynomial-time decidable. The map used to define it is polynomial-time computable by `Complexity.PolyHierarchy.polyTimeComputable_nMap`, and taking its preimage of the polynomial-time language $V$ stays in polynomial time by `Complexity.preimage_mem_P`. The transferred quantifier equivalences therefore give exactly the required representation in the alternating class at level $i+1$.

**Key facts.** `Complexity.PolyHierarchy.UnaryPT.bound`, `Complexity.PolyHierarchy.exists_padDecode_eq`, `Complexity.PolyHierarchy.qStep_transfer`, `Complexity.PolyHierarchy.altQuant_transfer`, `Complexity.PolyHierarchy.tupleDecode_succ_pairEncode`, `Complexity.PolyHierarchy.Extends.iterate_pairFstD`, `Complexity.pairFstD_pairEncode`, `Complexity.PolyHierarchy.polyTimeComputable_nMap`, `Complexity.preimage_mem_P`.
