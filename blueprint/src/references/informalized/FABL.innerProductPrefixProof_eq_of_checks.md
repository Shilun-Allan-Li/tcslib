<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.innerProductPrefixProof_eq_of_checks -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prefix values determined by linear checks

**Claim.** If all the specified linear checks hold, then for every $k\le m$ the proof bit at prefix index $k$, interpreted in $\mathbb{F}_2$, equals the sum of the products of the first $k$ paired input bits.

**Proof.** Proceed by induction on the prefix index $k$. At index zero, the endpoint check says the proof bit is false; its image in $\mathbb{F}_2$ is zero (`pcppBoolF₂Equiv_false`), which is the empty prefix sum. For the successor step, take an index $i<m$ and assume the claim at $i$. The product check says that the proof bit stored at the product position is the conjunction of the two input bits in pair $i$; converting this Boolean equality to $\mathbb{F}_2$ identifies that proof bit with the pair product (`pcppBoolF₂Equiv_and`). The recurrence check says that the next prefix proof value is the current prefix value plus this product. Substituting the induction hypothesis and the product identification, the next value is the current prefix sum plus pair $i$. The prefix recurrence (`innerProductPrefixBit_succ`) identifies this with the prefix sum through $i+1$, completing the induction.

**Key facts.** `FABL.pcppBoolF₂Equiv_false`, `FABL.pcppBoolF₂Equiv_and`, `FABL.innerProductPrefixBit_succ`.
