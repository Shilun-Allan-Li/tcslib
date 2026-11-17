<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Inclusions.lean :: Randomized.mem_NP_of_inRP_polyTimeModel -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Sided Randomized Recognition Lies in NP

**Claim.** If a polynomial-time verifier accepts members with probability at least $2/3$ and never accepts nonmembers, then the language belongs to $\mathrm{NP}$.

**Proof.** 1. Choose the verifier $M$, its random-bit length parameters $a,k$, and polynomial-time languages $V_1,V_0$ witnessing its efficiency. By the verifier's acceptance characterization, $M(x,u)=\mathrm{true}$ exactly when the paired encoding of $x,u$ belongs to $V_1$. Construct a polynomial-time language that requires both this acceptance condition and a length condition: the second component of the decoded pair must have the same length as the unary string of length $a(|x|+1)^k$ derived from the first component. The closure of polynomial time under composition (`Complexity.PolyTimeComputable.comp`), the polynomial-time computability of the pair decoders and unary length map (`Complexity.polyTimeComputable_pairSndD`, `Complexity.polyTimeComputable_polyUnary`, `Complexity.polyTimeComputable_pairFstD`), the equal-length test (`Complexity.lenEq_preimage_mem_P`), and intersection closure (`Complexity.inter_mem_P`) show this language is in $P$.

2. If $x$ is a member, the acceptance probability is at least $2/3$, hence positive. Some random string of the prescribed length is therefore accepted (`Randomized.exists_ofFn_of_randProb_pos`). Using it as the NP witness makes the paired encoding pass the acceptance test; its prescribed length makes it pass the length test. The length-constrained NP characterization (`Complexity.mem_NP_iff_exists_length_le`) now gives the required witness.

3. Conversely, suppose a witness passes both tests. The length test forces its length to be exactly $a(|x|+1)^k$, since the relevant unary string has that length. Thus it is representable as a uniformly random bit string of precisely the verifier's random length (`Randomized.exists_ofFn_eq`). If $x$ were not in the language, the one-sided guarantee says every such random string is rejected. But passing the acceptance test means the verifier accepts this witness, a contradiction. Hence any input with a witness passing both tests belongs to the language, completing the NP characterization.

**Key facts.** `Complexity.polyTimeComputable_pairSndD`, `Complexity.polyTimeComputable_polyUnary`, `Complexity.polyTimeComputable_pairFstD`, `Complexity.PolyTimeComputable.comp`, `Complexity.lenEq_preimage_mem_P`, `Complexity.inter_mem_P`, `Complexity.mem_NP_iff_exists_length_le`, `Randomized.exists_ofFn_of_randProb_pos`, `Randomized.exists_ofFn_eq`.
