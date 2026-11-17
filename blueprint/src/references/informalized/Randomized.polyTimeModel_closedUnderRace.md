<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PolyTimeModel.lean :: Randomized.polyTimeModel_closedUnderRace -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Closure Under Sequential Race

**Claim.** For every pair of Boolean predicates $M_1,M_2$ and natural numbers $a,k$, if the verifiers associated to both predicates are efficient in the model, then the verifier that applies $M_1$ to the first $a(|x|+1)^k$ bits of $r$, returns true if that accepts, and otherwise applies $M_2$ to the remaining suffix and returns false if that accepts (returning no answer if it does not) is efficient in the model.

**Proof.** Let $V_1,V_2$ be the polynomial-time languages witnessing the true answers of $M_1,M_2$. Use the preimage of $V_1$ under the function that keeps $x$ and truncates $r$ to the prescribed prefix as the race's true-language. This language is polynomial-time by closure under polynomial-time preimages and the prefix-truncation result (Complexity.preimage_mem_P and Randomized.polyTimeComputable_sliceTake). For false answers use the intersection of the complement of that first language with the preimage of $V_2$ under the corresponding suffix function. This too is polynomial-time, by complement and intersection closure and polynomial-time computability of suffix extraction (Complexity.compl_mem_P, Complexity.inter_mem_P, Complexity.preimage_mem_P, and Randomized.polyTimeComputable_sliceDrop).

On an encoding of $(x,r)$, decoding recovers both components. The pair-decoding identities show that membership in the first preimage is equivalent to $M_1$ accepting the prescribed prefix. Membership in the second preimage is equivalent to $M_2$ accepting the remaining suffix. The race returns true precisely in the first case; it returns false precisely when the first case fails and the second succeeds. If neither succeeds it returns no answer, so neither witness language contains the encoding. These cases give the model's true- and false-language equivalences.

**Key facts.** `Randomized.polyTimeComputable_sliceTake`, `Complexity.preimage_mem_P`, `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`, `Complexity.compl_mem_P`, `Randomized.polyTimeComputable_sliceDrop`, `Complexity.inter_mem_P`.
