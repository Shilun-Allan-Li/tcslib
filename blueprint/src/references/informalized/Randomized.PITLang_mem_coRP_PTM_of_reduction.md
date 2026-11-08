<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPReduce.lean :: Randomized.PITLang_mem_coRP_PTM_of_reduction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Sided Randomized Membership

**Claim.** The language of paired encodings of well-formed algebraic circuits on the same number of inputs with equal associated integer polynomials belongs to co-RP with polynomial time bound.

**Proof.** The reduction theorem places the circuit-equivalence language below the zero-polynomial language by a polynomial-time many-one reduction (`PITLang_le_ZEROP`). The zero-polynomial language belongs to co-RP (`ZEROP_mem_coRP_PTM`). The closure of co-RP under polynomial-time many-one reductions (`coRP_PTM_of_polyTimeReducible`) therefore gives the asserted membership.

**Key facts.** `Randomized.PITLang_le_ZEROP`, `Randomized.ZEROP_mem_coRP_PTM`, `Randomized.coRP_PTM_of_polyTimeReducible`.
