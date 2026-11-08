<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/PrimeFind.lean :: Complexity.BinArith.polyTimeComputable_lovaszPrime -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Polynomial-Time Prime Encoding

**Claim.** The function sending an input word to the binary expansion of the least prime at least $2^{\lceil\log_2(2|z|)\rceil}+1$ is polynomial-time computable.

**Proof.** The proof builds a polynomial-time search procedure from the available polynomial-time arithmetic and Boolean operations. It first establishes that one search update is polynomial-time computable: its cases are assembled from tests, comparisons, addition, remainder, projections of encoded tuples, constants, and the identity function. The initial search state is also polynomial-time computable, using the doubling loop and addition to form the initial candidate and auxiliary data.

Starting from that state, iterate the update for $64(|z|+1)^2$ steps. The invariant for the search is preserved at every step (`searchInv_init`, `searchInv_step`, and `iterate_invariant`); it records the candidate and auxiliary quantities needed to justify the search. The prime bound `lovaszPrime_le_linear` and the binary-length estimates `length_bits_le` and `length_bits_mono` bound the lengths of the invariant’s encoded data by a polynomial in the input length. Consequently the polynomial-time iteration theorem applies to this many updates.

To identify the final candidate, use the search measure: while it is positive, each update strictly decreases it, and when it is zero the update leaves the state fixed (`searchInv_step`). Its initial value is at most the stated quadratic iteration bound, using the linear bound on the least prime and the binary-value identity `bitsVal_bits`. Therefore after the prescribed number of steps the measure is zero. The invariant then identifies the candidate stored in the first decoded component of the final state as the desired least prime. Project that component and output its binary expansion, as required.

**Key facts.** `Complexity.BinArith.polyTimeComputable_slot3`, `Complexity.BinArith.polyTimeComputable_id`, `Complexity.BinArith.polyTimeComputable_beq`, `Complexity.BinArith.polyTimeComputable_mod`, `Complexity.BinArith.polyTimeComputable_add`, `Complexity.BinArith.polyTimeComputable_isZero`, `Complexity.polyTimeComputable_ite`, `Complexity.polyTimeComputable_const`, `Complexity.BinArith.polyTimeComputable_dblLoop`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.BinArith.searchInv_init`, `Complexity.BinArith.polyTimeComputable_iterate`, `Complexity.BinArith.searchInv_step`, `Complexity.BinArith.iterate_invariant`, `Complexity.BinArith.lovaszPrime_le_linear`, `Complexity.LogProg.length_bits_le`, `Complexity.LogProg.length_bits_mono`, `Complexity.BinArith.iterate_measure_eq_zero`, `Complexity.LogProg.bitsVal_bits`, `Complexity.polyTimeComputable_pairFstD`, `Complexity.PolyTimeComputable.comp`.

**Caveat.** The supplied statement of `SearchInv` and the definitions of `searchInit`, `searchStep`, and `searchMeasure` are absent, so the precise invariant contents and the final candidate-identification step cannot be spelled out from the provided material.
