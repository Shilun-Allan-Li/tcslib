<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerVerifier.lean :: Complexity.Meyer.evalAtom_mem_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time atomic evaluation

**Claim.** For each atom, the language of Boolean words on which its evaluation is true belongs to P.

**Proof.** The proof treats the atom constructors individually. For an answer atom, its evaluation is membership in the circuit-value language after a polynomial-time transformation: decode the description, form the query from the selected bit vector and the transformed time and auxiliary words, and pair-encode the result with the input. Each component transformation is polynomial-time computable, by the facts that decoding is polynomial-time (pt_vD), query formation preserves polynomial-time computability (pt_query), the time and auxiliary word maps are polynomial-time computable (pt_twd and pt_awd), and pairing is polynomial-time computable (PolyTimeComputable.pairEncode). Since circuit-value membership is in P (CVAL_mem_P), closure of P under polynomial-time preimages gives the result.

For the length-conjunction atom, each of its four length conditions is in P: equality of lengths is decidable in P for polynomial-time-computable word functions (lenEq_test), and comparison of lengths is likewise decidable in P (lenLe_test). The component words and the index encoding are polynomial-time computable, and P is closed under finite intersections (inter_mem_P), so their conjunction is in P.

For the two increment-based atoms, the condition that the incremented word is nonempty is the complement of the test that its length is at most zero. The increment operation and the relevant decoded word are polynomial-time computable (pt_inc, pt_vt, pt_va); the length comparison is in P and P is closed under complement (compl_mem_P).

For the zero-word atom, transducing a word to its true-bit representation is polynomial-time computable (polyTimeComputable_transduce). The input word equals the all-false word of its length exactly when this representation is empty (trues_eq_nil). Thus the condition reduces to a polynomial-time length-at-most-zero test. The index-zero atom is the same kind of test applied directly to the decoded index word. The strict comparison atom is the complement of the corresponding non-strict length comparison, while the non-strict comparison atom is itself a length test. Finally, the successor-length atom compares the decoded index length with the length of the input word preceded by one bit; that prefixed word is polynomial-time computable. These cases exhaust the constructors.

**Key facts.** `Complexity.PolyHierarchy.unaryPT_poly`, `Complexity.Meyer.pt_vx`, `Complexity.Meyer.pt_vD`, `Complexity.Meyer.pt_query`, `Complexity.Meyer.pt_twd`, `Complexity.Meyer.pt_awd`, `Complexity.Meyer.pt_vt`, `Complexity.Meyer.pt_va`, `Complexity.Meyer.pt_vj`, `Complexity.Meyer.pt_bjw`, `BoolCircuit.CVAL_mem_P`, `Complexity.preimage_mem_P`, `Complexity.Meyer.lenEq_test`, `Complexity.Meyer.lenLe_test`, `Complexity.inter_mem_P`, `Complexity.Meyer.pt_inc`, `Complexity.compl_mem_P`, `Complexity.polyTimeComputable_const`, `Complexity.polyTimeComputable_transduce`, `Complexity.Meyer.trues_eq_nil`, `Complexity.polyTimeComputable_prepend`, `Complexity.Meyer.pt_vj`, `Complexity.PolyTimeComputable.comp`, `Complexity.PolyTimeComputable.append`, `Complexity.Meyer.pt_vx`, `Complexity.PolyTimeComputable.pairEncode`.
