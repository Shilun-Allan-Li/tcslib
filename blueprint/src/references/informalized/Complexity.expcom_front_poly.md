<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/EXPCOM.lean :: Complexity.expcom_front_poly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Front Transformation

**Claim.** The map sending each Boolean word to its prescribed front transformation is computable by a finite Turing machine in polynomial time.

**Proof.** The front transformation first checks whether the input is a valid nested encoding with a final block of true bits, and then either constructs the simulator input or returns a fixed default word. Each operation in this construction has a polynomial-time implementation: incrementing a fixed-width word, extracting either component of a pair encoding, appending a bit, checking pair validity, and testing whether an increment result is empty. Composition gives polynomial-time computability of the nested tail extraction and of the increment-and-append portions. The Boolean validity test is assembled from the two pair-validity tests and the emptiness test using closure of polynomial-time computability under conjunction. The simulator-input construction uses the polynomial-time pair swap together with pair encoding and component extraction. Finally, selecting this result when the validity test succeeds and the fixed default word otherwise preserves polynomial-time computability, by closure under conditional choice and constant functions.

**Key facts.** `Complexity.PolyTimeComputable.comp`, `Complexity.polyTimeComputable_of_linear`, `Turing.FinTM.computesFunInTime_incFixed`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.polyTimeComputable_pairFstD`, `Complexity.polyTimeComputable_of_linear`, `Turing.FinTM.computesFunInTime_pairValid`, `Complexity.polyTimeComputable_and`, `Complexity.polyTimeComputable_of_linear`, `Turing.FinTM.computesFunInTime_ifEq`, `Complexity.polyTimeComputable_pairSwap`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.polyTimeComputable_ite`, `Complexity.polyTimeComputable_const`.
