<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.isCompleteQuadraticOne_of_linearChecks -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic Parity from Linear Checks

**Claim.** If all endpoint, linear-transition, product, and quadratic-prefix checks hold for the assignment and proof table, then the sum of pairwise products over indices $i<j$ equals $1$ in the binary field.

**Proof.** The prefix checks force each encoded quadratic-prefix bit to equal the corresponding quadratic prefix computed from the assignment; in particular, this holds at the final index $n$ ( `completeQuadraticPrefixProof_eq_of_checks`). The full-prefix identity identifies that final computed prefix with the complete quadratic bit, the sum of pairwise products over $i<j$ ( `completeQuadraticPrefixBit_full`). The endpoint check says the final table bit is true, whose binary encoding is $1$ ( `pcppBoolF₂Equiv_true`). Combining these equalities gives the complete quadratic bit equal to $1$.

**Key facts.** `FABL.completeQuadraticPrefixProof_eq_of_checks`, `FABL.completeQuadraticPrefixBit_full`, `FABL.pcppBoolF₂Equiv_true`.
