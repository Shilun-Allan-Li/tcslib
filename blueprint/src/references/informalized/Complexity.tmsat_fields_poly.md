<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.tmsat_fields_poly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time verifier fields

**Claim.** Each specified parsing and projection field of a bit string is polynomial-time computable, as is the one-bit output encoding whether all the parsing and unary-field validity checks hold.

**Proof.** First compute the split encoding of the input using the polynomial-time split-solving machine (Turing.FinTM.computesFunInTime_splitSolve), and regard this as the polynomial-time function tmsatSplit. The projections that return the first or second component of a decoded pair are polynomial-time computable (polyTimeComputable_pairFstD and polyTimeComputable_pairSndD). Composing these projections with the split yields the instance part; further nested projections yield the code, input, width, clock, and certificate fields. The first four requested fields and the certificate field are therefore polynomial-time computable by the composition principle (Complexity.PolyTimeComputable.comp). For the validity bit, the predicate that a pair decodes successfully is polynomial-time computable from its linear-time machine (Turing.FinTM.computesFunInTime_pairValid) and the linear-time-to-polynomial-time principle (Complexity.polyTimeComputable_of_linear). Apply it to the split and to each successive nested component. The width and clock unary checks are polynomial-time computable by the unary-field check (Complexity.tmsat_pt_unary) composed with the corresponding field extractors. Combining these Boolean checks with conjunction preserves polynomial-time computability (Complexity.polyTimeComputable_and), producing the requested one-bit validity output.

**Key facts.** `Turing.FinTM.computesFunInTime_splitSolve`, `Complexity.polyTimeComputable_pairFstD`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.PolyTimeComputable.comp`, `Turing.FinTM.computesFunInTime_pairValid`, `Complexity.polyTimeComputable_of_linear`, `Complexity.tmsat_pt_unary`, `Complexity.polyTimeComputable_and`.
