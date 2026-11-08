<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.sat_pipeline_poly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Validation Pipeline

**Claim.** The catalog-split validity bit, recovered instance, recovered-instance syntax bit, and safe evaluator request are all polynomial-time computable functions on binary strings.

**Proof.** First, a machine can compute the split encoding by solving the length equation used by the catalog split; the supplied split-solving result gives a time bound of degree $3$ for these parameters. The one-bit validity result and the recovered instance are obtained by applying, respectively, pair decoding followed by its validity test and pair decoding followed by projection to the first component. These are linear-time postprocessings, so composition preserves polynomial time. Next, apply the polynomial-time CNF syntax test to the recovered instance; composing polynomial-time functions again gives a polynomial-time syntax bit. Finally, the safe request selects the split encoding when both the validity and syntax bits hold, and otherwise returns a fixed encoding. Testing the conjunction of the two bits is polynomial-time, and selecting between polynomial-time functions using that bit preserves polynomial time. This establishes all four claims.

**Key facts.** `Turing.FinTM.computesFunInTime_splitSolve`, `Complexity.polyTimeComputable_of_linear`, `Turing.FinTM.computesFunInTime_pairValid`, `Complexity.polyTimeComputable_of_linear`, `Turing.FinTM.computesFunInTime_pairFst`, `Complexity.polyTimeComputable_of_linear`, `Complexity.PolyTimeComputable.comp`, `Complexity.satSyntax_poly`, `Complexity.polyTimeComputable_and`, `Complexity.polyTimeComputable_const`, `Complexity.polyTimeComputable_ite`.
