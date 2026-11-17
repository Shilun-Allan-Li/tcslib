<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.tmsat_result_accept -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance Characterizes the Verifier Language

**Claim.** The guarded result produced from a bit string is the word $11$ exactly when the string belongs to the verifier language.

**Proof.** For the forward implication, split according to whether the validity test succeeds. If it does, `tmsat_good_spec` decomposes the string into its two projected fields, proves the required length relation, and identifies the first field with the prescribed quadruple encoding of the extracted code, input, width, and clock. The acceptance characterization of `tmsatAnswer` then turns the assumed result $11$ into the claim that the decoded machine computes output $1$ on the assembled input at the extracted clock. These facts provide the witnesses required by the verifier language. If the validity test fails, the result is the answer on empty code, empty input, and time zero. The acceptance characterization would make that a computation at time zero, which is impossible by `FinTM.not_computesInTime_zero`; hence this case contradicts the assumed result. For the reverse implication, take witnesses from verifier-language membership and substitute the given concatenation for the string. The length relation and `tmsat_good_quad` show that the validity test succeeds and that the extracted fields recover the witnesses' code, input, width, clock, and certificate. The answer characterization now gives result $11$ from the witnessed computation.

**Key facts.** `Complexity.tmsat_good_spec`, `Complexity.tmsatAnswer_accept`, `Turing.FinTM.not_computesInTime_zero`, `Complexity.tmsat_good_quad`.
