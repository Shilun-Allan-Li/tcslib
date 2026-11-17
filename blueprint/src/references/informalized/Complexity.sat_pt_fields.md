<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.sat_pt_fields -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Pair Projections

**Claim.** Both total functions that decode a bit string as a pair and return its first or second component, using the empty string when decoding fails, are polynomial-time computable.

**Proof.** The pair parser has linear-time machines for each projection, with failed decodings returning the empty word (`Turing.FinTM.computesFunInTime_pairFst` and `Turing.FinTM.computesFunInTime_pairSnd`). A linear-time bound is a polynomial-time bound, so applying the linear-to-polynomial implication to each machine proves both claims (`Complexity.sat_pt_linear`).

**Key facts.** `Turing.FinTM.computesFunInTime_pairFst`, `Complexity.sat_pt_linear`, `Turing.FinTM.computesFunInTime_pairSnd`.
