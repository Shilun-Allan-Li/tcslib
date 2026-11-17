<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimePairing.lean :: Complexity.polyTimeComputable_pairFstD -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First projection is polynomial-time computable

**Claim.** The total first projection, which returns the decoded first component when parsing succeeds and the empty word otherwise, is polynomial-time computable.

**Proof.** A linear-time machine computes the total first projection by parsing the input and returning the first component on successful decoding, with the empty word as the default on failure. The linear-time-to-polynomial-time result applies directly to this machine and function, proving the claim.

**Key facts.** `Turing.FinTM.computesFunInTime_pairFst`, `Complexity.polyTimeComputable_of_linear`.
