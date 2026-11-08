<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPThreeQuery.lean :: FABL.compositionLocalAssignment_eq_extracted -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Local Assignment from an Extended Proof

**Claim.** For every input word, extended proof, and verifier seed, the local sign assignment obtained from the concatenated input and extended proof equals the extension of the encoded outer local bits, read from the first $\ell$ proof positions, by the auxiliary signs extracted for that seed.

**Proof.** Compare the assignments coordinate by coordinate, splitting each coordinate into an outer-query position or an auxiliary position. At an outer-query position, the local address is a lifted original address. The lifted-address identity (`inputProofWord_restrictOuterProof_liftOuterAddress`) shows that evaluating the concatenated word there agrees with evaluating the input word together with the restriction of the extended proof to its first $\ell$ positions. Encoding gives the stated outer sign. At an auxiliary position, the address selects the corresponding seed-indexed auxiliary bit in the extended proof; by definition, its sign encoding is exactly the extracted auxiliary sign. These are the two parts of the extended assignment, so equality holds at every coordinate.

**Key facts.** `FABL.inputProofWord_restrictOuterProof_liftOuterAddress`.
