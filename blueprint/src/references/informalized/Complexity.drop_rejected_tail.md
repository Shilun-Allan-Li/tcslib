<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.drop_rejected_tail -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rejection of Invalid Trailing Payloads

**Claim.** If the trailing payload is not canonical, or its length exceeds the length of the binary representation of the encoded pair's length, then the mode indicator is false on that pair encoding.

**Proof.** First suppose the tail is canonical. Every canonical bit string is the binary representation of its value (`Complexity.LogProg.canon_eq_bits`), so write it as $\mathrm{bits}(q)$. The assumed failure of the length bound says that the width of the binary representation of the encoded input length is strictly less than $|\mathrm{bits}(q)|$. The overflow result (`Complexity.dropIdx_query_overflow`) then says both that the queried bit of the transformed word is false and that $q$ is not below its length. The characterization of the drop language on an encoded binary query (`Complexity.drop_lang_pair`) gives a false indicator in either mode. If the tail is not canonical, the invalid-tail rejection result (`Complexity.drop_bad_tail`) directly gives the same conclusion.

**Key facts.** `Complexity.LogProg.canon_eq_bits`, `Complexity.dropIdx_query_overflow`, `Complexity.drop_lang_pair`, `Complexity.drop_bad_tail`.
