<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/EXPCOM.lean :: Complexity.expcom_ok_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization of Valid Front Inputs

**Claim.** A Boolean word passes the front-input validity test exactly when it has the form of a nested encoding of α, x, and a block of n true bits.

**Proof.** Suppose first that the validity test succeeds. Its three conjuncts say that the outer pair decodes, the resulting second component also decodes, and incrementing the remaining tail produces the empty default result. Each successful pair decoding reconstructs its input as the corresponding pair encoding (eq_pairEncode_of_pairDecode). Thus the word has nested form with some tail w. The final condition says that incrementing w has no successful nonempty output; the all-true characterization (expcom_all_true) then forces w to consist entirely of true bits. Taking n to be its length gives the required form. Conversely, for a word with this nested form, both pair decodings succeed by the decoding rule for pair encodings (pairDecode_pairEncode). Incrementing a block of true bits fails because there is no terminating false bit, as follows from the increment rule on replicated true bits (incFixed_replicate_true_append). Hence the final validity test also holds.

**Key facts.** `Turing.eq_pairEncode_of_pairDecode`, `Complexity.expcom_all_true`, `Turing.pairDecode_pairEncode`, `Turing.incFixed_replicate_true_append`.
