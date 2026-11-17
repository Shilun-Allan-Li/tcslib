<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/QBFEncoding.lean :: Complexity.QBF.decode_encode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding an Encoded Quantified Formula

**Claim.** For every quantified Boolean formula $Q$, decoding its encoding recovers its quantifier prefix and CNF matrix exactly.

**Proof.** Write $Q$ as a quantifier list $q_s$ and matrix $m$. Decoding the pair encoding recovers the encoded quantifier bits and serialized matrix (`Turing.pairDecode_pairEncode`). On the matrix side, decoding the serialization returns $m$ (`Std.Sat.CNF.decode_serialize`). On the prefix side, mapping the bit interpretation over the encoded quantifier bits amounts to interpreting each bit after it has been produced by `quantBit`; the map composition simplifies accordingly. Each quantifier is recovered because interpreting its encoding bit returns that quantifier (`Complexity.QBF.quantOfBit_quantBit`). Thus both components of the decoded formula equal the original components.

**Key facts.** `Turing.pairDecode_pairEncode`, `Std.Sat.CNF.decode_serialize`, `Complexity.QBF.quantOfBit_quantBit`.
