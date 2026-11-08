<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/CNFEncoding.lean :: Std.Sat.CNF.decode_serialize -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding serialized CNF formulas

**Claim.** For every CNF formula $\varphi$ over variables indexed by $\mathbb{N}$, decoding its binary serialization returns $\varphi$.

**Proof.** Serialization followed by parsing returns the original formula: $\operatorname{parse}(\operatorname{serialize}(\varphi))=\operatorname{some}(\varphi)$, by the parsing correctness result (`Std.Sat.CNF.parse_serialize`). Decoding takes the parsed value when parsing succeeds, so applying it to this serialization returns $\varphi$.

**Key facts.** `Std.Sat.CNF.parse_serialize`.
