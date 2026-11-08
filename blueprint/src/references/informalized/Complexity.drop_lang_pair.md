<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.drop_lang_pair -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indicator on Encoded Pairs

**Claim.** On the encoded pair of $z$ and the binary word for $q$, the indicator of the drop language equals the specified length test in true mode and the specified bit test in false mode.

**Proof.** The indicator formula for an index language evaluated on an encoded pair reduces membership to the predicate defining that language at the given pair (`Complexity.indicator_indexLang_pairEncode`). Apply it to the predicate that tests the length of $dropIdx(z)$ in true mode and the defaulted bit in false mode. Unfolding the two mode cases gives exactly the asserted Boolean value.

**Key facts.** `Complexity.indicator_indexLang_pairEncode`.
