<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.compLift_query -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of a lifted query

**Claim.** On the stated nested encoding, the indicator of the lifted query language is true in length mode exactly when $j<|f(x)|$; otherwise it equals the $j$th bit of $f(x)$, using false beyond the string’s end.

**Proof.** Applying the decoding operation twice to the nested encoding removes the outer index layer and then the paired string $b$, leaving the encoding of $x$ with the binary expansion of $j$. This is the decoding behavior of `dropIdx_pairEncode`. The indicator of an indexed language on an encoded input is the decision of its defining predicate (`indicator_indexLang_pairEncode`). Thus the result is the decision of the predicate that tests $j<|f(x)|$ in length mode, and otherwise tests whether the defaulted $j$th bit is true. In the first case this is the Boolean value of the inequality; in the second it is exactly the defaulted bit.

**Key facts.** `Complexity.dropIdx_pairEncode`, `Complexity.indicator_indexLang_pairEncode`.
