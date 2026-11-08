<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.indicator_inputLenLang -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Length Indicator

**Claim.** For a binary string $y$ and an index $a\in\mathbb N$, the indicator of the language of encoded pairs whose index is less than the string length, evaluated at the encoding of $y$ and the binary representation of $a$, equals the Boolean decision of whether $a<|y|$.

**Proof.** The indicator of an encoded pair in an indexed language is the classical decision of the predicate at that pair (`indicator_indexLang_pairEncode`). For the input-length language, that predicate is precisely $a<y.length$. Its decision therefore agrees with `decide (a < y.length)`, as claimed.

**Key facts.** `Complexity.indicator_indexLang_pairEncode`.
