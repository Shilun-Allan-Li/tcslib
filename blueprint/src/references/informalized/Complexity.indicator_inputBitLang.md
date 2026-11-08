<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.indicator_inputBitLang -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Bit Indicator

**Claim.** For a binary string $y$ and an index $a\in\mathbb N$, the indicator of the language of encoded pairs whose indexed bit is true, evaluated at the encoding of $y$ and the binary representation of $a$, equals the bit of $y$ at index $a$, with out-of-range indices interpreted as false.

**Proof.** The indicator of an encoded pair in an indexed language is the classical decision of the predicate at that pair (`indicator_indexLang_pairEncode`). Here that predicate says that $y.getD\ a\ false=true$. If this Boolean is true, the decision is true; if it is false, the decision is false. Thus the indicator equals $y.getD\ a\ false$ in either case.

**Key facts.** `Complexity.indicator_indexLang_pairEncode`.
