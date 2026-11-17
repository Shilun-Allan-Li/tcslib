<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.comp_lang_pair -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership of Encoded Pairs

**Claim.** The indicator of the language testing the output associated to $z$ at index $p$, on the encoded input $(z,\mathrm{bits}(p))$, is true exactly for the specified length or bit test, according to the mode.

**Proof.** By the encoded-pair indicator theorem (\texttt{indicator\_indexLang\_pairEncode}), membership of an input of the form $\langle z,\mathrm{bits}(p)\rangle$ in an index language is exactly its defining predicate evaluated at $(z,p)$. Apply this to the predicate defining the language here. In length mode it is $p<|\mathrm{compQ}(f,z)|$, whose Boolean indicator is the stated decision; in bit mode it is the equality of the selected bit with true, whose indicator is that bit itself.

**Key facts.** `Complexity.indicator_indexLang_pairEncode`.
