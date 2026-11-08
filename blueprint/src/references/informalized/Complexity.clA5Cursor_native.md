<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Cursor_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time cursor and instance projections

**Claim.** The emission cursor encoded in any Boolean word can be output in unary in polynomial time, and the retained instance encoded there can also be output in polynomial time.

**Proof.** The cursor is the length of the first header field. Header-field extraction is polynomial-time computable (\texttt{clHeaderField_native}), and filling a word with a fixed Boolean symbol to a length supplied by a polynomial-time computation preserves polynomial-time computability (\texttt{clNative_fill}); together these give the unary cursor output. The retained instance is obtained by taking the first header field after extracting the first tail. Composing the polynomial-time header-tail and header-field projections (\texttt{clHeaderTail_native} and \texttt{clHeaderField_native}) therefore computes that instance in polynomial time; composition preserves polynomial-time computability (\texttt{PolyTimeComputable.comp}).

**Key facts.** `Complexity.clHeaderField_native`, `Complexity.clNative_fill`, `Complexity.clHeaderTail_native`, `Complexity.PolyTimeComputable.comp`.
