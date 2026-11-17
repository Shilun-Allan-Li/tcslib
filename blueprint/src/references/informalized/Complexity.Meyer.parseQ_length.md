<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerTab.lean :: Complexity.Meyer.parseQ_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lengths of Parsed Fields

**Claim.** If parsing $y$ succeeds, yielding a bit vector and three words $t,a,x$, then $|t|\le |y|$ and $|a|\le |y|$.

**Proof.** If the bit prefix is too long to fit in $y$, parsing cannot succeed, so the hypothesis rules this case out. In the remaining case, expose the two successful field reads in the definition of the parser: the first reads $t$ and leaves a remainder $r$, and the second reads $a$ and leaves $x$. The successful parse identifies these fields with the stated $t$ and $a$. By the field-reading decomposition (`readField_eq_some`), each input to a successful field read consists of the encoding of the field, followed by a delimiter and the remainder. In particular, the encoding of a field has length at least the length of that field, and neither field's input can be longer than the original word $y$: the first input is the suffix after the bit prefix, and the second is a remainder of that suffix. Therefore both $|t|$ and $|a|$ are at most $|y|$.

**Key facts.** `Complexity.Meyer.readField_eq_some`.
