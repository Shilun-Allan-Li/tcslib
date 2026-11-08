<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Padding.lean :: Complexity.PolyHierarchy.unaryPT_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constant unary output

**Claim.** For every natural number $k$, the function sending each bit string to the word of $k$ true bits is polynomial-time computable.

**Proof.** The word consisting of $k$ true bits is fixed independently of the input. The result that every constant bit-string-valued function is polynomial-time computable (`Complexity.polyTimeComputable_const`) therefore applies to this particular constant word. By the definition of `UnaryPT`, this is exactly the required conclusion.

**Key facts.** `Complexity.polyTimeComputable_const`.
