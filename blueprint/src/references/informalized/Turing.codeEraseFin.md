<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeParser.lean :: Turing.codeEraseFin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded index erasure

**Claim.** For every $n$ and bit string $x$, erasing the bounded unary index reader yields exactly the result of the unary index skipper with bound $n$.

**Proof.** Both procedures first decode the same unary number and remaining suffix. They then impose the same condition, that the number is less than $n$; if it holds, each returns that suffix, and if it fails, each fails. Thus their results agree in all cases.
