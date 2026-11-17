<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.codePrimUnary -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Primitive Recursiveness of Unary Reading

**Claim.** The unary reader that counts leading true bits up to the first false bit and returns the count with the remaining suffix is primitive recursive.

**Proof.** Use primitive recursion on the Boolean list, with the empty list assigned failure. At a false head, return zero together with the tail. At a true head, use the result on the tail, increase its count by one, and preserve its suffix; if the recursive result is failure, that failure remains failure. These clauses match the unary reader, so the primitive-recursive list recursion computes it.
