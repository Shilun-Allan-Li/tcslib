<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.codePrimSkipState -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Primitive Recursiveness of State Skipping

**Claim.** The state-field skipper is primitive recursive jointly in the bound and the Boolean string.

**Proof.** First regard the input as a pair consisting of the bound and the string after its first bit. The test of whether that first bit is true is primitive recursive. In the true case, apply the primitive-recursive finite-state skipper to the bound and the remaining string; in the false case, return the remaining string wrapped in `some`. Conditional composition therefore makes this two-branch operation primitive recursive. Finally, primitive recursion on the original list handles the empty string by returning `none`, and for a nonempty string passes its head and tail to the two-branch operation. This is exactly the specified behavior: a leading $0$ is consumed immediately, while a leading $1$ invokes the bounded unary-field skipper.

**Key facts.** `Turing.codePrimSkipFin`.
