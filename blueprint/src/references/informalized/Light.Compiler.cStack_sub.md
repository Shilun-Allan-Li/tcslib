<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Cells.lean :: Light.Compiler.cStack_sub -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stack address under subtraction

**Claim.** For natural numbers $q$ and $x$, subtracting $2x$ from the stack address at index $q$ gives the stack address at index $q+x$.

**Proof.** By definition, the address at index $j$ is $-2j$. The left side is therefore $-2q-2x=-2(q+x)$, which is exactly the address at index $q+x$.
