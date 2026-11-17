<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Cells.lean :: Light.Compiler.cStack_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stack address under index addition

**Claim.** For natural numbers $q$ and $x$, the stack address at index $q+x$, increased by $2x$, equals the stack address at index $q$.

**Proof.** By definition, the address at index $j$ is $-2j$. Thus the left side is $-2(q+x)+2x$, which expands and cancels to $-2q$, the address at index $q$.
