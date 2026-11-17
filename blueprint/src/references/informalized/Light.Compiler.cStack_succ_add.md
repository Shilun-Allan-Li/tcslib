<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Cells.lean :: Light.Compiler.cStack_succ_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successive stack addresses

**Claim.** For every natural number $q$, the stack address at index $q+1$, increased by $2$, equals the stack address at index $q$.

**Proof.** Apply the index-addition identity with $x=1$. Since $q+1=q+1$ and $2\cdot1=2$, that identity gives the stated equality.

**Key facts.** `Light.Compiler.cStack_add`.
