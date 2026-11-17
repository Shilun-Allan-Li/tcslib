<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.fieldOffset_cons_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Offset after a leading field

**Claim.** Prepending a field $u$ shifts the offset of field $j$ by $|u|+1$ when it becomes field $j+1$.

**Proof.** In the offset sum for the first $j+1$ fields of $u::fs$, the leading field contributes $|u|+1$. The remaining $j$ contributions are exactly those in the offset sum for the first $j$ fields of $fs$. Adding these contributions gives the asserted identity.
