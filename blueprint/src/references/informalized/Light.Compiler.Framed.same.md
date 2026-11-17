<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Cells.lean :: Light.Compiler.Framed.same -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Framing Outside Scratch Addresses

**Claim.** If a memory satisfying the storage and frame-bound conditions is changed only at scratch addresses, it still satisfies those conditions for the same state and frame pointer.

**Proof.** The storage relation is preserved under agreement outside the scratch set (Light.Compiler.Rel.same). The frame bounds are unchanged: the frame pointer still satisfies $1\le q$, and the upper bound $q+F\le Q$ remains true. Together these establish the framed conditions for the new memory.

**Key facts.** `Light.Compiler.Rel.same`.
