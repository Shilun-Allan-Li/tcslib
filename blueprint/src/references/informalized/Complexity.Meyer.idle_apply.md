<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineParse.lean :: Complexity.Meyer.idle_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Idle action entry

**Claim.** For every natural number $n$ and index $j<n$, the $j$th entry of the idle action table is the pair consisting of no write instruction and zero movement.

**Proof.** By definition, the idle action table assigns the same pair, no write and zero movement, to every index. Evaluating it at $j$ therefore gives the claimed pair.
