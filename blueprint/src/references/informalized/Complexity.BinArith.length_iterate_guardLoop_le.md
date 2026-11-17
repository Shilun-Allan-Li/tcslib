<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Iterate.lean :: Complexity.BinArith.length_iterate_guardLoop_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length Bound for Iterated Guarded Updates

**Claim.** After any number $i$ of guarded-loop iterations starting from $w$, the resulting bit string has length at most $7(|w|+1)$.

**Proof.** For $i=0$, the iterate is $w$, and its length is at most $7(|w|+1)$. For a successor number of iterations, first apply the loop $i$ times and then once more. The slot bounds with parameter $|w|$ hold for the initial word (`Complexity.BinArith.slotsLe_self`) and remain true after every iteration (`Complexity.BinArith.slotsLe_guardLoop`), by the invariant-under-iteration principle (`Complexity.BinArith.iterate_invariant`). The one-step estimate (`Complexity.BinArith.length_guardLoop_le`) therefore bounds the final output by $7|w|+6$, which is at most $7(|w|+1)$.

**Key facts.** `Complexity.BinArith.iterate_invariant`, `Complexity.BinArith.length_guardLoop_le`, `Complexity.BinArith.slotsLe_guardLoop`, `Complexity.BinArith.slotsLe_self`.
