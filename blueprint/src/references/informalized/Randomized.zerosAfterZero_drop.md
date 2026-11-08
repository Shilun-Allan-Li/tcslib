<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/QuasiPolyHierarchy.lean :: Randomized.zerosAfterZero_drop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transducer Output After Dropping a Prefix

**Claim.** For natural numbers $m$ and $i$, applying the transducer to the suffix obtained by dropping the first $i$ bits of $m-1$ ones followed by zero and then $m$ ones produces $m$ zeros if $i<m$, and the empty string if $i\ge m$.

**Proof.** Split according to whether $i<m$. In that case, dropping the prefix removes only some of the initial $m-1$ ones, leaving a string of ones followed by the marked zero and then the final $m$ ones. The transducer emits nothing while reading the initial ones; at the zero it enters the state that emits a zero on each subsequent bit. Thus the final block of $m$ ones produces exactly $m$ zeros (`Randomized.zerosAfterZero_ones_zero`). If $i\ge m$ and $m>0$, the dropped prefix reaches or passes the zero, leaving only some suffix of the final block of ones, on which the transducer emits nothing (`Randomized.zerosAfterZero_ones`). If $m=0$, the original string is empty, so every dropped suffix is empty and the result is empty as well.

**Key facts.** `Randomized.zerosAfterZero_ones_zero`, `Randomized.zerosAfterZero_ones`.
