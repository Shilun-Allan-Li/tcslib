<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerTableau.lean :: Complexity.Meyer.wstep_none_iterate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Repeated Input-Head Movement

**Claim.** Applying the selector-directed step for the input tape $a$ times changes only the input-head position, moving it by the corresponding clamped direction $a$ times.

**Proof.** Induct on the number $a$ of steps, generalizing over the starting configuration. At zero steps both iterates are the identity, so the result follows immediately. For the successor case, separate the first step from the remaining $a$ steps on the left, and apply the induction hypothesis to the configuration after that first step. The selector step changes only the input-head position, applying one clamped move in direction $\mathrm{walkDir}(neg)$; the induction hypothesis then applies the same move $a$ more times. The resulting configuration has all original components other than the input position unchanged, with that position equal to the $a+1$-fold iterate of the clamped move.
