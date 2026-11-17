<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerTableau.lean :: Complexity.Meyer.wstep_some_iterate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Repeated work-tape movement

**Claim.** After applying the selector-directed step $a$ times, the configuration is unchanged except that the head on tape $h$ has moved by $a$ units in the selected direction.

**Proof.** Induct on $a$, allowing the starting configuration to vary. At $a=0$, no step has occurred, and the signed displacement is zero, so the claim is immediate. For the successor case, first apply the induction hypothesis: after $a$ steps only the selected head position has changed, by the signed displacement for $a$. One further step changes only that position, adding one in the positive direction or subtracting one in the negative direction. In either case the resulting position is the original position plus the signed displacement for $a+1$; every other component remains as stated.
