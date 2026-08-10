<!-- generated-by: proofmatch informalization (not_in_text) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Basic.lean :: flipBit_ne -->
<!-- origin: boolean-ch02-social-choice-arrow run 352ab7ff3113 verdict not_in_text (0.90) -->

# Flipping bit i leaves the other coordinates alone

**Claim.** For `x : BoolCube n` and `i j : Fin n` with `i ≠ j`, the point
`flipBit x i` agrees with `x` at coordinate `j`: `flipBit x i j = x j`.
Here `flipBit x i = Function.update x i (!x i)`.

**Proof.**

1. Unfold `flipBit` to `Function.update x i (!x i)` (`simp [flipBit]`).
2. `Function.update_of_ne` applied to `Ne.symm h : j ≠ i` rewrites the update
   at the untouched index to `x j`, closing the goal.

**Used in.** The `flipBit` bookkeeping behind `chiS_flipBit` and hence
`influence_chi` / `influence_eq_sum_fourier`: every argument that flips one
coordinate needs this fact to keep the remaining coordinates fixed.
