<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitLayerReduction.lean :: composedDelta_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Peeling the width factor off the composed parameter

**Claim.** For naturals `w, l, d` with `3 ≤ d`,
`composedDelta w (l : ℝ) d = (1 / (40 * w)) * composedDelta l (l : ℝ) (d - 1)`.
That is, the leading `1 / (40 * w)` factor splits off and the remaining
parameter is the same expression with the *width* argument replaced by `l` and
the depth dropped by one. Both sides expand to `(1/(40w)) * (1/(40l))^(d-2)`.

**Proof.**

1. `rcases d with (_ | _ | d)` splits off `d = 0` and `d = 1`; in both cases
   `norm_num [composedDelta] at *` closes the goal from the contradictory
   hypothesis `3 ≤ d`.
2. In the remaining case `d + 2`, `cases d` separates `d = 2` (both sides are
   `1/(40w)`, the exponent being `0`) from `d ≥ 3`, and
   `simp_all +decide [pow_succ']` finishes by pulling one `1 / (40 * l)` out of
   the power. ∎

Note this lemma reparameterizes `w ↦ l`, which is what makes it *different* from
`composedDelta_step_right`; the recursion in the LMN argument actually uses the
latter.

**Used in.** Nothing — this declaration is currently unused inside and outside
the file; the inductive step factors via `composedDelta_step_right` instead.
