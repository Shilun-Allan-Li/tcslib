<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/JohnsonBound.lean :: J2 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# `J2 n d`: the Johnson weight threshold

**Definition.** `J2 n d : ℝ` is
`((n : ℝ) - Real.sqrt ((n : ℝ) * ((n : ℝ) - 2 * (d : ℝ)))) / 2`,
the real number against which codeword weights are compared: the hypothesis
`(w : ℝ) ≤ J2 n d` says the code's weight ceiling `w` sits at or below this
threshold.

**Remark.** No positivity or `2 * d ≤ n` side condition is built into the
definition — `Real.sqrt` of a negative argument is `0`, so `J2 n d` is total, and
the hypotheses `0 < n`, `2 * d ≤ n` are carried by the theorems instead. In the
Lean development `J2` is a pure abbreviation for that expression: it is `unfold`ed
at the single point where it does work (`johnson_arith`, `unfold J2 at hw` turning
`(w : ℝ) ≤ J2 n d` into `2 * (w : ℝ) ≤ n - √(n(n - 2d))`).

**Used in.** The `hwJ` hypothesis of `binary_johnson_card_bound`,
`binary_johnson_card_bound_of_admissible` and `binary_johnson_bound_radius`;
`johnson_arith` is what converts it into the negativity of the quadratic shift
expression that drives the pairwise-inner-product bound.
