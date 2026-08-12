<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ArrowTheorem.lean :: unanimity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Unanimity of a social welfare function

**Definition.** For `f : BooleanFunc n` (a map `(Fin n → Bool) → ℝ`),

`unanimity f ↔ f (fun _ => false) = 1`.

Each voter's ballot in a single pairwise comparison is a `Bool`, with `false`
meaning "prefers the first alternative"; `boolToSign false = 1`. So the all-false
input is the profile in which *every* voter ranks `a` above `b`, and the
condition says society then also ranks `a` above `b` (output `+1`).

**Remark.** The definition pins down only the one point `(false, …, false)`, not
the mirror point `(true, …, true)`. That is deliberate: the companion hypothesis
`isOddFunc f` (`f (fun i => !x i) = -f x`) supplies the other end for free, so
demanding both would be redundant. A plain `Prop`-valued definition; no proof.

**Used in.** A hypothesis of `degree_one_implies_dictator` and of the top-level
`arrow_theorem`. Its only real work happens inside
`degree_one_implies_dictator` step 3, where `rw [unanimity]` combined with the
level-1 Walsh expansion and `boolToSign_false` turns the single function value
into the linear constraint `∑ i, fourierCoeff f {i} = 1` — the fact that later
forces exactly one degree-1 coefficient to equal `1`.
