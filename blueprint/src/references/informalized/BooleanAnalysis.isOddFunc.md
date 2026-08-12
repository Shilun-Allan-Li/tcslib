<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Basic.lean :: isOddFunc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Odd Boolean functions

**Definition.** `isOddFunc (f : BooleanFunc n) : Prop := ∀ x : BoolCube n,
f (fun i => !x i) = -f x` — negating *every* input coordinate negates the
output.

- In social-choice language this is the antisymmetry (neutrality) axiom: if
  every voter reverses their preference between the two candidates, the
  aggregated outcome reverses too.
- It is a predicate on real-valued `f`, logically independent of `isPmOne`
  (`∀ x, f x = 1 ∨ f x = -1`). Arrow's theorem assumes both; `arrow_theorem`
  takes `hodd : isOddFunc f` and `hpm : isPmOne f` separately.
- Note the antipodal map `fun i => !x i` flips all `n` coordinates at once —
  unrelated to the single-coordinate `flipBit`.

**Remark.** The Fourier meaning is a parity constraint: oddness forces all
even-level coefficients to vanish (`fourierCoeff_odd_even`), so an odd function
is supported on odd `|S|` — in particular it has zero mean.

**Used in.** The hypothesis of `fourierCoeff_odd_even`, and a standing
assumption across `ArrowTheorem.lean`: `corrFunc_ge_neg_third` (line 191),
the `corrFunc = -1/3` characterisation (line 232), and `arrow_theorem`
(line 704). At `acyclic_implies_corrFunc` (line 502) and
`degree_one_implies_dictator` (line 557) it is bound as `_hodd` — carried for
uniformity of the statement but not used in those two proofs.
