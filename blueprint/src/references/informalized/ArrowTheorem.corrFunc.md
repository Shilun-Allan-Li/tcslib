<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ArrowTheorem.lean :: corrFunc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The pairwise correlation function (noise stability at `-1/3`)

**Definition.** For `f : BooleanFunc n`,

`corrFunc f = ∑ S : Finset (Fin n), fourierCoeff f S ^ 2 * (-1/3 : ℝ) ^ S.card`.

Summation is over all `2^n` subsets of coordinates, weighting each squared
Fourier coefficient by `(-1/3)` raised to the level `|S|`. This is the noise
stability `Stab_{-1/3}[f]`, equivalently `∑_k W^k[f] · (-1/3)^k` in terms of
Fourier weight per level. `noncomputable`, inherited from `fourierCoeff`.

**Remark.** The quantity is engineered so that two very different computations
meet on it.

- *Analytically* it is a weighted Fourier sum, so the sign pattern of
  `(-1/3)^{|S|}` can be exploited level by level: `corrFunc_ge_neg_third` shows
  `corrFunc f ≥ -1/3` for odd `±1`-valued `f` (even levels vanish by
  `fourierCoeff_odd_even`, odd levels satisfy `(-1/3)^k ≥ -1/3`, and Parseval
  normalizes the total weight to `1`), and
  `corrFunc_eq_neg_third_of_weight_one` shows that attaining `-1/3` forces every
  coefficient off level 1 to vanish.
- *Probabilistically* it is a pairwise expectation: `expected_product_helper`
  proves `(1/6)^n * ∑ p, f (votes1 p) * f (votes2 p) = corrFunc f` for any pair
  of vote projections admitting the `-1/3` kernel, so all three of
  `expected_product_eq_corrFunc`, `expected_product_bcca`,
  `expected_product_abca` land on the *same* value.

That coincidence is the pivot of Kalai's proof: acyclicity constrains the
probabilistic side, and the analytic side converts the constraint into
degree-1-ness.

**Used in.** `corrFunc_ge_neg_third`, `corrFunc_eq_neg_third_of_weight_one`,
`expected_product_helper` and the three `expected_product_*` lemmas,
`acyclic_implies_corrFunc`, and step 1 of `arrow_theorem`.
