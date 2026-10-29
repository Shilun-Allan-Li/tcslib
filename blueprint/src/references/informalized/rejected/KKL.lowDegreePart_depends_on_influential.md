<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/KKL.lean :: lowDegreePart_depends_on_influential -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The low-degree part is close to a junta on the influential coordinates

**Claim.** For `τ > 0` there is `g : BooleanFunc n` with
`IsJunta g (influentialCoords f τ)` and
`l2DistSq (lowDegreePart f k) g ≤ (n : ℝ) * τ`.

**Proof.** Take `J := influentialCoords f τ` and
`g x := ∑ S, if S.card ≤ k ∧ S ⊆ J then f̂(S)·χ_S(x) else 0` — the low-degree
part with every Fourier set that leaves `J` deleted.

- *Junta.* If `x` and `y` agree on `J`, each surviving character agrees:
  `chiS` is a product over `i ∈ S ⊆ J`, so `Finset.prod_congr` plus
  `congrArg boolToSign (hxy i (h.2 hi))` gives `g x = g y`.
- *`hdiff`.* `lowDegreePart f k x - g x = ∑ S, if S.card ≤ k ∧ ¬S ⊆ J then f̂(S)·χ_S(x) else 0`
  (subtract the sums termwise, `by_cases` on the two guards).
- *`hbound`.* Parseval on that difference: `hh_eq` rewrites
  `expect (h²)` as `innerProduct h h` and then `parseval` as `∑ S, fourierCoeff h S ^ 2`;
  `hcoeff` computes `fourierCoeff h T = if T.card ≤ k ∧ ¬T ⊆ J then f̂(T) else 0`
  by the same unfolded orthogonality computation as
  `fourierCoeff_lowDegreePart` (`fourier_coeff_chi`, `Finset.sum_comm`,
  `Finset.sum_ite_eq'`). Dropping the `|S| ≤ k` guard (adding nonnegative terms)
  gives `l2DistSq (lowDegreePart f k) g ≤ ∑ S, if ¬S ⊆ J then f̂(S)² else 0`.
- *`hunion`.* Each `S ⊄ J` contains some `i ∉ J` (`Finset.not_subset.mp`), so
  after `Finset.sum_comm` and `influence_eq_sum_fourier` the weight `f̂(S)²` is
  charged to that coordinate by `Finset.single_le_sum`:
  `∑_{S ⊄ J} f̂(S)² ≤ ∑_{i ∉ J} influence i f`.
- *`hinfluence`.* Every `i ∉ J` has `influence i f < τ` (negation of the filter
  condition), so the sum is at most `(#{i ∉ J}) · τ ≤ n · τ`
  (`Finset.sum_const`, `nsmul_eq_mul`, `Finset.card_filter_le`).
- `linarith` chains the last three bounds. ∎

**Remark.** The error bound is `n · τ`, not the sharp Friedgut estimate — the
union bound charges each excluded coordinate its full influence. `friedgut_junta`
absorbs the factor `n` by choosing `τ = ε/(4n)`.

**Used in.** `friedgut_junta` (the `hjunta` step, paired with
`influential_coords_card`). No call sites outside `BooleanAnalysis/KKL.lean`.
