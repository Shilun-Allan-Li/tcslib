<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/KKL.lean :: max_influence_from_sum_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# L2 pigeonhole: some influence is at least the L2/L1 ratio

**Claim.** If `0 < totalInfluence f`, there is `i : Fin n` with
`influence i f ≥ (∑ j, influence j f ^ 2) / totalInfluence f`.

**Proof.**

- `n > 0`: otherwise `interval_cases n` makes the influence sum empty and
  `simp [totalInfluence]` contradicts `hI`.
- Pick a maximizer: `Finset.exists_max_image` on `fun i => influence i f` over
  the nonempty `Finset.univ` (`Finset.univ_nonempty_iff`, `Fin.pos_iff_nonempty`)
  gives `j` with `hj_max`.
- Clear the denominator with `div_le_iff₀ hI` and bound
  `∑ i, influence i f ^ 2 ≤ ∑ i, influence j f * influence i f` termwise
  (`rw [sq]`, then `mul_le_mul_of_nonneg_right (hj_max i _)` with influence
  nonnegativity from `influence_eq_sum_fourier` + `positivity`);
  `Finset.mul_sum` folds the right side into `influence j f * totalInfluence f`. ∎

**Note.** Dead declaration: nothing in the repository calls
`max_influence_from_sum_sq`. It was intended as the pigeonhole step of the KKL
argument, but `KKL_balanced` uses the weaker averaging bound
`max_influence_lower_bound` (`Basic.lean`) instead, and its hard case is left as
**`sorry`** (KKL.lean:618).
