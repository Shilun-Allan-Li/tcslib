<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Bonami.lean :: sum_boolCube_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Splitting a sum over the cube along the last coordinate

**Claim.** For any `φ : BoolCube (n + 1) → ℝ`,

```
∑ x : BoolCube (n+1), φ x
  = ∑ x : BoolCube n, φ (Fin.snoc x false) + ∑ x : BoolCube n, φ (Fin.snoc x true)
```

Summing over `{0,1}^{n+1}` is the same as summing the two last-coordinate
restrictions over `{0,1}^n`.

**Proof.**

1. Reindex `{0,1}^{n+1}` by `{0,1}^n × Bool`: the auxiliary step `h_split`
   applies `Finset.sum_bij` with the bijection
   `x ↦ (Fin.init x, x (Fin.last n))`. Injectivity is checked coordinatewise
   with `funext_iff` and `Fin.lastCases` (every index is either a `castSucc` or
   `Fin.last n`), and surjectivity by exhibiting `Fin.snoc b.1 b.2`.
2. Turn the product sum into a double sum with `Finset.sum_product`, then
   evaluate the inner two-element `Bool` sum with `Finset.sum_eq_add`, giving
   the `false` and `true` terms.
3. `Finset.sum_add_distrib` / `simp_all` / `aesop` recombine the two halves into
   the stated right-hand side.

**Used in.** The workhorse for every last-coordinate decomposition in this file:
`uniformWeight_succ` partners it in `fourierCoeff_avgLast`, `expect_succ_eq`,
`second_moment_decomp` and `degree_avgLast`.

**Note.** The declaration carries a plain `/- ... -/` comment rather than a
doc-comment, and the proof uses `erw` at one step.
