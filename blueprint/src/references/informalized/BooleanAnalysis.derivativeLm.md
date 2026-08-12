<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Basic.lean :: derivativeLm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The discrete derivative as a linear map

**Definition.** `derivativeLm i : BooleanFunc n →ₗ[ℝ] BooleanFunc n` bundles the
`i`-th discrete derivative into an `ℝ`-linear map, by supplying the three fields
of a `LinearMap`:

- `toFun := derivative i`, where
  `derivative i f x = (f (Function.update x i false) - f (Function.update x i true)) / 2`
  — the half-difference of `f` at the two points agreeing with `x` off
  coordinate `i`;
- `map_add' := derivative_add i`, proved by `ext x`, then
  `simp only [derivative, Pi.add_apply]` and `ring`;
- `map_smul' := derivative_smul i`, the same shape with
  `Pi.smul_apply, smul_eq_mul` and `ring`.

Both field proofs are pure real arithmetic once the `Pi` structure is unfolded —
`derivative i` is a fixed linear combination of two evaluations, so additivity
and homogeneity are immediate.

**Remark.** The `false`/`true` order matches the sign convention of
`boolToSign` (`false ↦ +1`, `true ↦ -1`): `Function.update x i false` is the
`+1` input, so this is the textbook `D_i f = (f(xⁱ→⁺¹) - f(xⁱ→⁻¹))/2`, whose
Fourier action deletes `i` from every frequency containing it.

**No `sorry`** anywhere in the block. Two caveats worth recording, both
non-mathematical:

- The declaration carries no docstring — only the line comment
  `-- Derivative is a linear map` above it.
- It is currently **unused**: `derivativeLm` has no references anywhere in
  `TCSlib/` outside its own definition, and `derivative` itself is referenced
  only by `derivative_add`, `derivative_smul` and this bundling. (Repo-wide
  matches for "derivative" elsewhere are all prose in comments, e.g. in
  `Hypercontractivity/` and `BLR/LowDegree.lean`.) The linear-map packaging is
  available but no downstream proof consumes it.

**Used in.** Nothing yet — see above.
