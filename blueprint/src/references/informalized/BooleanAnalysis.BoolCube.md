<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Basic.lean :: BoolCube -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The Boolean hypercube

**Definition.** `BoolCube n := Fin n → Bool` is the domain of the whole
Boolean-analysis layer: a point of the hypercube is a function assigning one bit
to each of the `n` coordinates.

- It is an `abbrev`, hence reducible — Lean unfolds it on sight, so every
  instance already available on the Pi type `Fin n → Bool` (`Fintype`,
  `DecidableEq`, `Inhabited`) applies with no transfer boilerplate. This is what
  makes `∑ x : BoolCube n, f x` legal notation.
- Its cardinality is `2 ^ n`, obtained from `Fintype.card_pi` together with
  `Fintype.card_bool` and `Finset.card_fin` — the chain spelled out by hand
  inside `innerProduct_self_pm_one`.

**Remark.** The docstring calls it `{0,1}ⁿ`, but no arithmetic happens on `Bool`:
every analytic statement first pushes coordinates through `boolToSign`
(`false ↦ 1`, `true ↦ -1`) into `{-1,1} ⊆ ℝ`. `Bool` is the indexing picture and
`boolToSign` is the only bridge to the sign picture.

**Used in.** Every declaration in the file and in the downstream Fourier layer —
as the domain of `BooleanFunc n`, the index of `expect`/`innerProduct`, the
argument of `chiS`, and the type acted on by `flipBit`.
