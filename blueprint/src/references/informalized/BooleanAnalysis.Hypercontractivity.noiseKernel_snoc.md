<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/General/Kernel.lean :: noiseKernel_snoc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The noise kernel factors along the last coordinate

**Claim.** For any `ρ : ℝ`, `x' y' : BoolCube n` and bits `b b' : Bool`,

`noiseKernel ρ (Fin.snoc x' b) (Fin.snoc y' b')
   = noiseKernel ρ x' y' * ((1 + ρ * boolToSign b * boolToSign b') / 2)`.

That is, the product defining the kernel on the `(n+1)`-cube splits into the
`n`-dimensional kernel on the first `n` coordinates times the single one-bit
factor coming from the appended coordinate.

**Proof.** A one-liner: `unfold noiseKernel`, then
`simp +decide [Fin.prod_univ_castSucc]` peels the last factor off the product
over `Fin (n+1)` and evaluates `Fin.snoc` at `castSucc` and at `last`; `ring`
finishes.

**Used in.** `BooleanAnalysis.Hypercontractivity.weighted_sum_succ_decomp` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/General/Kernel.lean`.
