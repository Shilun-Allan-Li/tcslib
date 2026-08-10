<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Simple.lean :: noiseOp_snoc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The noise operator splits along the last coordinate

**Claim.** For `ρ : ℝ`, `f : BooleanFunc (n+1)`, `x : BoolCube n` and `b : Bool`,

`noiseOp ρ f (Fin.snoc x b) = noiseOp ρ (avgLast f) x + boolToSign b * ρ * noiseOp ρ (diffLast f) x`.

Evaluating `T_ρ f` at a point whose last bit is `b` is the same as applying `T_ρ`
separately to the last-coordinate average `avgLast f` and half-difference
`diffLast f` on the `n`-cube, the second contribution carrying the extra factor
`ρ` and the sign of `b`.

**Proof.** Both sides are sums over frequencies; the proof matches them term by
term after splitting the frequency set.

1. `convert finset_fin_succ_sum_partition (fun S ↦ ρ ^ S.card * fourierCoeff f S * chiS S (Fin.snoc x b))`
   rewrites the left side (which is `noiseOp` unfolded, `∑ S : Finset (Fin (n+1))`)
   as the sum over lifted sets `T.image Fin.castSucc` plus the sum over
   `T.image Fin.castSucc ∪ {Fin.last n}`. `congr! 1` then splits into the two
   matching goals.
2. Lifted sets ↦ `avgLast`: `Finset.sum_congr` termwise, then
   `← fourierCoeff_avgLast` replaces `f̂(T.image castSucc)` by
   `(avgLast f)^(T)`, and `card_image_castSucc` plus `chiS_snoc_castSucc`
   handle `|T.image castSucc| = |T|` and the character's indifference to the
   last bit.
3. Sets containing `Fin.last n` ↦ `diffLast`: expand `noiseOp ρ (diffLast f) x`
   by `rfl` to its Fourier sum, distribute the scalar with `Finset.mul_sum`, and
   termwise apply `fourierCoeff_diffLast`, `card_image_castSucc_union_last`
   (cardinality `|T| + 1`, the source of the extra `ρ`) and
   `chiS_snoc_with_last` (the source of `boolToSign b`); `ring` finishes. ∎

**Used in.** `fourth_moment_noise_decomp` and `noise_qth_moment_decomp`, which
turn this pointwise identity into the moment recursions driving
`hypercontractivity_2_4` and `hypercontractivity_2_2k`.
