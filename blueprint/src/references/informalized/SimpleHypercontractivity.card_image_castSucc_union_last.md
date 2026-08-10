<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Simple.lean :: card_image_castSucc_union_last -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Adding the last coordinate to a lifted subset increases its size by one

**Claim.** For `S : Finset (Fin n)`,
`(S.image Fin.castSucc ∪ {Fin.last n}).card = S.card + 1`.

**Proof.** `rw [Finset.card_union, Finset.card_image_of_injective] <;>
norm_num [Function.Injective]`:

1. `Finset.card_union` turns the goal into
   `|S.image castSucc| + 1 - |S.image castSucc ∩ {Fin.last n}|`.
2. `Finset.card_image_of_injective` replaces `|S.image castSucc|` by `|S|`, with
   the injectivity side goal for `Fin.castSucc` closed by
   `norm_num [Function.Injective]`.
3. The same `norm_num` sees that `Fin.last n` is not of the form `castSucc i`,
   so the intersection is empty and the correction term vanishes. ∎

**Used in.** `noiseOp_snoc`, on the half of the last-coordinate partition where
the frequency set contains `Fin.last n`; the `+1` is what produces the extra
factor of `ρ` in the `diffLast` term.
