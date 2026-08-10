<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Bonami.lean :: fourierCoeff_diffLast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Fourier coefficients of the half-difference

**Claim.** For `f : BooleanFunc (n + 1)` and `S : Finset (Fin n)`,

```
fourierCoeff (diffLast f) S = fourierCoeff f (S.image Fin.castSucc ∪ {Fin.last n})
```

Taking the half-difference of `f` along the last coordinate reads off exactly
those Fourier coefficients of `f` whose frequency set contains the last
coordinate: the coefficient of `diffLast f` at `S` is the coefficient of `f` at
`S` lifted by `Fin.castSucc` together with `Fin.last n`.

**Proof.**

1. Unfold everything in sight — `diffLast`, `fourierCoeff`, `innerProduct`,
   `expect`, `chiS`, `restrictLast` — so both sides are explicit weighted sums
   over cubes, and rewrite the weight with `uniformWeight_succ`.
2. Split the index set: prove
   `(univ : Finset (Fin (n+1) → Bool))` is the union of the images of
   `Fin.snoc · false` and `Fin.snoc · true`, by `Fin.lastCases` on
   `x (Fin.last n)`; the two images are disjoint
   (`norm_num [Finset.disjoint_left]`), so `Finset.sum_union` applies.
3. Each image sum becomes a sum over `BoolCube n` via `Finset.sum_image`, whose
   injectivity side goals are `fun x y h => by simpa using congrArg Fin.init h`.
4. On each branch the character factorises: `Finset.prod_union` and
   `Finset.prod_image` give `χ_{S.image castSucc ∪ {last n}} (Fin.snoc x b)
   = χ_S x · boolToSign b`, so the `false` branch contributes `+χ_S x` and the
   `true` branch `−χ_S x` — precisely the half-difference.
5. `ring_nf` together with `Finset.sum_add_distrib` / `Finset.sum_mul` /
   `mul_add` reassembles the two branches into `fourierCoeff (diffLast f) S`.

**Used in.** `SimpleHypercontractivity.noiseOp_snoc` (with
`card_image_castSucc_union_last` supplying `|S| + 1` for the noise exponent);
`degree_diffLast` reproves the same identity inline rather than calling it.
