<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/KKL.lean :: highDegreePart -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# High-degree part of a Boolean function

**Definition.** For `f : BooleanFunc n` and `k : ℕ`,

`highDegreePart f k = fun x => ∑ S, if k < S.card then fourierCoeff f S * chiS S x else 0`,

the Fourier expansion of `f` restricted to levels strictly above `k`. It is the
exact complement of `lowDegreePart f k`: the two guards `S.card ≤ k` and
`k < S.card` partition the index set, which is what `low_plus_high_eq` exploits.

**Used in.** Only two places, both in `KKL.lean`: `low_plus_high_eq`
(`lowDegreePart f k x + highDegreePart f k x = f x`) and `lowDegree_l2_error`,
where it is immediately re-expressed as `fun x => f x - lowDegreePart f k x`
(the `hdef` step) so that its Fourier coefficients can be computed by
subtraction. Nothing outside `BooleanAnalysis/KKL.lean` mentions it.

**Remark.** No lemma states the "obvious" facts about it directly (e.g. that its
Fourier coefficient at `S` is `f̂(S)` iff `k < |S|`); that computation appears
inline as `hfour` inside `lowDegree_l2_error`.
