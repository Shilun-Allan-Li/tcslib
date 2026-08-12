<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/KKL.lean :: lowDegreePart -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Low-degree truncation of a Boolean function

**Definition.** For `f : BooleanFunc n` and `k : ℕ`,

`lowDegreePart f k = fun x => ∑ S, if S.card ≤ k then fourierCoeff f S * chiS S x else 0`,

i.e. the Fourier expansion of `f` with every level above `k` deleted. Two
mechanical points that shape all downstream proofs: the sum runs over *all*
`S : Finset (Fin n)` with an `if`-guard rather than over a filtered `Finset`
(so consumers split with `split_ifs` / `by_cases h : S.card ≤ k`), and the
result lives in `BooleanFunc n = BoolCube n → ℝ` — it is real-valued, not
`±1`-valued, even when `f` is.

**Used in.** `fourierCoeff_lowDegreePart` (its Fourier coefficients),
`low_plus_high_eq` (it plus `highDegreePart` recovers `f`), `lowDegree_l2_error`
and `lowDegree_approx` (its L2 error), `lowDegreePart_depends_on_influential`
(it is close to a junta) and `friedgut_junta`, which uses it as the intermediate
function in the triangle-inequality step. No call sites outside
`BooleanAnalysis/KKL.lean`.
