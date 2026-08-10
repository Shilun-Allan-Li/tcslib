<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/MRRW.lean :: binomial_tail_entropy_asymptotic -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Binomial tails grow at the binary entropy rate

**Claim.** For real `τ` with `0 ≤ τ` and `τ ≤ 1/2`, the sequence

```
n ↦ Real.logb 2 (∑ j ∈ Finset.range (⌊τ * n⌋₊ + 1), (n.choose j : ℝ)) / n
```

tends to `binaryEntropy τ` along `Filter.atTop`. This is the Lean form of
`∑_{j ≤ ⌊τn⌋} C(n,j) = 2^{n·H(τ) + o(n)}`: the normalized base-2 logarithm of
the binomial tail converges to `H(τ)`, with no error term made explicit.

**Proof.** Not yet formalized — the proof body is `sorry`, so this entry records
a target statement rather than a completed argument. The only justification
offered in the file is the docstring's pointer: it is item (ii) in the proof
sketch of `entropy_growth_of_objective` ("Proposition 4"), where the tail
`∑_{j ≤ t_n} C(n,j)` is to be estimated by Stirling's formula.

**Used in.** Intended as the counting input to `entropy_growth_of_objective`
(itself `sorry`), which bounds `limsup (1/n) · logb 2 (cdKernel n (t n) (a n) 0)`
by `binaryEntropy τ` and is one of the two asymptotic ingredients of
`mrrw_bound`. Note the hypotheses here are the closed-interval ones
`0 ≤ τ ≤ 1/2`, weaker than the strict `0 < τ < 1/2` assumed by the propositions
that consume it, so the endpoints `binaryEntropy_zero` and `binaryEntropy_half`
are also covered.
