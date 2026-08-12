<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/KKL.lean :: sum_fourier_sq_eq_expect_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Parseval with a square on both sides

**Claim.** For `f : BooleanFunc n`,
`∑ S, fourierCoeff f S ^ 2 = expect (fun x => f x ^ 2)`.

**Proof.** Two rewrites.

1. `← parseval` replaces the Fourier sum by the inner product `innerProduct f f`,
   and unfolding `innerProduct` turns the goal into
   `expect (fun x => f x * f x) = expect (fun x => f x ^ 2)`.
2. `congr 1; ext x; ring` closes the gap between `f x * f x` and `f x ^ 2`.

**Remark.** Purely a shape adjustment to `parseval` (which is stated with a
product, `⟪f, f⟫ = ∑_S f̂(S)²`), so that a proof reasoning about `E[f²]` need not
re-derive `a * a = a ^ 2` under a binder. It is currently **unused**:
`KKL_balanced` gets the `±1` case directly from `parseval_pm_one`, and
`expect_sq_pm_one` — the neighbouring lemma that does need `E[f²]` — goes through
`innerProduct_self_pm_one` instead.
