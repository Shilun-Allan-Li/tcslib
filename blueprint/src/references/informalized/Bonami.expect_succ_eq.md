<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Bonami.lean :: expect_succ_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Expectation on the (n+1)-cube splits over the last coordinate

**Claim.** For `φ : BooleanFunc (n+1)`,
`expect φ = (expect (restrictLast φ false) + expect (restrictLast φ true)) / 2`,
where `restrictLast φ b x = φ (Fin.snoc x b)`.

**Proof.**

1. `unfold expect restrictLast`, turning both sides into weighted sums.
2. `sum_boolCube_succ` splits `∑ x : BoolCube (n+1), φ x` into
   `∑ x : BoolCube n, φ (snoc x false) + ∑ x : BoolCube n, φ (snoc x true)`.
3. `uniformWeight_succ` rewrites `uniformWeight (n+1)` as `uniformWeight n / 2`,
   after which `ring` finishes. ∎

**Used in.** `fourth_moment_decomp` (via `convert expect_succ_eq (fun x => f x ^ 4)`),
the step that turns `𝔼[f⁴]` into the average of the two restrictions before the
`avgLast`/`diffLast` substitution.
