<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/KKL.lean :: expect_sq_pm_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A ±1-valued function has second moment one

**Claim.** If `f : BooleanFunc n` is `±1`-valued (`isPmOne f`), then
`expect (fun x => f x ^ 2) = 1`.

**Proof.** A restatement of an existing fact across the `x * x` / `x ^ 2`
divide.

1. `have h := innerProduct_self_pm_one f hf` gives `innerProduct f f = 1`
   (`Basic.lean`) — the substance of the claim.
2. `simp only [innerProduct] at h` unfolds it to
   `expect (fun x => f x * f x) = 1`.
3. `convert h using 1` then `congr 1; ext x; ring` reconciles the two
   integrands, `f x ^ 2 = f x * f x`. ∎

**Remark.** No new mathematics — purely the bookkeeping step of moving from the
inner-product spelling used in `Basic.lean` to the moment spelling used in the
hypercontractivity files, where `expect (fun x => f x ^ 2)` is the normal form.

**Used in.** Nothing — no other declaration in the repository references it.
`KKL_balanced` and `balanced_totalInfluence_ge_one`, the natural consumers, both
reach for `parseval_pm_one` instead (the Fourier-side form of the same
normalisation), so this "Step 04" of the file's plan is stated but never called
on.
