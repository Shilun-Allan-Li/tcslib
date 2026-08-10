<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Bonami.lean :: expect_fourth_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Fourth moments are non-negative

**Claim.** For `f : BooleanFunc n`, `0 ≤ expect (fun x => f x ^ 4)`.

**Proof.** A granular helper. Take the product form
`expect_sq_nonneg_prod (fun x => f x ^ 2) (fun x => 1)`, which gives
`0 ≤ expect (fun x => (f x ^ 2) ^ 2 * 1 ^ 2)`, and reconcile the two integrands
with `convert … using 1` followed by `norm_num [sq]; ring_nf`. ∎

**Used in.** `bonami_expect` (`hA`, `hB`: non-negativity of the fourth moments of
`avgLast f` and `diffLast f`) and `Hypercontractivity/Simple.lean`.
