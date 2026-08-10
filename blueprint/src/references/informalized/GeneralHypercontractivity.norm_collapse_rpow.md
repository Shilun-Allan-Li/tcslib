<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/General.lean :: norm_collapse_rpow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Splitting the `p`-th moment along the last coordinate

**Claim.** For `p > 0` and `f : BooleanFunc (n + 1)`,
`expect (fun x => |f x| ^ p)` equals
`expect (fun x' => (1/2) * (|f (Fin.snoc x' false)| ^ p + |f (Fin.snoc x' true)| ^ p))`.
That is, the `p`-th moment over the `(n+1)`-cube is the `n`-cube average of the
two-point average over the final bit.

**Proof.** Immediate: `convert expect_succ_eq_iterated _ using 1`. The general
Fubini step `expect_succ_eq_iterated` says
`expect h = expect (fun x' => (1/2)(h (snoc x' false) + h (snoc x' true)))` for
any `h : BooleanFunc (n+1)`; instantiating `h := fun x => |f x| ^ p` is the
claim, so no arithmetic is needed.

**Remark.** `_hp : 0 < p` is unused — the identity is linear in the integrand and
holds for any exponent; the hypothesis is carried for uniformity with the other
norm lemmas in the file.

**Used in.** `norm_collapse_clean`, which is the form consumed by the induction
step `two_func_hyp_succ`.
