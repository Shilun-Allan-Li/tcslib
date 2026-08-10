<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/General.lean :: avg_rpow_ge_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The symmetric average of (1±b)^p is at least 1

**Claim.** For real `p ≥ 1` and `0 ≤ b ≤ 1`,

`1 ≤ ((1 + b) ^ p + (1 - b) ^ p) / 2`,

the `rpow` powers being taken at the nonnegative bases `1 + b` and `1 - b`.

**Proof.** Jensen at the midpoint.

1. `convexOn_rpow (by linarith)` gives `ConvexOn ℝ (Set.Ici 0) (fun x => x ^ p)`
   for `p ≥ 1`.
2. Apply its defining inequality (`ConvexOn.2`) at the points `1 + b` and `1 - b`
   — both in `Set.Ici 0` — with weights `1/2, 1/2`.
3. The convex combination is `1`, and `1 ^ p = 1`, so the left side of Jensen is
   `1`; `convert … using 1 <;> norm_num <;> ring_nf` reconciles the two forms.

**Note.** A two-point special case of Jensen; as written it has no consumers
anywhere in the repository (see report).
