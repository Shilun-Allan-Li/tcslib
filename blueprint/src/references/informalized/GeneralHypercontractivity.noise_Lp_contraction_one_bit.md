<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/General.lean :: noise_Lp_contraction_one_bit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# `L^q` contractivity of the noise operator on one bit

**Claim.** For `1 ≤ q`, `0 ≤ ρ ≤ 1` and `g : BooleanFunc 1`,
`(expect (fun x => |noiseOp ρ g x| ^ q)) ^ (1/q) ≤ (expect (fun x => |g x| ^ q)) ^ (1/q)`,
i.e. `‖T_ρ g‖_q ≤ ‖g‖_q` for a single-bit function.

**Proof.** Reduce to a two-point inequality and apply convexity.

1. `unfold noiseOp`, `expect`, `uniformWeight`; then
   `rw [show (Finset.univ : Finset (BoolCube 1)) = {fun _ => false, fun _ => true} by decide]`
   and `Finset.sum_pair`, together with
   `rw [show (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} by decide]`,
   writes both sides in terms of `a = fourierCoeff g ∅` and `b = fourierCoeff g {0}`:
   `T_ρ g` takes the values `a ± ρb` while `g` takes `a ± b`
   (`one_bit_val_false`, `one_bit_val_true`).
2. `h_jensen`: for all `a b`, `|a + ρb|^q + |a − ρb|^q ≤ |a + b|^q + |a − b|^q`.
   - `h_abs`: `|a + ρb| ≤ (1+ρ)/2 · |a+b| + (1−ρ)/2 · |a−b|` and symmetrically for
     `|a − ρb|`, by `abs_le` and case analysis `abs_cases` on `a ± b` plus
     `nlinarith` (this is where `0 ≤ ρ ≤ 1` is used).
   - `fun t => t ^ q` is convex on `Set.Ici 0` (`convexOn_rpow`, needs `1 ≤ q`), so
     `ConvexOn.2` gives `((1+ρ)/2 · x + (1−ρ)/2 · y)^q ≤ (1+ρ)/2 · x^q + (1−ρ)/2 · y^q`.
   - Combine with `Real.rpow_le_rpow` on `h_abs` and add the two bounds; the
     weights `(1±ρ)/2` recombine to `1` (`ring`).
3. Instantiate `h_jensen` at `(a, b)` and finish with `Real.rpow_le_rpow` for the
   outer exponent `1/q`.

**Remark.** Currently **dead code**: nothing in the repository calls it. The
`n`-dimensional statement it specializes is proved independently as
`trivial_contractivity`, via the kernel/Jensen route
(`noiseOp_abs_rpow_le_kernel_avg` + `noiseKernel_sum_left`).
