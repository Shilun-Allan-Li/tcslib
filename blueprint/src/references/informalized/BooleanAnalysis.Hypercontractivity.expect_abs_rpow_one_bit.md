<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/OneBit.lean :: expect_abs_rpow_one_bit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The one-bit Lp norm in terms of Fourier coefficients

**Claim.** For `p : ℝ` and `f : BooleanFunc 1`, writing `a = fourierCoeff f ∅` and
`b = fourierCoeff f {0}`,
`expect (fun x => |f x| ^ p) = (|a + b| ^ p + |a - b| ^ p) / 2`.
No hypothesis on `p` is needed — this is a rewriting of the two-point average.

**Proof.** Four rewrites.

1. Unfold `expect` and `uniformWeight`; the weight for `n = 1` is `1/2`.
2. Replace the index set by the explicit pair via `boolCube1_univ`, then
   `Finset.sum_pair boolCube1_ne` writes the sum as the `false` term plus the
   `true` term.
3. `simp only [one_bit_val_false, one_bit_val_true]` substitutes
   `f (fun _ => false) = a + b` and `f (fun _ => true) = a - b`.
4. `norm_num; ring` normalises the `1/2` factor into the stated division. ∎

**Used in.** `BooleanAnalysis.Hypercontractivity.low_norms_one_bit` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/General/TwoPoint.lean`; `BooleanAnalysis.Hypercontractivity.one_bit_p2_hypercontractivity`, `BooleanAnalysis.Hypercontractivity.two_point_rpow_le` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/OneBit.lean`; `BooleanAnalysis.Hypercontractivity.expect_abs_rpow_affine` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/TwoPoint.lean`.
