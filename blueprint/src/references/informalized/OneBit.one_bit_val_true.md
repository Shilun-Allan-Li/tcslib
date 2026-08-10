<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/OneBit.lean :: one_bit_val_true -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Value of a one-bit function at `true`

**Claim.** For `f : BooleanFunc 1`,

```
f (fun _ => true) = fourierCoeff f ∅ - fourierCoeff f {0}
```

so with `a = f̂(∅)`, `b = f̂({0})` the value at `true` is `a − b`.

**Proof.** The mirror image of `one_bit_val_false`.

1. `conv_lhs => rw [walsh_expansion f]` expands `f (fun _ => true)` as
   `∑ S : Finset (Fin 1), f̂(S) · χ_S(true)`.
2. `finsetFin1_univ` rewrites the index set to `{∅, {0}}` and
   `Finset.sum_pair finsetFin1_ne` splits it into the two terms.
3. `simp [chiS, boolToSign]` evaluates `χ_∅(true) = 1` and
   `χ_{0}(true) = boolToSign true = -1`; a trailing `ring` normalises
   `a + (-1) · b` to `a − b`. ∎

**Used in.** Together with `one_bit_val_false` it gives the two-point picture of a
one-bit function used by `expect_abs_rpow_one_bit`, and hence by
`one_bit_p2_hypercontractivity`.
