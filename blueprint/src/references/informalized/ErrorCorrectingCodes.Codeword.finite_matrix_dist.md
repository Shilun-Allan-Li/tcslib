<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/LinearCodes.lean :: finite_matrix_dist -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The set of generator matrices mapping a fixed message to a fixed word is finite

**Claim.** Let `α` be a finite field, `v : Codeword n α` and `x : Codeword k α`.
Then the set of `n × k` matrices sending `x` to `v`,

```
{ G : Matrix (Fin n) (Fin k) α | Matrix.mulVec G x = v }
```

is `Set.Finite`.

**Proof.** Three steps, all bookkeeping — the linear condition plays no role.

1. `dist_subset`: the set is contained in `Set.univ` (`intro G _; trivial`).
2. `matrices_fintype`: `Finite.Set.subset` turns that inclusion into
   `Finite ↑{G | Matrix.mulVec G x = v}`, using that
   `Matrix (Fin n) (Fin k) α` is itself a finite type (from `[Fintype α]`).
3. `Set.finite_coe_iff.mp` converts the `Finite` coercion instance into
   `Set.Finite`.

**Used in.** `matrix_dist`, purely as the finiteness certificate needed to form
`Set.Finite.toFinset` and take a cardinality; nothing about the fibre structure
of `G ↦ G · x` is established here.
