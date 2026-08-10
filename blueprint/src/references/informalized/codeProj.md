<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumHamming.lean :: codeProj -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The code projector as an endomorphism of the full space

**Definition.** For a code subspace `C : Submodule ℂ (Hn n)` of the `n`-qubit
space,

```
codeProj C : Hn n →ₗ[ℂ] Hn n
codeProj C = (C.subtypeL.comp (Submodule.orthogonalProjection C)).toLinearMap
```

the orthogonal projection onto `C` followed by the inclusion `C ↪ Hn n`, so that
the result is an operator on the *whole* space rather than a map into `C`. This
is the `Π_C` of the Knill–Laflamme conditions. A `noncomputable def`, no proof
content.

**Remark.** The retyping to `Hn n →ₗ[ℂ] Hn n` is what makes composites such as
`Π_C ∘ E† ∘ F ∘ Π_C` well formed, which is why the definition exists at all.
Well-definedness of `Submodule.orthogonalProjection C` needs `C` to be a
complete subspace; this comes from the `FiniteDimensional ℂ ↥C` instance
declared just above via `FiniteDimensional.finiteDimensional_submodule`, so no
completeness hypothesis appears in the signature.

**Used in.** `codeProj_apply` (the defining simp lemma), `codeProj_mem`,
`codeProj_eq_self_of_mem`, `codeProj_idempotent`, the definitions of
`KnillLaflamme` and `IsNondegenerate`, and `error_subspaces_orthogonal`.
