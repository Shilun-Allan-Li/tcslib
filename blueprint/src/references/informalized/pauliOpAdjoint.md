<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumHamming.lean :: pauliOpAdjoint -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The conjugate-transpose operator of a Pauli string

**Definition.** For a Pauli string `p : PauliString n`,

```
pauliOpAdjoint p : Hn n →ₗ[ℂ] Hn n
pauliOpAdjoint p = Matrix.toEuclideanLin (pauliMatrix p)ᴴ
```

the linear endomorphism of the `n`-qubit space `Hn n = EuclideanSpace ℂ (Fin n →
Fin 2)` given by the conjugate transpose of the `2^n × 2^n` tensor-product
matrix `pauliMatrix p`. It is the companion of `pauliOp p = toEuclideanLin
(pauliMatrix p)`. A `noncomputable def`, no proof content.

**Remark.** Despite the name, this is *defined* as a conjugate transpose, not
obtained from Mathlib's adjoint construction, and no lemma in the file records
`⟪pauliOpAdjoint p x, y⟫ = ⟪x, pauliOp p y⟫`. The adjoint property is instead
re-proved inline where it is needed, as the `h_adj` step of
`error_subspaces_orthogonal`
(`(A.mulVec x) ⬝ᵥ star y = x ⬝ᵥ star (Aᴴ.mulVec y)`). Nor is it proved here that
Pauli operators are unitary, so `pauliOpAdjoint p ∘ pauliOp p = 1` is not
available as a rewrite.

**Used in.** The statements of `KnillLaflamme` and `IsNondegenerate` (the
`Π_C ∘ E† ∘ F ∘ Π_C` expression), and in `error_subspaces_orthogonal`.
