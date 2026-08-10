<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumHamming.lean :: codeProj_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Applying the code projector is the orthogonal projection, coerced

**Claim.** For `C : Submodule ℂ (Hn n)` and `x : Hn n`,

```
codeProj C x = (Submodule.orthogonalProjection C x : Hn n)
```

i.e. evaluating the endomorphism `codeProj C` at `x` is the same as taking
`Submodule.orthogonalProjection C x : ↥C` and coercing it back into `Hn n`.

**Proof.** Immediate from `simp [codeProj]`: unfolding `codeProj` exposes the
composition `C.subtypeL ∘ orthogonalProjection C`, whose `toLinearMap`
application `simp` reduces to the coercion of the projection.

**Remark.** This is the bridging lemma between the "operator on `Hn n`" view
used in the Knill–Laflamme statements and the "map into `↥C`" view that Mathlib's
projection API is phrased in. It carries `@[simp]`, so it fires automatically and
most later reasoning about `codeProj` happens in the Mathlib idiom.

**Used in.** `codeProj_mem`, and inside `error_subspaces_orthogonal` (both as an
explicit `rw` and via `simp_all`).
