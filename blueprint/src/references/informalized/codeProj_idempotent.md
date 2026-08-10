<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumHamming.lean :: codeProj_idempotent -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The code projector is idempotent

**Claim.** For `C : Submodule ℂ (Hn n)` and any `x : Hn n`,

```
codeProj C (codeProj C x) = codeProj C x
```

i.e. `Π_C² = Π_C` in pointwise form (the statement is about values, not an
equality of linear maps).

**Proof.** Two steps, both citing the preceding helpers.

1. `apply codeProj_eq_self_of_mem (C := C)` reduces the goal to
   `codeProj C x ∈ C`.
2. `exact codeProj_mem C x` discharges that.

**Remark.** Reviewer note: this lemma is currently **dead** — nothing in
`QuantumHamming.lean` or elsewhere in the library references
`codeProj_idempotent`. The Hamming-bound argument goes through
`error_subspaces_orthogonal` and `error_sphere_dimension`, which use
`codeProj_eq_self_of_mem` directly and never need idempotence. It is retained as
a sanity property of the projector.
