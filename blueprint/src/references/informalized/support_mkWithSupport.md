<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumHamming.lean :: support_mkWithSupport -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# `mkWithSupport` has exactly the prescribed support

**Claim.** For any `S : Finset (Fin n)` and any assignment `f : S → PauliNZ`,

```
support (mkWithSupport S f) = S
```

where `support p = univ.filter (fun i => p i ≠ PauliBasis.I)`. So the string
built from `S` and `f` is non-identity precisely on `S`.

**Proof.** One-line: `classical; ext i; simp [support, mkWithSupport,
PauliNZ.toBasis_ne_I]`.

- `ext i` reduces to `i ∈ support (mkWithSupport S f) ↔ i ∈ S`.
- `simp` unfolds `support` and the dependent `if` of `mkWithSupport`. Outside
  `S` the value is `PauliBasis.I`, so the filter rejects `i`; inside `S` the
  value is `(f ⟨i, _⟩).toBasis`, and `PauliNZ.toBasis_ne_I` supplies the
  required disequality with `PauliBasis.I`.

**Used in.** `card_pauliStringsExactSupport` — it is the "lands in the right
fibre" half of the bijection `S → PauliNZ ≃ pauliStringsExactSupport S`, which
in turn feeds the weight-`j` layer count in `card_pauliErrorsLe`.
