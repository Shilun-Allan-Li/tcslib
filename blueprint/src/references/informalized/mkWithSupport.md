<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumHamming.lean :: mkWithSupport -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Building a Pauli string from a support set and an assignment

**Definition.** Given a set of qubit positions `S : Finset (Fin n)` and a choice
of non-identity Pauli at each of them, `f : S → PauliNZ`, the Pauli string
`mkWithSupport S f : PauliString n` is

```
mkWithSupport S f i = if h : i ∈ S then (f ⟨i, h⟩).toBasis else PauliBasis.I
```

— the operator `f i` on qubits inside `S`, and identity everywhere else. The
`if h : …` is a dependent `if`, since `f` needs the membership proof to be
applied. A plain `def`, no proof content.

**Remark.** This is the "choose the support, then assign `X`/`Y`/`Z`" half of
the Pauli counting argument, packaged as a function so that it can serve as the
map in a bijection. Its correctness — that the support really comes out as `S`,
so no cancellation or collapsing occurs — is `support_mkWithSupport`.

**Used in.** `support_mkWithSupport`, and in
`card_pauliStringsExactSupport`, where `Finset.image (mkWithSupport S ·) univ`
is shown to be exactly `pauliStringsExactSupport S` and the map is shown
injective, yielding the count `3 ^ S.card`.
