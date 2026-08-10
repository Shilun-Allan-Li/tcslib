<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: extendFromC -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Extending a pair of functions on `C` by zero

**Definition.** For `C : Finset (Fin n)`, `extendFromC C` is the `F p`-linear map

```
(C → F p) × (C → F p) →ₗ[F p] V_sub C
```

sending `⟨f, g⟩` to the vector of `V n p` whose two components are
`fun i => if h : i ∈ C then f ⟨i, h⟩ else 0` and the same with `g` — i.e. the
pair is transplanted onto the coordinates of `C` and padded with zeros
elsewhere. The dependent `if` (`dite`) supplies the membership proof needed to
index `f`.

- Landing in `V_sub C` is discharged by `intro j hj; constructor <;> simp [hj]`:
  for `j ∉ C` both branches take the `else` value `0`, which is exactly the
  defining condition of `V_sub`.
- `map_add'` and `map_smul'`: `apply Subtype.ext`, then
  `ext i <;> by_cases hi : i ∈ C <;> simp [hi]` — on `C` the operation is the one
  on `C → F p`, off `C` both sides are `0`.

**Used in.** `restrictToC_extendFromC` and `extendFromC_restrictToC`, which make
it the inverse half of `V_sub_iso`.
