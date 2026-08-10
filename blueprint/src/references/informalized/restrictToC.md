<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: restrictToC -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Restricting a vector supported on `C` to its `C`-coordinates

**Definition.** For `C : Finset (Fin n)`, `restrictToC C` is the `F p`-linear map

```
V_sub C →ₗ[F p] (C → F p) × (C → F p)
```

that sends `⟨v, _⟩` — a vector of `V n p = (Fin n → F p) × (Fin n → F p)` whose
coordinates outside `C` vanish — to the pair of component functions restricted
to `↑C`, namely `(fun c => v.1 c.1, fun c => v.2 c.1)`. The `V_sub C`-membership
proof is discarded; only the underlying pair is read.

The two linearity fields are routine:

- `map_add'`: `rintro ⟨x, hx⟩ ⟨y, hy⟩` then `ext c <;> simp` — addition on
  `V_sub C` is the componentwise addition of `V n p`.
- `map_smul'`: `rcases` the argument, then `ext c <;> simp` — likewise for
  scalar multiplication.

Note this is only the forward half of a bijection; nothing here records that the
map is injective or surjective.

**Used in.** `restrictToC_extendFromC` / `extendFromC_restrictToC` (the two
round-trip identities) and hence `V_sub_iso`, which is what `dim_V_sub` uses to
get `dim V_C = 2|C|`.
