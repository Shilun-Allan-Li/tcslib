<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: V_sub_iso -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The support subspace `V_C` is isomorphic to `(F_p^C)²`

**Definition.** For `C : Finset (Fin n)`, `V_sub_iso C` is the `F p`-linear
equivalence

```
V_sub C ≃ₗ[F p] (C → F p) × (C → F p)
```

assembled from maps already in place:

- `toFun := restrictToC C` and `invFun := extendFromC C`;
- `left_inv := extendFromC_restrictToC C` and
  `right_inv := restrictToC_extendFromC C` — the two previously proved
  round-trip identities;
- `map_add'`, `map_smul'` are inherited verbatim as
  `(restrictToC C).map_add'` and `(restrictToC C).map_smul'`.

So the definition contributes no new mathematics: it only packages
`restrictToC`/`extendFromC` as mutually inverse linear maps.

**Used in.** `dim_V_sub`, which transports `finrank` across the equivalence
(`LinearEquiv.finrank_eq`, then `Module.finrank_prod` and `two_mul`) to conclude
`Module.finrank (F p) (V_sub C) = 2 * C.card`.
