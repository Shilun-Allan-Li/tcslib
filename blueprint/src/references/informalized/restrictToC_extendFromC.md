<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: restrictToC_extendFromC -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Extending then restricting a coordinate pair is the identity

**Claim.** For every `C : Finset (Fin n)` and every `x : (C → F p) × (C → F p)`,
`restrictToC C (extendFromC C x) = x`. That is, `extendFromC C` — which pads a
pair of functions on `C` by zero outside `C` to land in the support subspace
`V_sub C` — is a right inverse of the restriction map `restrictToC C`.

**Proof.**

1. `rintro ⟨f, g⟩` splits `x` into its two coordinate functions.
2. `Prod.ext` reduces the goal to the two components separately, and `funext c`
   to a single index `c : C`.
3. Each component is then closed by `simp [restrictToC, extendFromC]`: unfolding
   both definitions, the `c`-th entry is `if h : c.1 ∈ C then f ⟨c.1, h⟩ else 0`,
   and the `dif` condition holds because `c : C` carries its own membership
   proof, so the value is `f c`.

**Used in.** Supplies the `right_inv` field of the linear equivalence
`V_sub_iso C : V_sub C ≃ₗ[F p] (C → F p) × (C → F p)`, whose companion
`left_inv` is `extendFromC_restrictToC`. That equivalence is what gives
`dim_V_sub : finrank (V_sub C) = 2 * C.card`.
