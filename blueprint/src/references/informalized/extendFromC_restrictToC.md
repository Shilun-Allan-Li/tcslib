<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: extendFromC_restrictToC -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Restricting then extending a supported vector is the identity

**Claim.** For every `C : Finset (Fin n)` and every `x : V_sub C`,
`extendFromC C (restrictToC C x) = x`. That is, discarding the coordinates
outside `C` and then padding back with zeros recovers the original vector — the
left-inverse direction, which needs the defining property of `V_sub C`.

**Proof.** Write `x = ⟨v, hv⟩` with `v : V n p` and `hv : v ∈ V_sub C`.

1. `simpa [V_sub] using hv` turns the membership into the usable form
   `hv' : ∀ j ∉ C, v.1 j = 0 ∧ v.2 j = 0`.
2. `Subtype.ext` drops to the underlying vector and `ext i` to a single
   coordinate `i`, in each of the two components.
3. `by_cases hi : i ∈ C`. On `C`, the round trip is definitional:
   `simp [extendFromC, restrictToC, hi]`.
4. Off `C`, the padded value is `0` while the original is `v.1 i` (resp.
   `v.2 i`); these agree by `hv' i hi`, fed to
   `simp [extendFromC, restrictToC, hi, h0]`.

**Remark.** Step 4 is the only place the support hypothesis is used, and it is
why the equivalence is stated on `V_sub C` rather than on all of `V n p`: the
restriction map genuinely loses information off `C`.

**Used in.** The `left_inv` field of `V_sub_iso C`, paired with
`restrictToC_extendFromC`; together they yield `dim_V_sub`.
