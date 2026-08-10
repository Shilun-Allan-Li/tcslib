<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/EncodingProperties.lean :: encode_go_fst_nonfree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# γ agrees with σ at variables already fixed by ρ₀

**Claim.** For all `f : DNF n`, `w`, `fuel`, `path`, `ρ₀ σ : Restriction n`,
`acc` and `v : Fin n` with `ρ₀ v ≠ none`,

```
(razborovEncode.go f w fuel path ρ₀ σ acc).1 v = σ v
```

The encoder only ever writes to variables that are free under the current `ρ₀`,
so a variable that is already fixed keeps its incoming σ-value.

**Proof.** Induction on `fuel`, generalizing `path`, `ρ₀`, `σ`, `acc`.

1. Base cases (`fuel = 0` for either shape of `path`, and `fuel + 1` with
   `path = []`): the loop returns `(σ, acc)`, so `simp [razborovEncode.go]`.
2. `fuel + 1`, `path = step :: rest`: `simp only [razborovEncode.go]` then
   `split` on `f.find?`; the `none` branch is `rfl`.
3. In the `some t` branch, `generalize` the filtered free-literal list
   `List.filter (·.1.var ∈ Restriction.freeVars ρ₀) (List.zipIdx t)` to `fli`
   and `match` on it. `fli = []` returns `σ` (`simp`).
4. For `fli = fl :: fls`: from `List.mem_filter`, `Restriction.freeVars`,
   `Finset.mem_filter` and `Option.isNone_iff_eq_none`, every `p` in the list has
   `ρ₀ p.1.var = none`; combined with `hv : ρ₀ v ≠ none` this gives
   `hne : ∀ p ∈ fl :: fls, p.1.var ≠ v`.
5. Apply the induction hypothesis to the recursive call, discharging its
   non-freeness side condition with `processClauseLits_rho_ne_none` (this clause
   pass cannot make `ρ₀ v` become `none`), then close with
   `processClauseLits_sigma_stable _ _ _ _ _ hne`.

**Used in.** `encode_go_fst_sigma_indep_at_free`,
`encode_go_not_kills_first_clause`, and the invariant instantiation in
`go_roundtrip` (`Switching/RoundTrip.lean`).
