<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/EncodingProperties.lean :: foldl_rho_stable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The decoder's ρ₀-fold fixes untargeted variables

**Claim.** Let `t : Term n`, `entries : List (ℕ × Bool)`, `ρ₀ : Restriction n` and
`v : Fin n`, and suppose no entry targets `v`: for every `e ∈ entries`, if
`t.drop e.1 = l :: rest` then `l.var ≠ v`. Then

```
entries.foldl (fun ρ₀ e => match t.drop e.1 with | [] => ρ₀ | l :: _ => Function.update ρ₀ l.var (some e.2)) ρ₀ v = ρ₀ v
```

This is the ρ₀ half of the fold `razborovDecode.processEntries` performs on one
clause's aux block; the only difference from `foldl_sigma_stable` is that the
update writes `some e.2` rather than `none`.

**Proof.** Induction on `entries`, generalizing `ρ₀`.

1. `[]`: `simp`.
2. `e :: es`: `simp only [List.foldl_cons]`, specialize the hypothesis to `e`
   (`List.mem_cons_self`) and to the tail (`List.mem_cons_of_mem`).
3. `match h : t.drop e.1` with:
   - `[]`: no-op step, `exact ih _ hne_es`.
   - `l :: _`: `rw [ih _ hne_es]`, then
     `simp only [Function.update_apply, (hne_e l _ h).symm, ite_false]` since
     `l.var ≠ v`.

**Used in.** `roundtrip_inv_hD'` and `go_roundtrip_gen` in
`Switching/RoundTrip.lean`.
