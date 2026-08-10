<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/EncodingProperties.lean :: foldl_sigma_stable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The decoder's σ-fold fixes untargeted variables

**Claim.** Let `t : Term n`, `entries : List (ℕ × Bool)`, `σ : Restriction n` and
`v : Fin n`, and suppose no entry targets `v`: for every `e ∈ entries`, if
`t.drop e.1 = l :: rest` then `l.var ≠ v`. Then

```
entries.foldl (fun σ e => match t.drop e.1 with | [] => σ | l :: _ => Function.update σ l.var none) σ v = σ v
```

This is the σ half of the fold that `razborovDecode.processEntries` performs on
one clause's aux block.

**Proof.** Induction on `entries`, generalizing `σ`.

1. `[]`: `simp` — the fold is the identity.
2. `e :: es`: `simp only [List.foldl_cons]`; specialize the hypothesis to `e`
   (`List.mem_cons_self`) and to the tail (`List.mem_cons_of_mem`).
3. `match h : t.drop e.1` with:
   - `[]`: the step is a no-op, so `exact ih _ hne_es`.
   - `l :: _`: `rw [ih _ hne_es]` pushes the claim onto the single update, then
     `simp only [Function.update_apply, (hne_e l _ h).symm, ite_false]` discharges
     it because `l.var ≠ v`.

**Used in.** `roundtrip_inv_hC'`, `roundtrip_inv_hD'` and `go_roundtrip_gen` in
`Switching/RoundTrip.lean`.
