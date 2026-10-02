<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/EncodingProperties.lean :: encode_go_not_kills_first_clause -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The encoder never kills the clause it selected

**Claim.** Let `f : DNF n` have var-determined literals in every term
(`hnd : ∀ t ∈ f, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂`), let
`ρ₀ σ : Restriction n` satisfy `hE : ∀ v, ρ₀ v = none → σ v = none`, and let `t`
be the first clause of `f` not killed by `ρ₀`
(`f.find? (fun t => decide (¬Term.killedBy t ρ₀)) = some t`). Then for every
literal `l ∈ t` whose variable is free under `ρ₀`,

```
(razborovEncode.go f w enc_fuel path ρ₀ σ []).1 l.var ≠ some l.neg
```

so the produced γ never assigns `l.var` the value that would falsify `l`. Needs
`set_option maxHeartbeats 800000`.

**Proof.** `induction' enc_fuel … generalizing path ρ₀ σ`, with `simp_all +decide`
throughout.

1. Fuel `0`, and fuel `_ + 1` with `path = []`: `razborovEncode.go` returns `σ`,
   and `hE` with `hfree` gives `σ l.var = none ≠ some l.neg`.
2. `path = step :: rest`: first show the encoder's free-literal filter on
   `t.zipIdx` is non-empty — `l` itself sits at index `List.idxOf l t` and is free
   (`List.mem_iff_get`, `Restriction.freeVars`, `List.exists_cons_of_ne_nil`), so
   it equals some `fl :: fls`.
3. `hnd_lits`: any `m` in `fl :: fls` with `m.1.var = l.var` has `m.1 = l` — via
   `List.mem_filter`, `List.mem_zipIdx`, `List.getElem_mem` and `hnd` applied to
   `t` (a member of `f` by `List.mem_of_find?_eq_some`).
4. `by_cases hpcl` on whether the clause pass leaves `l.var` free in ρ₀.
   - Free: `processClauseLits_path_nil_of_rho_none_and_mem` forces the remaining
     path to `[]`, so one more unfold of `razborovEncode.go` returns the clause
     pass's σ directly.
   - Fixed: `encode_go_fst_acc` then `encode_go_fst_nonfree` show
     γ `l.var` = the clause pass's σ at `l.var` (`hkey`).
   Either way `processClauseLits_sigma_ne_neg … (by rw [hE _ hfree]; simp)` closes
   the goal: `processClauseLits` sets `l.var` to the *satisfying* direction
   `some (!l.neg)`, never to `some l.neg`.

**Used in.** `find_clause_preserved_in_encode` (`Switching/RoundTrip.lean`) — the
step that makes the decoder's `find?` select the same clause as the encoder's.
