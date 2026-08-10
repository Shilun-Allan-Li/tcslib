<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/RoundTrip.lean :: find_clause_preserved_in_encode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The decoder locates the same clause as the encoder

**Claim.** Let `f` have pairwise variable-distinct literals inside each clause
(`hnd`), and suppose the encoder's first non-killed clause under `ρ₀` is
`t_clause`, i.e. `f.find? (fun t => ¬t.killedBy ρ₀) = some t_clause`. Suppose the
decoder's restriction `ρ₀_dec` agrees with the encoder output `γ =
(razborovEncode.go f w enc_fuel path ρ₀ σ []).1` at every variable free in `ρ₀`
(`hB`), agrees with `ρ₀` at every fixed variable (`hD`), and `σ` is free wherever
`ρ₀` is (`hE`). Then `f.find? (fun t => ¬t.killedBy ρ₀_dec) = some t_clause` as
well.

**Proof.** By `first_clause_preserved` it suffices to show `t_clause` is not
killed by `ρ₀_dec` (`hD` handles the earlier clauses, which stay killed). So take
a literal `l ∈ t_clause` with `Literal.killedBy l ρ₀_dec` and split on the status
of `l.var` in `ρ₀`.

1. `ρ₀ l.var = none`: rewrite the killing hypothesis with `hB`, so `γ` kills `l`.
   That contradicts `encode_go_not_kills_first_clause`, which is exactly the
   statement that the encoder never fixes a free literal of its own first clause
   against that clause (this is where `hnd` and `hE` are consumed).
2. `ρ₀ l.var ≠ none`: rewrite with `hD`, so `l` witnesses `Term.killedBy t_clause ρ₀`,
   contradicting `List.find?_some hfind_enc`, which says `t_clause` is *not*
   killed by `ρ₀`.

**Used in.** `go_roundtrip_gen` — it is what lets the decoder's `find?` step be
rewritten by `hfind_dec` and so replay the encoder's clause choice.
