<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/EncodingProperties.lean :: decode_go_preserves_none -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The decoder loop never un-frees a variable

**Claim.** For any `f : DNF n`, width bound `w`, fuel `fuel`, restrictions
`σ ρ₀ : Restriction n`, aux list `aux : List (ℕ × Bool)` and variable `v`: if
`σ v = none` then `(razborovDecode.go f w fuel σ ρ₀ aux).1 v = none`. That is,
the decoder's σ-component keeps `v` free for the whole run.

**Proof.** Induction on `fuel`, generalizing `σ`, `ρ₀` and `aux`.

1. `fuel = 0`: `cases aux <;> simp [razborovDecode.go, hv]` — both `go`
   equations return `σ` unchanged.
2. `fuel + 1` with `aux = []`: same, `simp [razborovDecode.go, hv]`.
3. `fuel + 1` with `aux = entry :: restAux`: `simp only [razborovDecode.go]`
   then `split` on `f.find? (fun t => decide (¬Term.killedBy t ρ₀))`.
   - `none`: the loop returns `σ`, so `exact hv`.
   - `some t`: `apply ih`, and the new σ-argument still sends `v` to `none` by
     `processEntries_preserves_none t w σ ρ₀ _ v hv`.

The only place the decoder writes to σ is `Function.update σ l.var none`, which
can never turn a `none` into a `some` — that is what
`processEntries_preserves_none` supplies at each clause block.

**Note.** No caller of this lemma exists anywhere in `TCSlib/`: the round-trip
proof in `Switching/RoundTrip.lean` uses the `processEntries`-level version
instead. It is currently a dead declaration.
