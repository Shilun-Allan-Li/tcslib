<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Encoding.lean :: razborovDecode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The Razborov decoder

**Definition.** `razborovDecode f w γ aux` recovers the original restriction from
the encoded pair `(γ, aux)` produced by `razborovEncode f w d ρ`. It is
`(razborovDecode.go f w (aux.length + 1) γ γ aux).1`: the fuel is `aux.length + 1`,
and both the restriction being un-fixed (`σ`, initially `γ`) and the
path-simulating restriction (`ρ₀`, also initially `γ`) start from `γ`; only the
`σ` component is returned.

Two mutually-used `where` auxiliaries:

- `processEntries t w σ ρ₀ entries` consumes the `aux` block of one clause `t`.
  On `(idx, dir) :: rest`: if `idx ≥ w` the entry is the termination marker, so
  it returns `(σ, ρ₀, rest)` and stops; otherwise it looks at `t.drop idx` — on
  `[]` (out-of-range position) it likewise stops, and on `l :: _` it sets
  `σ l.var := none` (releasing the variable the encoder had fixed) and
  `ρ₀ l.var := some dir` (replaying the path direction), then recurses on `rest`.
  On `[]` it returns `(σ, ρ₀, [])`.
- `go f w fuel σ ρ₀ aux` is the main loop. With `aux = []`, or fuel `0`, it
  returns `(σ, ρ₀)`. Otherwise it selects the first clause of `f` not killed by
  `ρ₀` via `f.find? (fun t => decide (¬Term.killedBy t ρ₀))`; on `none` it
  returns `(σ, ρ₀)`, on `some t` it runs `processEntries t w σ ρ₀ aux` and
  recurses with the updated `σ'`, `ρ₀'` and leftover `aux'`.

The clause-selection step is the same `find?` on the same `ρ₀` used by
`razborovEncode.go`, which is what makes the decoder track the encoder's clause
sequence without storing clause identities in `aux`.

**Used in.** `razborovDecode_encode` (the round-trip identity) and hence
`razborovEncode_injective`.
