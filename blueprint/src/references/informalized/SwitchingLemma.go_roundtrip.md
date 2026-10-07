<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/RoundTrip.lean :: go_roundtrip -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Round-trip for the raw encoder/decoder loops

**Claim.** Let `f` have width ≤ `w` and variable-distinct literals within each
clause (`hnd`), and let `enc := razborovEncode.go f w enc_fuel path ρ ρ []` be the
encoder run started with both restrictions equal to `ρ`. Then
`(razborovDecode.go f w (enc.2.length + 1) enc.1 enc.1 enc.2).1 = ρ`.

**Proof.** One `exact`: the diagonal instance `σ_dec = ρ₀_dec = enc.1`, `σ = ρ₀ = ρ`,
`dec_fuel = enc.2.length + 1` of `go_roundtrip_gen`. Its six hypotheses become
trivial here:

- `hE` is `fun v hv => hv` (`σ` *is* `ρ`);
- `hA`, `hB` are `rfl` (the decoder starts at `enc.1`);
- `hC`, `hD` are `encode_go_fst_nonfree` — the encoder never changes a variable
  already fixed by `ρ`;
- the fuel bound is `le_refl`.

**Used in.** `razborovDecode_encode`, which is just this statement after unfolding
`razborovEncode` / `razborovDecode`.
