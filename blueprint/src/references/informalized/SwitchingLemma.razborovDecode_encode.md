<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/RoundTrip.lean :: razborovDecode_encode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Decoding the Razborov encoding recovers the restriction

**Claim.** For a DNF `f` of width ≤ `w` whose clauses have variable-distinct
literals (`hnd`), and any restriction `ρ`,
`razborovDecode f w (razborovEncode f w d ρ).1 (razborovEncode f w d ρ).2 = ρ`,
i.e. the decoder applied to the encoding `(γ, aux)` returns `ρ`.

**Proof.** `unfold razborovDecode razborovEncode` exposes both as their `go` loops —
the encoder with fuel `path.length + 1` on `path = (canonicalDTree f ρ).deepPath.take d`,
the decoder with fuel `aux.length + 1` — and this is literally `go_roundtrip f w hw hnd _ _ ρ`.

**Note.** The badness hypothesis is `_hbad : IsBadRestriction f.eval d ρ` and is
deliberately unused: the round-trip holds for *every* restriction, since the
decoder replays the encoder's clause choices whatever the path is. Badness is only
needed downstream, to know the path has `d` steps.
