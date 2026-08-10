<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/EncodingProperties.lean :: processEntries_preserves_none -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The decoder's clause pass preserves unset variables

**Claim.** For a term `t`, width `w`, restrictions `σ ρ₀`, aux list `aux` and a
variable `v` with `σ v = none`, the σ-component of
`razborovDecode.processEntries t w σ ρ₀ aux` is still `none` at `v`.

**Proof.** `induction aux generalizing σ ρ₀`.

1. `aux = []` — `processEntries` returns `σ` unchanged, so the goal is `hv`
   (`simp [razborovDecode.processEntries, hv]`).
2. `aux = entry :: rest` — unfold (`simp only [razborovDecode.processEntries]`)
   and `split` on the guard `idx ≥ w`: the termination-marker branch returns `σ`,
   closed by `exact hv`.
3. `split` again on `t.drop idx`: the `[]` branch also returns `σ`
   (`exact hv`).
4. In the `l :: _` branch the recursion runs on
   `Function.update σ l.var none`; `apply ih` and discharge its hypothesis by
   `simp only [Function.update_apply]` then `split` — if `v = l.var` the value is
   literally `none` (`rfl`), otherwise `hv`. ∎

**Why it is trivial.** The decoder's only σ-writes set variables to `none`
(it *unfixes* the variables the encoder fixed), so `none` can never be
overwritten by a `some`.

**Used in.** `decode_go_preserves_none` (same file), which lifts the invariant
through the fuelled decode loop `razborovDecode.go`.
