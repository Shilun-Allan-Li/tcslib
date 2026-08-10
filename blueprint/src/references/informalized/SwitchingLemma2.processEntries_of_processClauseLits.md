<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/EncodingProperties.lean :: processEntries_of_processClauseLits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The decoder replays exactly one encoder clause block

**Claim.** Let `t : Term n` with `t.length ≤ w`, let every `p ∈ lits` come from
`t.zipIdx`, and put `pcl := processClauseLits lits path ρ₀_enc σ_enc`. Then

`razborovDecode.processEntries t w σ_dec ρ₀_dec (pcl.2.2.2 ++ [(w, false)] ++ rest)`

equals the triple whose first two components are the left folds of `pcl.2.2.2`
that update `σ_dec` at `l.var` to `none` and `ρ₀_dec` at `l.var` to `some e.2`
(where `l` is the head of `t.drop e.1`, the entry being skipped when that drop is
empty), and whose third component is exactly `rest`.

**Proof.** `induction lits generalizing path ρ₀_enc σ_enc σ_dec ρ₀_dec`.

1. `lits = []`, and `lits = hd :: tl` with `path = []` — the aux block is empty,
   so `processEntries` meets the marker `(w, false)` first; its guard `idx ≥ w`
   holds and it returns `(σ_dec, ρ₀_dec, rest)`, matching `List.foldl_nil`
   (`simp only [processClauseLits, List.nil_append, List.foldl_nil]` then
   `simp [razborovDecode.processEntries]`).
2. `lits = hd :: tl`, `path = p :: ps` — unfold one encoder step
   (`simp only [processClauseLits]`), emitting the entry `(hd.2, p.2)`.
3. `hd ∈ t.zipIdx` (from `hmem`), so `List.mem_zipIdx` plus `omega` gives
   `hd.2 < t.length ≤ w`: the marker guard is *not* triggered for this entry.
4. `zipIdx_drop_spec t hd.1 hd.2 hmem_hd` gives `t.drop hd.2 = hd.1 :: drop_rest`,
   so `processEntries` takes the `l :: _` branch, writing `none` into σ and
   `some p.2` into ρ₀ at `hd.1.var` (`simp only [List.cons_append,
   razborovDecode.processEntries, show ¬(hd.2 ≥ w) …, ↓reduceIte, hdrop]`).
5. That is one `List.foldl_cons` step on the right (`simp only [List.foldl_cons,
   hdrop]`), so `ih ps _ _ _ _` with `hmem` weakened along `.tail` closes it. ∎

**Used in.** `go_roundtrip_gen` (`Switching/RoundTrip.lean`) — this is the lemma
that makes decoding step-for-step inverse to encoding on a single clause block.
