<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Restriction.lean :: zipIdx_find_to_find -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Searching an index-tagged list finds the same element as searching the list

**Claim.** For `l : List α`, `p : α → Bool`, `x : α`, `idx : ℕ` and an offset
`start : ℕ` (defaulting to `0`): if
`(l.zipIdx start).find? (fun ⟨a, _⟩ => p a) = some ⟨x, idx⟩`, then
`l.find? p = some x`. Tagging positions and then searching on the value
component returns the same value the bare search would.

**Proof.** Induction on `l`, generalizing `idx` and `start`.

1. `nil`: `simp [List.zipIdx] at h` — searching the empty list cannot succeed.
2. `cons hd tl`: `simp only [List.zipIdx_cons, List.find?_cons] at h ⊢`, then
   `by_cases hp : p hd`.
   - `p hd` true: both searches stop at the head, and `simp [hp] at h ⊢;
     exact h.1` reads off `x = hd` from the pair equality.
   - `p hd` false: both searches recurse, and `simp [hp] at h ⊢; exact ih _ _ h`
     applies the induction hypothesis at the shifted `start`.

**Remark.** The `start` binder carries a default value `:= 0`, unusual for a
lemma; every use would have to pass it explicitly anyway since `h` mentions it.

**Used in.** Nothing — this lemma has no call site in the repository, so it is
currently dead code (the index-tagged search steps in
`Switching/EncodingProperties.lean` go through `zipIdx_drop_spec` instead).
