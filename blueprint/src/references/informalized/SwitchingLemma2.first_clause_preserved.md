<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Restriction.lean :: first_clause_preserved -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The first surviving clause does not move under a fixed-coordinate refinement

**Claim.** Let `f : DNF n`, `ρ σ : Restriction n` and `t : Term n`. Assume `t` is
the first term of `f` not killed by `ρ`
(`f.find? (fun t => decide (¬Term.killedBy t ρ)) = some t`), that `σ` agrees
with `ρ` on all fixed coordinates (`∀ v, ρ v ≠ none → σ v = ρ v`), and that `t`
is still not killed by `σ`. Then `t` is also the first term of `f` not killed by
`σ`.

**Proof.** Work with the append characterisation of `find?`.

1. `rw [List.find?_eq_some_iff_append] at hfirst ⊢` restates both sides as: the
   predicate holds at `t`, and `f = prefix_ ++ t :: suffix_` with the predicate
   failing on every member of `prefix_`.
2. `obtain ⟨hpt, prefix_, suffix_, hf_eq, hprefix⟩ := hfirst` supplies that
   decomposition for `ρ`; `refine ⟨by simp [ht_alive], prefix_, suffix_, hf_eq, …⟩`
   reuses the *same* split for `σ`, the head condition coming from `ht_alive`.
3. For `t' ∈ prefix_`: `hprefix t' ht'_mem` (after `simp`) gives
   `Term.killedBy t' ρ`, then `killedBy_of_nonfree_agree t' ρ σ … hagree`
   transfers it to `σ`, and `simp [ht'_killed_σ]` shows the `σ`-predicate fails
   at `t'`.

**Remark.** The point is that only the prefix needs re-checking: the witness
list splitting `f` is fixed once and for all in step 2, so no re-scan of `f` is
required.

**Used in.** `Switching/RoundTrip.lean:40`, where the Razborov-style decoding
must recover the same "first alive clause" from the re-derived restriction.
