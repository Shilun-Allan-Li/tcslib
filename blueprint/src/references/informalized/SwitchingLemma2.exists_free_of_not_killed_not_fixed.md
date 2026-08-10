<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/CanonicalDTree.lean :: exists_free_of_not_killed_not_fixed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# An alive DNF has a free variable

**Claim.** Let `f : DNF n` and `ρ : Restriction n`. If not every term of `f` is
killed by `ρ` (`¬∀ t ∈ f, Term.killedBy t ρ`) and no term of `f` is fixed by `ρ`
(`¬∃ t ∈ f, Term.fixedBy t ρ`), then `ρ` leaves some variable free:
`∃ v : Fin n, v ∈ ρ.freeVars`. This is a `private` helper.

**Proof.** By contradiction: assume `ρ` fixes every variable, i.e. `∀ v,
v ∉ ρ.freeVars` (`by_contra`, `push_neg`).

1. Reduce to showing every `t ∈ f` is killed (`apply h1; intro t ht`), and
   assume some `t` is not (`by_contra ht_nk`).
2. Derive the forbidden `∃ t ∈ f, Term.fixedBy t ρ` from `⟨t, ht, …⟩`: it
   remains to show each `l ∈ t` satisfies `Literal.fixedBy l ρ`.
3. Since `l.var ∉ ρ.freeVars`, unfolding `Restriction.freeVars` gives
   `ρ l.var ≠ none` (`Finset.mem_filter`, `Option.isNone_iff_eq_none`), so
   `ρ l.var = some b` for some `b` (`cases hv : ρ l.var`).
4. If `b = l.neg` then `l` — hence `t` — is killed by `ρ`
   (`Literal.killedBy`), contradicting `ht_nk`.
5. Otherwise `b ≠ l.neg`, so `b = !l.neg` by a two-way Boolean case split
   (`cases b <;> cases l.neg`), which is exactly `Literal.fixedBy l ρ`. ∎

**Used in.** Nothing — the declaration is currently dead. The same argument is
re-derived inline inside `canonicalDTree_go_correct` and
`canonicalDTree_go_fuel_invariant`, and `selectBranchVar_spec` proves the
sharper form that actually produces the branching variable.
