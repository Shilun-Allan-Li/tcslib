<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Restriction.lean :: killedBy_of_nonfree_agree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Killing survives any restriction agreeing on the fixed coordinates

**Claim.** Let `t : Term n` and `ρ σ : Restriction n`. If `t` is killed by `ρ`
(`Term.killedBy t ρ`, i.e. some literal `l ∈ t` has `ρ l.var = some l.neg`) and
`σ` agrees with `ρ` wherever `ρ` is fixed (`∀ v, ρ v ≠ none → σ v = ρ v`), then
`t` is killed by `σ`.

**Proof.** One term-mode step after destructuring.

1. `obtain ⟨l, hl_mem, hl_killed⟩ := hk` produces the killing literal `l` with
   `ρ l.var = some l.neg`.
2. The same `l` witnesses `Term.killedBy t σ`: `hl_killed` says `ρ l.var` is
   `some l.neg`, hence `ρ l.var ≠ none`, so `hagree l.var` gives
   `σ l.var = ρ l.var` and `rwa [Literal.killedBy, hagree …]` closes the goal.
   The side condition `ρ l.var ≠ none` is discharged inline by
   `simp [Literal.killedBy] at hl_killed; rw [hl_killed]; simp`.

**Remark.** The content is just that a killing literal necessarily sits on a
*fixed* coordinate of `ρ`, so the agreement hypothesis — which says nothing
about `ρ`'s free coordinates — already covers it.

**Used in.** `first_clause_preserved` (same file, line 179), which is in turn
used by `Switching/RoundTrip.lean:40`. It has no other call site.
