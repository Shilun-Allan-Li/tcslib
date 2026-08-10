<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionCompose.lean :: composeRestr_id_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The all-free restriction is a right identity for composition

**Claim.** For every `ρ : Restriction n`, `composeRestr ρ (fun _ => none) = ρ`.

**Proof.** One line: `funext i; simp [composeRestr, Option.orElse]; cases ρ i <;> simp`.

1. `funext i` reduces to the coordinate statement
   `(ρ i).orElse (fun _ => none) = ρ i`.
2. `simp [composeRestr, Option.orElse]` unfolds both the composition and the
   `Option.orElse` match.
3. `cases ρ i <;> simp` checks the two branches: `none.orElse _ = none` and
   `(some b).orElse _ = some b`.

**Remark.** Only the right identity is stated; there is no `composeRestr_id_left`
in the file, and indeed the left version fails for the same reason `composeRestr`
is asymmetric — `composeRestr (fun _ => none) ρ = ρ` does hold, but is not
needed anywhere.

**Used in.** Nothing else in the library; it is a sanity-check lemma for the
`composeRestr` interface.
