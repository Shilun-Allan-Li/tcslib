<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitCompression.lean :: dnf_concat_width_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Concatenating DNFs preserves a width bound

**Claim.** If every `φ` in `dnfs : List (DNF n)` has `DNF.width φ ≤ l`, then
`DNF.width (listConcat dnfs) ≤ l`.

Width is the maximum term length, so flattening cannot create a longer term. This
is the width half of the OR-case compression (the evaluation half is
`dnf_concat_eval`).

**Proof.** By duality with the CNF version rather than by a fresh induction. Let
`dual φ` be `φ.map (fun clause => clause.map (fun l => ⟨l.var, !l.neg⟩))` — flip
every literal's polarity — and apply `convert` against
`cnf_concat_width_le (dnfs.map dual) l`.

1. `have h_width_eq`: for any `cnfs : List (CNF n)`,
   `CNF.width (listConcat cnfs) = DNF.width (listConcat (cnfs.map dual))`.
   Polarity-flipping is a `List.map` on each clause, so it preserves clause
   length, i.e. `Term.width`; after `simp [CNF.width, DNF.width]` an induction on
   `cnfs` plus `congr! 2` / `ext` / `simp [Term.width]` matches the two folds.
2. Instantiating `h_width_eq` at `dnfs.map dual` (and `Eq.symm`) identifies the
   two width expressions; the remaining list-level goal is closed by
   `List.ext_get` and `aesop`.
3. Side goal — the hypothesis of `cnf_concat_width_le`: every `dual φ` has width
   `≤ l`. This is `h φ hφ` transported along `cnfToDualDNF_width`, which states
   that dualising a formula leaves its width unchanged.

**Note.** `CNF n` and `DNF n` are the same type (`List (Term n)`) with identical
`width` definitions, so the dualisation detour is bookkeeping, not mathematics; a
direct induction would do.
