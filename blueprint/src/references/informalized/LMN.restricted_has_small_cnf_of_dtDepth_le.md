<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/GateSwitching.lean :: restricted_has_small_cnf_of_dtDepth_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Shallow restricted function has a narrow CNF

**Claim.** For `f : (Fin n → Bool) → Bool`, a restriction `ρ` and `l : ℕ`, if
`dtDepth (restrictFn f ρ) ≤ l` then there is a CNF `ψ : CNF n` with
`ψ.width ≤ l` and `ψ.eval x = restrictFn f ρ x` for all `x`.

**Proof.** One line: `(dtDepth_le_implies_small_dnf_cnf _ l h).2`. That lemma
returns the DNF and CNF representations as a conjunction, and this declaration
just projects out the CNF component, specialised to the restricted function
`restrictFn f ρ`.

**Why it exists.** A deliberately granular repackaging: it saves the callers
(`all_gates_have_small_cnf`, `layer2_cnf_replaceability_union_bound`) from
writing the `.2` projection and from re-elaborating the restricted function at
each use site.
