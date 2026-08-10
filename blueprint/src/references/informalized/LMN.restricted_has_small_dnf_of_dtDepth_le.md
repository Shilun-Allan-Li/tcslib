<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/GateSwitching.lean :: restricted_has_small_dnf_of_dtDepth_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Shallow restricted function has a narrow DNF

**Claim.** For `f : (Fin n → Bool) → Bool`, a restriction `ρ` and `l : ℕ`, if
`dtDepth (restrictFn f ρ) ≤ l` then there is a DNF `φ : DNF n` with
`φ.width ≤ l` and `φ.eval x = restrictFn f ρ x` for all `x`.

**Proof.** One line: `(dtDepth_le_implies_small_dnf_cnf _ l h).1` — the DNF
component of the same conjunction whose CNF component gives
`restricted_has_small_cnf_of_dtDepth_le`.

**Note.** This is the unused mirror image of the CNF version; no other
declaration in the library currently references it. It is kept for symmetry with
`restricted_has_small_cnf_of_dtDepth_le`.
