<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: processClauseLits_numFree_ρ_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# ρ₀ loses exactly min(#lits, #path) free variables

**Claim.** If every literal of `lits` has its variable free in `ρ₀`
(`hfree`) and the literal variables are pairwise distinct (`hdistinct`), then
`(processClauseLits lits path ρ₀ σ).2.1.numFree + min lits.length path.length
= ρ₀.numFree`.

**Proof.** Induction on `lits`, generalizing `path`, `ρ₀`, `σ`.

- Base case: `cases path <;> aesop` — `ρ₀` is returned unchanged.
- Cons case: `rcases path` and `simp_all +decide`; the empty-path arm is `rfl`.
  For `p :: ps`, `convert congr_arg (· + 1) (hl ps …)` matches the goal against
  the induction hypothesis at the updated restrictions, leaving two side goals:
  - `rw [numFree_update_free]; aesop` — fixing the head literal's (free)
    variable drops `numFree` by exactly one, accounting for the `+ 1`.
  - the remaining literals' variables are still free after the update, since
    `hdistinct` makes them different from `hd.1.var`
    (`Function.update_of_ne (Ne.symm …)`, then `hfree`).

**Used in.** `canonicalPath_preserve_processClauseLits` (`hfuel_ok`), where a
strict decrease `ρ₀.numFree ≥ ρ'.numFree + 1` is needed to justify the fuel
budget of the canonical-tree recursion. Companion σ-side lemma:
`processClauseLits_numFree_σ`.
