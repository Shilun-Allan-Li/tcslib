<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: processClauseLits_numFree_σ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# σ loses exactly min(#lits, #path) free variables

**Claim.** Assume `ρ₀` and `σ` are free at the same variables (`hagree`), every
literal of `lits` has its variable free in `ρ₀` (`hfree`), and the literal
variables are pairwise distinct (`hdistinct`). Then
`(processClauseLits lits path ρ₀ σ).2.2.1.numFree + min lits.length path.length
= σ.numFree`.

**Proof.** Induction on `lits`, generalizing `path`, `ρ₀`, `σ`.

- *Nil* and *path = []*: nothing is fixed and the `min` is `0`
  (`simp [processClauseLits]`).
- *Cons* `hd :: tl` against `p :: ps`: the step fixes `hd.1.var` in both
  restrictions.
  1. `hhd := hfree hd` gives `ρ₀ hd.1.var = none`, and `hagree` transfers it to
     `hhdσ : σ hd.1.var = none`.
  2. `hupd`: `numFree_update_free σ hd.1.var (!hd.1.neg) hhdσ` — fixing a
     genuinely free variable drops `σ.numFree` by exactly one.
  3. The three hypotheses are re-established for the updated pair:
     `hagree'` by cases on `v = hd.1.var` with `Function.update_of_ne`;
     `hfree'` because `hdistinct` (via `List.rel_of_pairwise_cons`) keeps every
     remaining literal's variable different from `hd.1.var`, so the update does
     not touch it; `hdistinct'` by `List.Pairwise.of_cons`.
  4. The induction hypothesis plus `omega`.

**Used in.** `razborovEncode_go_numFree_invariant` (`hσ_pcl`) — this is the σ-side
half of the counting invariant that ultimately gives
`razborovEncode_fst_numFree_eq` (γ has exactly `d` more fixed variables than ρ).
The ρ₀-side analogue is `processClauseLits_numFree_ρ_eq`.
