<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/CanonicalDTree.lean :: cont_eq_canonicalDTree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The termSubTree continuation is itself a canonical decision tree

**Claim.** Let `f : DNF n`, `t ∈ f`, and let `ρ_orig`, `ρ'` be restrictions
with `ρ_orig.numFree ≥ ρ'.numFree + 1`. Then the standard `termSubTree`
continuation evaluated at `ρ'`,
`if decide (Term.fixedBy t ρ') then .leaf true else canonicalDTree.go f ρ_orig.numFree ρ'`,
is literally equal to `canonicalDTree f ρ'`.

**Proof.** `split_ifs` on `Term.fixedBy t ρ'`, then `simp_all +decide
[canonicalDTree]` to expose `canonicalDTree f ρ' = canonicalDTree.go f (ρ'.numFree + 1) ρ'`.

- **Fixed case.** The continuation is `.leaf true`; unfold one step of the
  recursion (`rw [canonicalDTree.go]`) and `split_ifs` on its guards.
  - If every term of `f` is killed by `ρ'`, then in particular `t` is: some
    `l ∈ t` has `ρ' l.var = some l.neg` (`Literal.killedBy`), while
    `Term.fixedBy t ρ'` gives `ρ' l.var = some (!l.neg)` — contradiction
    (`absurd`, `aesop`).
  - If some term of `f` is fixed, the recursion also returns `.leaf true`
    (`rfl`).
  - The remaining guard is impossible, since `⟨t, ht_mem, ‹fixedBy t ρ'›⟩`
    witnesses `∃ t ∈ f, Term.fixedBy t ρ'`.
- **Non-fixed case.** The goal reduces to
  `canonicalDTree.go f ρ_orig.numFree ρ' = canonicalDTree.go f (ρ'.numFree + 1) ρ'`,
  which is exactly `canonicalDTree_go_fuel_invariant` applied with `rfl`,
  the hypothesis `hfuel` (giving `ρ'.numFree < ρ_orig.numFree`), and
  `Nat.lt_succ_self`. ∎

**Used in.** `canonicalPath_preserve_processClauseLits` in
`TCSlib/BooleanAnalysis/Switching.lean` — this is the self-similarity step that
lets the canonical-path analysis treat a subtree reached after processing one
clause as a fresh canonical tree.
