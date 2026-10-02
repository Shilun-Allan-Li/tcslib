<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: processClauseLits_freeVars_agree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# processClauseLits preserves ρ₀/σ agreement on free variables

**Claim.** If `ρ₀` and `σ` are free at exactly the same variables
(`hagree : ∀ v, ρ₀ v = none ↔ σ v = none`), then the two outputs
`(processClauseLits lits path ρ₀ σ).2.1` (the ρ₀ component) and
`….2.2.1` (the σ component) are again free at exactly the same variables.

**Proof.** Induction on `lits`, generalizing `path`, `ρ₀`, `σ`.

- *Nil* and *path exhausted*: `processClauseLits` returns the inputs unchanged
  (`simp [processClauseLits]`), so the goal is `hagree v`.
- *Cons* `hd :: tl` against `p :: ps`: `simp only [processClauseLits]` exposes the
  recursive call with `ρ₀` updated at `hd.1.var` to `some p.2` and `σ` updated at
  the same variable to `some (!hd.1.neg)`. `apply ih` reduces to re-establishing
  agreement for the updated pair: at `v = hd.1.var` both sides are `some _`
  (`simp [Function.update]`), and away from it `Function.update_of_ne` reduces to
  `hagree v`.

*Remark.* The declaration's docstring talks about σ's `numFree` decreasing by at
most one; the statement actually proved is only this agreement invariant. The
`numFree` accounting lives in `processClauseLits_numFree_σ`.

**Used in.** `razborovEncode_go_numFree_invariant` (`hagree_pcl`), to carry the
agreement hypothesis of `processClauseLits_numFree_σ` across one iteration of
`razborovEncode.go`.
