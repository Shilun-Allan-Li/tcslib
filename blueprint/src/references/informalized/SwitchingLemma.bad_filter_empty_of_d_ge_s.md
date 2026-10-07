<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: bad_filter_empty_of_d_ge_s -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# No bad restriction when the depth threshold reaches the number of free variables

**Claim.** Let `f : DNF n` and `d s : ℕ` with `s ≤ d`. Then the set of
restrictions that are simultaneously `IsRestriction s` (exactly `s` free
variables) and `IsBadRestriction f.eval d` (restricted decision-tree depth
`> d`) is empty.

**Proof.** One inequality chain; `private` helper.

1. `simp +zetaDelta` unfolds `IsRestriction` to `ρ.numFree = s` and
   `IsBadRestriction` to `dtDepth (restrictFn f.eval ρ) > d`, reducing the goal
   to: no `ρ` with `ρ.numFree = s` has `dtDepth (restrictFn f.eval ρ) > d`.
2. `dtDepth_restrictFn_le_numFree` gives
   `dtDepth (restrictFn f.eval ρ) ≤ ρ.numFree` — a restricted function can always
   be decided by querying only its free variables.
3. So `dtDepth (restrictFn f.eval ρ) ≤ s ≤ d`, and `not_lt.mpr` (with `linarith`
   supplying `s ≤ d` from the hypothesis) contradicts `> d`.

**Used in.** `switching_lemma`: it disposes of the degenerate branch `¬(d ≤ s)`,
where the left-hand count is `0` and the bound holds by `norm_num`.
