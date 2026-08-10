<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/RoundTrip.lean :: processClauseLits_aux_ne_of_pcl_none -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Aux entries never target a variable that stayed free

**Claim.** Let every pair of `lits` come from `t.zipIdx` (`hmem`), and suppose
`v` is still free after processing, `(processClauseLits lits path ρ₀ σ).2.1 v = none`.
Then no recorded aux entry `e` of that run points at `v`: whenever
`t.drop e.1 = l :: rest`, we have `l.var ≠ v`.

**Proof.** Induction on `lits`, generalizing `path`, `ρ₀`, `σ` (`induction' … generalizing`).

- *Nil*: the aux list is empty (`simp [processClauseLits]`), so there is nothing
  to check. Same for an exhausted path (the `path = []` arm).
- *Cons* `(l₀, i₀) :: tl` against `step :: path`: the aux list is
  `(i₀, step.2) :: (recursive aux)`, so `simp_all [processClauseLits]` splits the
  goal into head and tail.
  - *Head entry*: `zipIdx_drop_spec` turns the membership `(l₀, i₀) ∈ t.zipIdx`
    into `t.drop i₀ = l₀ :: rest`, so the dropped literal is `l₀` itself
    (`grind`). If `l₀.var = v` then this step fixed `v`, and
    `processClauseLits_rho_ne_none` on the updated restrictions gives
    `(…).2.1 v ≠ none` — contradicting `hnone`.
  - *Tail entries*: the induction hypothesis, discharged by `grind`.

**Used in.** `go_roundtrip_gen` (goals `hA'`, `hB'`, and the base case), where it
feeds `foldl_sigma_stable` / `foldl_rho_stable` to show the decoder's fold leaves
still-free variables untouched.
