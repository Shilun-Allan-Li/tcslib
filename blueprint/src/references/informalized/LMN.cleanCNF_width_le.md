<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitHelpers.lean :: cleanCNF_width_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Cleaning a CNF does not increase its width

**Claim.** For every `c : CNF n`, `(cleanCNF c).width ≤ c.width`, where
`CNF.width` is `(·.map Term.width).foldr max 0` — the longest clause length, `0`
for the empty CNF.

**Proof.** The outer shape is proof by contradiction dressed up oddly: a dummy
`h_max_le : ∀ {s t}, s ≤ t → ∀ {a}, a ≤ s → a ≤ t` (just `le_trans`) is
introduced only so that `contrapose! h_max_le` moves the negated goal
`c.width < (cleanCNF c).width` into a hypothesis; `absurd h_max_le (not_lt_of_ge …)`
then discharges it against the real bound, proved in the `by` block by two
inductions:

1. `h_foldr_le` (first): for every `l : List (Term n)`,
   `(l.map (fun t => (dedupTermVar t).width)).foldr max 0 ≤ (l.map Term.width).foldr max 0`.
   Induction on `l`; the step is `max_le_max (dedupTermVar_width_le t) ih`, using
   that de-duplication never lengthens a clause.
2. Instantiated at `c.filter (fun t => !termHasContradiction t)`, this bounds the
   cleaned width by the filtered-list width; `convert … using 1` plus
   `unfold cleanCNF; unfold CNF.width; aesop` matches the goal shape.
3. `h_foldr_le` (second, shadowing the first): for every `l`,
   `((l.filter (fun t => !termHasContradiction t)).map Term.width).foldr max 0 ≤
   (l.map Term.width).foldr max 0` — deleting clauses can only lower a maximum
   (`induction l <;> simp +decide [*]; grind`).
4. `le_trans` of steps 2 and 3 gives `(cleanCNF c).width ≤ c.width`. ∎

**Used in.** `switching_bernoulli_dtDepth_cnf_general` (its only caller), so that
the width hypothesis `CNF.width f ≤ w` survives normalisation.
