<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/EncodingProperties.lean :: processClauseLits_sigma_none_of_rho_none -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# If ρ₀ stays unset at v, so does σ

**Claim.** Let `v` be free for the incoming branching restriction, `ρ₀ v = none`,
and suppose it is *still* free afterwards,
`(processClauseLits lits path ρ₀ σ).2.1 v = none`. Then the σ-component is
unchanged at `v`: `(processClauseLits lits path ρ₀ σ).2.2.1 v = σ v`.

**Proof.** `induction' lits with hd tl ih generalizing path ρ₀ σ`.

1. `lits = []` — output is the input pair for either shape of `path`
   (`cases path <;> aesop`).
2. `lits = hd :: tl` — `rcases path`; for the empty path both components are
   returned unchanged, and for `path = x :: path` unfold one step
   (`simp +decide [processClauseLits]` in `h` and the goal).
3. `by_cases hvar : hd.1.var = v`. If `hd.1.var = v`, the recursive call receives
   `Function.update ρ₀ v (some x.2)`, which is not `none` at `v`; by
   `processClauseLits_rho_ne_none` the output ρ₀ at `v` is not `none` either,
   contradicting `h` (`absurd`).
4. Otherwise `convert ih path (Function.update ρ₀ hd.1.var (some x.2))
   (Function.update σ hd.1.var (some !hd.1.neg)) _ h using 1`, and the two
   residual `Function.update_apply` side goals — that both updates are inert at
   `v` — close by `aesop`. ∎

**Why it holds.** `processClauseLits` updates ρ₀ and σ at exactly the same
variables in lockstep (one `Function.update` each per consumed path entry), so
"ρ₀ untouched at `v`" forces "σ untouched at `v`".

**Used in.** `encode_go_fst_sigma_indep_at_free` (same file) and
`go_roundtrip_gen` (`Switching/RoundTrip.lean`), to propagate the "free variables
still have `σ v = none`" invariant across one clause.
