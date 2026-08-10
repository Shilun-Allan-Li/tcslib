<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitHelpers.lean :: dedupTermVar_var_inj -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A de-duplicated term has at most one literal per variable

**Claim.** For every `t : Term n`, any two literals `l₁, l₂ ∈ dedupTermVar t`
with `l₁.var = l₂.var` are equal. (Equality of literals, not just of variables:
`Literal` also carries the polarity `neg`.)

**Proof.** Induction on `t` with the statement generalised over the
accumulator, carrying both invariants the `foldr` needs.

1. State `h_ind`: for all `t` and all `acc` with `acc.Nodup` and `acc`
   already variable-injective, the `foldr` result is variable-injective.
2. `induction' t with l t ih generalizing acc`.
   - `nil`: the result is `acc`, so the conclusion is the hypothesis
     `hvar_inj`.
   - `cons`: `grind` — if the guard `acc.any (·.var = l.var)` holds the list is
     unchanged, and otherwise `l` is prepended with a variable occurring
     nowhere in the accumulated tail, so injectivity survives.
3. Apply `h_ind` at `acc = []`, both side conditions by `simp +decide`.

**Used in.** `cleanDNF_var_inj` and `cleanCNF_var_inj`, i.e. the `var_inj`
hypothesis of the switching lemma.
