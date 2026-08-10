<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/CanonicalDTree.lean :: numFree_update_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Fixing a variable never increases the number of free variables

**Claim.** For any `ρ : Restriction n`, `v : Fin n` and `b : Bool`,
`Restriction.numFree (Function.update ρ v (some b)) ≤ ρ.numFree`. No hypothesis
on `v` is required — this is the non-strict companion of `numFree_update_lt`.
It is a `private` helper.

**Proof.** `numFree` is the cardinality of `freeVars`
(`simp only [Restriction.numFree]`), so it suffices to show
`(Function.update ρ v (some b)).freeVars ⊆ ρ.freeVars`
(`Finset.card_le_card`).

1. Take `i` free after the update; unfolding `Restriction.freeVars` this says
   `Function.update ρ v (some b) i = none`
   (`Finset.mem_filter`, `Option.isNone_iff_eq_none`).
2. Rewrite with `Function.update_apply` and `split at hi` on `i = v`: in the
   `i = v` branch the value is `some b`, so the hypothesis is absurd
   (`simp at hi`); otherwise the value is `ρ i`, giving `ρ i = none`
   directly. ∎

**Used in.** `termSubTree_cont_congr` (and hence, via the recursive calls,
`termSubTree_cont_congr_strict`): descending into a `termSubTree` branch may fix
a variable, and the continuation-agreement hypothesis has to be transported
along the resulting non-increase in `numFree`.
