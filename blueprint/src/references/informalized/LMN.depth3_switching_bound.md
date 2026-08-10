<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/Depth3Switching.lean :: depth3_switching_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Two-stage switching bound for depth-3 circuits

**Claim.** Let `f` be the AND of `gates : Fin s₂ → DNF n` (`h_f : f x = true ↔ ∀ i, (gates i).eval x = true`),
each gate of width `≤ w` with variable-distinct, `Nodup` terms, `0 < w`, `0 < l`,
`0 < n`, and `0 < p₁ ≤ 1/(40w)`, `0 < p₂ ≤ 1/(40l)`, both `≤ 1`. Then
`bernoulliRestrProb (p₁ * p₂) (fun ρ => dtDepth (restrictFn f ρ) > t) ≤ s₂ · ((1/2)^l + exp(-n·p₁/3)) + ((1/2)^t + exp(-n·p₂/3))`.

**Proof.** Split the composed restriction into the two switching stages.

1. `h_two_stage`: apply `two_stage_bound` with stage-1 failure event
   `A ρ₁ = ∃ i, dtDepth (restrictFn (gates i).eval ρ₁) > l` and
   `β = (1/2)^t + exp(-n·p₂/3)`. The numeric side conditions go by
   `norm_num [hp₁_pos, hp₁_le, …]`, `0 ≤ β` by `positivity`, and the conditional
   stage-2 hypothesis is exactly
   `depth3_second_stage_bound f s₂ gates l t ρ₁ h_f hρ₁ hl_pos hn p₂ …`
   (all gates shallow ⇒ `f|_{ρ₁}` is one nice width-`l` CNF ⇒ CNF switching lemma).
2. It remains to bound `bernoulliRestrProb p₁ A` by `s₂ · ((1/2)^l + exp(-n·p₁/3))`:
   `add_le_add ?_ le_rfl` then
   `convert switching_bernoulli_union_bound gates w l hw hw_pos hnd hnodup hn p₁ …`,
   the union bound over the `s₂` gates. ∎

**Note.** The proof opens with `by_contra h_contra` and then discharges the goal
via `refine h_contra <| …`; the contradiction hypothesis is never used, so the
`by_contra` is inert. Depends transitively on the `sorry` in
`dedupClauseVars_eval_of_not_taut` (through `depth3_second_stage_bound`).

**Used in.** `circuit_reduction_depth3`.
