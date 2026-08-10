<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/IterativeReduction.lean :: two_stage_composed_union_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Two-stage composed union bound (statement only — proof is `sorry`)

**Claim.** Let `0 ≤ p ≤ 1` and `0 ≤ q ≤ 1`, and let `A B : Restriction n → Prop`
be decidable events. Then
`∑ ρ₁, bernoulliRestrWeight p ρ₁ * bernoulliRestrProb q (fun ρ₂ => A ρ₁ ∨ B ρ₂)
≤ bernoulliRestrProb p A + bernoulliRestrProb q B`.
Read through `restriction_compose_eq`, the left side is the probability under a
two-stage restriction (Bernoulli(`p`) then Bernoulli(`q`)) that the first-stage
event `A` or the second-stage event `B` occurs; the bound is the sum of the two
single-stage probabilities.

**Proof.** **Not proved.** The body is `sorry`, with the source comment
"goal ordering from `rotate_left` changed in v4.25.0-rc2; needs interactive
rewrite" — so an earlier tactic script broke under the toolchain bump and was
replaced by the placeholder. The intended argument, recorded in the file's
module docstring, is:

1. Pointwise in `ρ₁`, `bernoulliRestrProb q (fun ρ₂ => A ρ₁ ∨ B ρ₂) ≤
   (if A ρ₁ then 1 else 0) + bernoulliRestrProb q B` — the indicator absorbs the
   `A ρ₁` disjunct, which is constant in `ρ₂`.
2. Multiply by `bernoulliRestrWeight p ρ₁` and sum over `ρ₁`; the indicator terms
   give `bernoulliRestrProb p A` and the `bernoulliRestrProb q B` terms give
   `bernoulliRestrProb q B` because the weights sum to one
   (`bernoulliRestrWeight_sum_one`).

**Reviewer note.** The blueprint entry for this theorem
(`blueprint/src/chapter/BooleanAnalysis/LMN/IterativeReduction.tex`) carries
`\leanok` even though the Lean proof is a `sorry`; that mark is currently
unjustified. The theorem is also not yet used anywhere in the library — the
depth-reduction development goes through `LMN.two_stage_bound'` instead.
