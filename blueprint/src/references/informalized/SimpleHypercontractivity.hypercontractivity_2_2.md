<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Simple.lean :: hypercontractivity_2_2 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# (2,2)-hypercontractivity is contractivity

**Claim.** For every `ρ : ℝ` with `ρ ^ 2 ≤ 1` and every `f : BooleanFunc n`,
`expect (fun x => noiseOp ρ f x ^ 2) ≤ (expect (fun x => f x ^ 2)) ^ 1`. This is
the `k = 1` instance of the `(2, 2k)`-hypercontractivity family, stated in the
family's shape (right-hand side raised to the power `k = 1`) rather than as a new
inequality.

**Proof.** Immediate: `rw [pow_one]` removes the exponent, and the goal is then
`contractivity ρ hρ f` verbatim. ∎

**Why it matters.** It is the anchor of the `(2, 2k)` family — the shape
`expect ((T_ρ f) ^ (2k)) ≤ (expect (f ^ 2)) ^ k` at `k = 1` — so the family reads
uniformly even though this member needs no hypercontractive input beyond
`|ρ| ≤ 1`. Compare `hypercontractivity_2_6`, the `k = 3` member, which does go
through `hypercontractivity_2_q`.
