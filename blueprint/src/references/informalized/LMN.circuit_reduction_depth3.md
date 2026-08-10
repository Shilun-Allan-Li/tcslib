<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/Depth3Switching.lean :: circuit_reduction_depth3 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Depth-3 reduction at the library's composed restriction rate

**Claim.** Same setting as `depth3_switching_bound` (`f` is the AND of `s₂`
width-`w` DNF gates with hygienic terms, `0 < w`, `0 < l`, `0 < n`), but with the
restriction rate supplied by the library parameter `composedDelta w l 3`:
`bernoulliRestrProb (composedDelta w (↑l) 3) (fun ρ => dtDepth (restrictFn f ρ) > t) ≤ s₂ · ((1/2)^l + exp(-n·p₁/3)) + ((1/2)^t + exp(-n·p₂/3))`
where `p₁ = 1/(40w)` and `p₂ = 1/(40l)` are `let`-bound in the statement.

**Proof.** Only the parameter bookkeeping is new.

1. `h_delta`: `unfold composedDelta; simp [pow_one]` gives
   `composedDelta w l 3 = (1/(40w)) · (1/(40l))`, since the exponent is `3 - 2 = 1`;
   `rw [h_delta]` puts the goal in product form.
2. `Nat.one_le_cast.mpr` on `hw_pos` and `hl_pos` gives `(1 : ℝ) ≤ w` and `1 ≤ l`.
3. Apply `depth3_switching_bound` with `p₁ := 1/(40w)`, `p₂ := 1/(40l)`:
   positivity for `0 < pᵢ`, `le_rfl` for `pᵢ ≤ 1/(40·)` (they are equal), and
   `div_le_iff₀` plus `nlinarith` with the casts from step 2 for `pᵢ ≤ 1`. ∎

**Note.** This is the statement in the shape the iterated (depth-`d`) reduction
consumes, specialised to `d = 3`; the Chernoff tails `exp(-n·pᵢ/3)` vanish as
`n → ∞`, leaving `s₂ · (1/2)^l + (1/2)^t`. It carries the same transitive `sorry`
dependency as `depth3_switching_bound`.

**Used in.** `circuit_reduction_depth3_le_eps`.
