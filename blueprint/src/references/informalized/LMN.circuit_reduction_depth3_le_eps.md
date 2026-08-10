<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/Depth3Switching.lean :: circuit_reduction_depth3_le_eps -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Depth-3 reduction in `ε` form

**Claim.** Same setting as `circuit_reduction_depth3` (`f` the AND of `s₂`
width-`w` DNF gates with hygienic terms, `0 < w`, `0 < l`, `0 < n`), plus the two
parameter hypotheses `s₂ · (1/2)^l ≤ ε/2` and `(1/2)^t ≤ ε/2`. Then
`bernoulliRestrProb (composedDelta w (↑l) 3) (fun ρ => dtDepth (restrictFn f ρ) > t) ≤ ε + s₂ · exp(-n·p₁/3) + exp(-n·p₂/3)`
with `p₁ = 1/(40w)`, `p₂ = 1/(40l)`.

**Proof.** Arithmetic repackaging of the previous bound.

1. `h := circuit_reduction_depth3 f s₂ gates w l t h_f hw hw_pos hnd hnodup hn hl_pos`.
2. `simp only at h ⊢` zeta-reduces the `let`-bound `p₁`, `p₂` in both.
3. `linarith`: expanding `s₂ · ((1/2)^l + exp(-n·p₁/3))` and adding
   `(1/2)^t`, the two dominant terms are `≤ ε/2 + ε/2 = ε` by `hl_bound` and
   `ht_bound`, and the tails are carried unchanged. ∎

**Note.** `ε` is unconstrained (no `0 < ε`) — the hypotheses `hl_bound` and
`ht_bound` do all the work, so choosing `l ≈ log₂(2s₂/ε)` and `t ≈ log₂(2/ε)` is
left to the caller rather than derived here. This is the terminal statement of
the file and is not referenced elsewhere; it inherits the transitive `sorry`
dependency of `circuit_reduction_depth3`.
