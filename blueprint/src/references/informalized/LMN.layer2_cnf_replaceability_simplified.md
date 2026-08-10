<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/GateSwitching.lean :: layer2_cnf_replaceability_simplified -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Layer-2 CNF-replaceability in the clean `s₂·2^{-l} + ε` form

**Claim.** Same hypotheses as `layer2_cnf_replaceability_union_bound` (gates
`Fin s₂ → DNF n` of width `≤ w`, `0 < w`, `hnd`, `hnodup`, `0 < n`,
`0 < p ≤ 1/(40w)`, `p ≤ 1`), plus `0 < ε`, `0 < s₂` and the largeness
assumption `hn_large : exp(-n·p/3) ≤ ε / s₂`. Then the probability that some
layer-2 gate fails to be a width-`≤ l` CNF after the restriction is at most
`s₂ · (1/2)^l + ε`.

**Proof.** Two lines.

1. `have := layer2_cnf_replaceability_union_bound gates w l hw hw_pos hnd hnodup hn p hp_pos hp_le hp1`
   gives the bound `s₂ · ((1/2)^l + exp(-n·p/3))`.
2. `exact this.trans (…)`: after `rw [mul_add]` the remaining goal is
   `s₂ · (1/2)^l + s₂ · exp(-n·p/3) ≤ s₂ · (1/2)^l + ε`, closed by `nlinarith`
   from `hn_large` together with `mul_div_cancel₀ ε (s₂ ≠ 0)` — i.e.
   `s₂ · (ε / s₂) = ε`, which is where `hs₂_pos` is needed.

**Remark.** `ε` is a hypothesis-supplied slack, not a limit: `hn_large` is the
only place `n` being "large" enters, and `_hε` is unused beyond documenting that
the slack is positive.
