<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/GateSwitching.lean :: switching_bernoulli_union_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Union bound over `s` DNF gates

**Claim.** Let `gates : Fin s → DNF n`, each of width `≤ w` with `0 < w`, each
term variable-distinct (`hnd`) and `Nodup`, `0 < n`, and `0 < p ≤ 1/(40w)` with
`p ≤ 1`. Then
`bernoulliRestrProb p (fun ρ => ∃ i, dtDepth (restrictFn (gates i).eval ρ) > l) ≤ s · ((1/2)^l + exp(-n·p/3))`.

**Proof.** A finite union bound followed by a uniform per-gate bound.

1. Establish a general subadditivity fact `h_sum_bound`: for any
   `S : Finset (Fin s)` and family of decidable predicates `A`,
   `bernoulliRestrProb p (fun ρ => ∃ i ∈ S, A i ρ) ≤ ∑ i ∈ S, bernoulliRestrProb p (A i)`.
   After `simp [bernoulliRestrProb]` and `Finset.sum_comm`, `Finset.sum_le_sum`
   reduces this to one restriction `ρ` at a time; `Finset.sum_ite` plus
   `split_ifs` splits on whether some `i ∈ S` satisfies `A i ρ`. In the positive
   case the right side carries a factor
   `(S.filter (A · ρ)).card ≥ 1` — witnessed by `Classical.choose_spec` of the
   existential via `Finset.card_pos` and `Finset.mem_filter` — so
   `le_mul_of_one_le_left` applies, using
   `pow_nonneg` twice for `0 ≤ bernoulliRestrWeight p ρ`. In the negative case
   the left side is `0` and `mul_nonneg` finishes.
2. Specialise to `S = Finset.univ` and `A i ρ = dtDepth (restrictFn (gates i).eval ρ) > l`
   (`simpa using h_sum_bound Finset.univ …`) to get `h_union_bound`.
3. `le_trans h_union_bound` then `convert Finset.sum_le_card_nsmul` turns the
   goal into a uniform bound `(1/2)^l + exp(-n·p/3)` on each summand, with
   `card Finset.univ = s` handled by `norm_num` / `ext`.
4. That uniform bound is `switching_bernoulli_dtDepth_dnf (gates i) w (hw i) hw_pos (hnd i) (hnodup i) hn p hp_pos hp_le hp1 l`
   applied gatewise. ∎

**Used in.** `layer2_cnf_replaceability_union_bound` here, and in
`LMN/CircuitCompression.lean`, `LMN/CircuitLayerReduction.lean`,
`LMN/Depth3Switching.lean`.
