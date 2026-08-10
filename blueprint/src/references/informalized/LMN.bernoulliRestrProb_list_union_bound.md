<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitLayerReduction.lean :: bernoulliRestrProb_list_union_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Union bound over a list of circuits

**Claim.** Let `0 ≤ p ≤ 1`, let `cs : List (Circuit n)`, and let
`bad : Circuit n → Restriction n → Prop` be decidable in `ρ` for each circuit.
Then
`bernoulliRestrProb p (fun ρ => ∃ c ∈ cs, bad c ρ) ≤
cs.foldr (fun c acc => bernoulliRestrProb p (bad c) + acc) 0`,
i.e. the probability that some listed circuit is bad is at most the sum, taken
in list order, of the individual bad-probabilities.

**Proof.** `convert` the goal to `bernoulliRestrProb_union_bound_fin p hp hp1
cs.length (fun i ρ => bad cs[i] ρ)`, the `Fin`-indexed union bound, leaving two
goals.

1. **The events agree.** `congr! 2` reduces to
   `(∃ c ∈ cs, bad c ρ) ↔ ∃ i, bad cs[i] ρ`. Forward: destructure the
   membership and turn it into an index with `List.mem_iff_get`. Backward: an
   index gives a member by `List.getElem_mem`. Both directions finish with
   `aesop`.
2. **The bounds agree.** `∑ i : Fin cs.length, bernoulliRestrProb p (bad cs[i])`
   equals the `foldr`, by `induction cs` with
   `simp +decide [*, Fin.sum_univ_succ]` peeling one head term per step. ∎

Only the reindexing `Fin cs.length ↔ list membership` is new here; the
probabilistic content is entirely in
`bernoulliRestrProb_union_bound_fin` (`LMN/IterativeReduction.lean`).

**Used in.** `circuit_reduction_ind_step`, to bound the stage-1 failure event
"some child `c₀` of the root gate has `dtDepth (restrictFn c₀.eval ρ) > l`" by a
`foldr` sum over the children, which is then bounded child-by-child using the
inductive hypothesis.
