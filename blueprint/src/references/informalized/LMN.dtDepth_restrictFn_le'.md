<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionMonotonicity.lean :: dtDepth_restrictFn_le' -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Decision-tree depth is monotone under restriction

**Claim.** For every `f : (Fin n → Bool) → Bool` and every `ρ : Restriction n`,
`dtDepth (restrictFn f ρ) ≤ dtDepth f`. Here `dtDepth g` is
`Nat.find (fun d => ∃ T : DecisionTree n, T.depth ≤ d ∧ ∀ x, T.eval x = g x)`,
i.e. the least decision-tree depth computing `g`.

**Proof.** Exhibit a tree for `restrictFn f ρ` of depth at most `dtDepth f`.

1. `Nat.find_spec` at `d = dtDepth f` (with the same `buildFullDTree`
   nonemptiness witness used to define `dtDepth`) yields `T` with
   `hTd : T.depth ≤ dtDepth f` and `hTe : ∀ x, T.eval x = f x`.
2. Put `T' := dtRestrict T ρ`. Then `T'.depth ≤ dtDepth f` by
   `dtRestrict_depth_le` chained with `hTd` (`le_trans`).
3. `T'` computes the restriction: `dtRestrict_eval` gives
   `T'.eval x = T.eval (Restriction.extend ρ x)`, and `simp [restrictFn]` plus
   `hTe` identifies that with `restrictFn f ρ x`.
4. `Nat.find_min' _ ⟨T', hT'd, hT'e⟩` concludes, since `dtDepth (restrictFn f ρ)`
   is the least such bound.

**Used in.** `dtDepth_composeRestr_le` here, and repeatedly in
`CircuitLayerReduction.lean` (e.g. the literal-circuit cases of
`depth2_circuit_switching_bound`-style arguments) to transport a depth bound for
`f` to all of its restrictions.
