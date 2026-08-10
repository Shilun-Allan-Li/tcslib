<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RecursiveReduction.lean :: compress_and_switch -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Compression plus switching for one gate

**Claim.** Let `cs : List (Circuit n)`, `ρ₁ : Restriction n`, `l t : ℕ` with
`0 < l`, `0 < n`, and suppose every child satisfies
`dtDepth (restrictFn c.eval ρ₁) ≤ l`. Then under a further Bernoulli restriction
`ρ₂` with parameter `1 / (40 * l)`,

`bernoulliRestrProb (1/(40l)) (fun ρ₂ => dtDepth (restrictFn (Circuit.node isAnd cs).eval (composeRestr ρ₁ ρ₂)) > t) ≤ (1/2)^t + Real.exp (-(n / (120 * l)))`.

The bound is uniform in `isAnd`, i.e. holds for both an AND and an OR gate.

**Proof.** `by_cases h : isAnd <;> simp_all +decide [SwitchingLemma2.bernoulliRestrProb]`
splits on the gate type; the two branches are dual.

1. **AND.** `and_children_have_cnf cs ρ₁ l h_all` gives `ψ : CNF n` with
   `CNF.width ψ ≤ l` computing the `ρ₁`-restricted node. `convert
   switching_bernoulli_dtDepth_cnf_general ψ l hψ_width hl hn (1/(40*l)) … t using 1`
   applies the switching lemma to `ψ` at `p = 1/(40l)`; its side conditions
   `0 < p`, `p ≤ 1/(40 * width)`, `p ≤ 1` are discharged by `positivity` and
   `div_le_div_iff₀` / `div_le_iff₀` with `norm_cast <;> linarith`.
2. Matching the events uses `restrictFn_composeRestr` to turn
   `restrictFn _ (composeRestr ρ₁ ρ₂)` into a `ρ₂`-restriction of the
   `ρ₁`-restricted function, and `funext hψ_eval` to replace that function by
   `ψ.eval`.
3. Matching the bounds is arithmetic (`ring_nf; norm_num [add_comm]`): the general
   lemma yields `Real.exp (-(n * p / 3))`, and `n * (1/(40l)) / 3 = n / (120 l)`.
4. **OR.** Same shape with `or_children_have_dnf` and
   `switching_bernoulli_dtDepth_dnf_general`, packaged as the intermediate
   `have h_switch` about `restrictFn φ.eval ρ₂`; `convert h_switch using 3` then
   `simp [restrictFn_composeRestr]` and the rewrite `φ.eval = _` finish.

**Used in.** `circuit_layer_reduction`
(`TCSlib/BooleanAnalysis/LMN/CircuitLayerReduction.lean`) — this is the per-gate
failure bound the recursion sums over.
