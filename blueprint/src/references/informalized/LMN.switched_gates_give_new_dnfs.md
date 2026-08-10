<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CompressionStep.lean :: switched_gates_give_new_dnfs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Switched gates can be re-presented as clean width-`l` DNFs

**Claim.** Let `gates : Fin m → DNF n`, let `ρ₁` be a restriction, and suppose
every restricted gate has small decision-tree depth:
`dtDepth (restrictFn (gates i).eval ρ₁) ≤ l` for all `i`. Then there is a new
family `gates' : Fin m → DNF n` such that for every `i`:
`(gates' i).width ≤ l`; `(gates' i).eval x = restrictFn (gates i).eval ρ₁ x` for
all `x`; within each term of `gates' i`, two literals on the same variable are
equal; and each term is `List.Nodup`.

The last two conditions are the hygiene hypotheses the Bernoulli switching lemma
demands of its input DNFs, so this lemma is what lets the reduction be iterated:
the output gates are again legal inputs for the next round.

**Proof.** Pointwise, then `choose`.

1. `have h_each`: for each `i`, produce one such DNF. `dtDepth_le_implies_small_dnf_cnf`
   applied to `restrictFn (gates i).eval ρ₁` and `l` (using `h_switch i`) yields
   `⟨φ₀, hw₀, heval₀⟩` — a DNF of width `≤ l` computing the restricted gate.
2. Take `cleanDNF φ₀` (drop self-contradictory terms, then de-duplicate the
   variables in each surviving term). Its four properties come off the shelf:
   `cleanDNF_width_le` composed with `hw₀` for the width, `cleanDNF_eval` with
   `heval₀` for the evaluation, and `cleanDNF_var_inj` / `cleanDNF_nodup` for the
   two hygiene conditions.
3. `choose gates' hgates' using h_each` turns the pointwise existentials into a
   single function, and the conclusion is its four projections.

**Note.** Stated as a helper for `layer2_composed_bound` / `one_step_layer_reduction`,
but not currently referenced anywhere in the library.
