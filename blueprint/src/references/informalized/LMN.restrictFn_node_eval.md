<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RecursiveReduction.lean :: restrictFn_node_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Restriction commutes with an AND/OR gate

**Claim.** For `cs : List (Circuit n)` and `ρ : Restriction n`,
`restrictFn (Circuit.eval (Circuit.node isAnd cs)) ρ` is the function sending `x`
to `cs.foldr (fun c acc => restrictFn c.eval ρ x && acc) true` when `isAnd` is
`true`, and to the corresponding `||`-fold with base `false` when `isAnd` is
`false`. That is, restricting a gate is the gate applied to the restricted
children.

**Proof.** `unfold restrictFn; cases isAnd <;> simp +decide [Circuit.eval]`. After
unfolding, the left side is `x ↦ (Circuit.node isAnd cs).eval (ρ.extend x)`; the
two defining equations of `Circuit.eval` on `node true` / `node false` are exactly
the two folds, with each child evaluated at the same point `ρ.extend x`.

**Remark.** Purely definitional bookkeeping — `restrictFn` only relocates the
argument, so it passes through the fold without touching the list structure.

**Used in.** `and_children_have_cnf` and `or_children_have_dnf` (same file), to
match the fold produced by the compression lemmas (`List.all` / `List.any` over
`cs.map (fun c => restrictFn c.eval ρ)`) against the restricted node.
