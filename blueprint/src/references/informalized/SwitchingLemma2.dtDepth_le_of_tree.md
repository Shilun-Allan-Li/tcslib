<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Restriction.lean :: dtDepth_le_of_tree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Exhibiting a shallow tree bounds the decision-tree depth

**Claim.** (`private`) For `f : (Fin n → Bool) → Bool`, if some decision tree
`T : DecisionTree n` has `T.depth ≤ d` and computes `f` (`∀ x, T.eval x = f x`),
then `dtDepth f ≤ d`. This is the introduction rule for the depth measure: to
bound it from above, produce a witness tree.

**Proof.** Immediate in two steps.

1. `unfold dtDepth` exposes the definition as
   `Nat.find (p := fun d => ∃ T : DecisionTree n, T.depth ≤ d ∧ ∀ x, T.eval x = f x)`.
2. `Nat.find_min' _ ⟨T, hd, heval⟩` — the tuple witnesses that `d` itself
   satisfies the predicate, and `Nat.find` returns the least such value, hence
   `dtDepth f ≤ d`. ∎

**Used in.** `fixedTerm_implies_dtDepth_zero` and
`killedAll_implies_dtDepth_zero` (same file), each instantiated with a constant
leaf (`.leaf true` / `.leaf false`) of depth `0` to conclude
`dtDepth (restrictFn f.eval ρ) = 0` via `Nat.eq_zero_of_le_zero`.
