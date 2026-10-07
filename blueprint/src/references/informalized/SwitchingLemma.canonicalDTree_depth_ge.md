<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/CanonicalDTree.lean :: canonicalDTree_depth_ge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The canonical tree is at least as deep as the optimal one

**Claim.** For every `f : DNF n` and `ρ : Restriction n`,
`(canonicalDTree f ρ).depth ≥ dtDepth (restrictFn f.eval ρ)`. That is, the
Razborov canonical decision tree for `f` under `ρ` is a witness for the
minimum-depth problem, so it cannot beat the minimum `dtDepth`.

**Proof.** Immediate composition of two facts:
`depth_ge_dtDepth _ (canonicalDTree_correct f ρ)`.

- `canonicalDTree_correct f ρ` says the canonical tree computes the restricted
  function pointwise: `∀ x, (canonicalDTree f ρ).eval x = restrictFn f.eval ρ x`.
- `depth_ge_dtDepth` turns any such correctness proof into the depth bound: since
  `dtDepth g` is `Nat.find (fun d => ∃ T, T.depth ≤ d ∧ ∀ x, T.eval x = g x)`,
  the tree itself gives a member of that predicate at `d = T.depth`, and
  `Nat.find_min'` yields `dtDepth g ≤ T.depth`. ∎

**Used in.** `canonicalDTree_deepPath_length_ge` and
`razborovEncode_fst_numFree_eq` in `TCSlib/BooleanAnalysis/Switching.lean`: both
combine it by `omega` with `IsBadRestriction f.eval d ρ` (i.e.
`dtDepth (restrictFn f.eval ρ) > d`) to conclude that the canonical tree's
deepest path is longer than `d` — the step that gives the encoding argument a
length-`d` path to work with.
