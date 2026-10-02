<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: dtDepth_witness -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# dtDepth is attained by an actual decision tree

**Claim.** For any `f : (Fin n → Bool) → Bool` there exists a decision tree
`T : DecisionTree n` with `T.depth ≤ dtDepth f` and `∀ x, T.eval x = f x`. The
minimum in the definition of `dtDepth` is realised, not merely approached.

**Proof.** Unwrap the `Nat.find` in `dtDepth`.

1. Let `p d := ∃ T, T.depth ≤ d ∧ ∀ x, T.eval x = f x`.
2. `p` is satisfiable: `⟨n, buildFullDTree f 0 (fun _ => false), …⟩`, using
   `buildFullDTree_depth` for the depth bound and `buildFullDTree_eval` for
   correctness. This is the same witness `dtDepth` itself uses to justify
   `Nat.find`.
3. `Nat.find_spec hexists` says `p` holds at `Nat.find`. Since `dtDepth f` is
   definitionally that `Nat.find`, `unfold dtDepth` followed by
   `convert hspec using 1` transports the statement. ∎

**Used in.** `dtDepth_le_implies_small_dnf_cnf`, which `obtain`s this witness and
pushes it through `toDNF` / `toCNF` to get width-`d` DNF and CNF representations of
any `f` of decision-tree depth at most `d`.
