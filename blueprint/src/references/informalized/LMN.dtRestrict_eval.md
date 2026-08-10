<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionMonotonicity.lean :: dtRestrict_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A restricted decision tree computes the restricted function

**Claim.** For every `T : DecisionTree n`, every `ρ : Restriction n` and every
input `x : Fin n → Bool`,
`(dtRestrict T ρ).eval x = T.eval (Restriction.extend ρ x)`,
where `Restriction.extend ρ x i = (ρ i).getD (x i)` fills the free coordinates
of `ρ` from `x`. Equivalently, `dtRestrict T ρ` computes `restrictFn (T.eval) ρ`.

**Proof.** Structural induction on `T`.

1. Leaf: both sides are the leaf value (`simp [dtRestrict, DecisionTree.eval]`).
2. Branch `.branch var lo hi`: unfold one step of `dtRestrict`
   (`simp only [dtRestrict]`) and `split` on the three match arms, naming the
   hypothesis about `ρ var` with `rename_i hv`.
   - `ρ var = some false`: rewrite by the `lo` induction hypothesis; on the right
     `extend ρ x var = false` by `hv`, so `DecisionTree.eval` also takes the
     `lo` branch (`simp [DecisionTree.eval, Restriction.extend, hv]`).
   - `ρ var = some true`: same with the `hi` induction hypothesis.
   - `ρ var = none`: the branch is preserved, so `extend ρ x var = x var` and
     both sides pick the same subtree; closed by `simp` with both induction
     hypotheses.

**Used in.** `dtDepth_restrictFn_le'`, supplying the "computes the right
function" half of the decision-tree witness (`dtRestrict_depth_le` supplies the
depth half).
