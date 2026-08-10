<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: DecisionTree.negateLeaves_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Negating the leaves negates the computed function

**Claim.** For every decision tree `T : DecisionTree n` and input
`x : Fin n → Bool`, `T.negateLeaves.eval x = !(T.eval x)`, where
`DecisionTree.negateLeaves` replaces each `leaf b` by `leaf (!b)` and recurses
through branches.

**Proof.** Induction on `T` (`induction T with`).

1. **Leaf** `.leaf b`: both sides are `!b` — `simp [negateLeaves,
   DecisionTree.eval]`.
2. **Branch** `.branch v lo hi`: `simp only [negateLeaves, DecisionTree.eval]`
   exposes the same test `if x v then … else …` on both sides, and `split <;>
   simp_all` closes each branch using the induction hypotheses `ih_lo`, `ih_hi`.

**Used in.** `dtDepth_neg` (`dtDepth (fun x => !(f x)) = dtDepth f`), where a
depth-`d` tree for `f` is turned into a depth-`d` tree for `¬f`.
