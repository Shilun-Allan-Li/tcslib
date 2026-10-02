<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/CanonicalDTree.lean :: canonicalDTree_go_fuel_invariant -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Fuel invariance of the canonical decision tree recursion

**Claim.** For a DNF `f` and a restriction `ρ`, the tree produced by the
fuelled recursion `canonicalDTree.go f fuel ρ` does not depend on `fuel`, as
long as the fuel exceeds `ρ.numFree`: for all `fuel₁, fuel₂` with
`ρ.numFree < fuel₁` and `ρ.numFree < fuel₂`, we get
`canonicalDTree.go f fuel₁ ρ = canonicalDTree.go f fuel₂ ρ`. (The statement is
phrased with an explicit `k = ρ.numFree` so it can be proved by strong
induction on `k`.)

**Proof.** Strong induction on `k = ρ.numFree` (`Nat.strongRecOn`).

1. Both fuels are positive, so write `fuel₁ = f₁ + 1`, `fuel₂ = f₂ + 1`
   (`obtain ⟨f₁, rfl⟩ … by omega`), and unfold both sides
   (`simp only [canonicalDTree.go]`).
2. `split_ifs` on the two guards: if all terms of `f` are killed by `ρ`, both
   sides are `.leaf false`; if some term is fixed, both are `.leaf true`
   (`rfl` in each case). The guards are the same on both sides, so no fuel
   appears.
3. In the alive branch, `split` on `f.find? (¬ killedBy · ρ)`. On `none` both
   sides are `.leaf false` (`rfl`). On `some t` we have `¬Term.killedBy t ρ`
   (`List.find?_some`), `t ∈ f` (`List.mem_of_find?_eq_some`), hence
   `¬Term.fixedBy t ρ` from the second guard.
4. Therefore `t` has a literal free in `ρ`: otherwise every `l ∈ t` has
   `ρ l.var = some b`, and `b = l.neg` would make `t` killed, so `b = !l.neg`
   and `t` would be fixed (`by_contra`, `push_neg`, case split on `ρ l.var`,
   `cases b <;> cases l.neg <;> simp_all`).
5. Apply `termSubTree_cont_congr_strict t ρ hex`: it suffices that the two
   continuations agree on every `ρ'` with `ρ'.numFree < ρ.numFree`. If
   `Term.fixedBy t ρ'` holds both continuations give `.leaf true`; otherwise
   they are `go f f₁ ρ'` and `go f f₂ ρ'`, equal by the induction hypothesis
   at `ρ'.numFree < k`, with both fuel bounds discharged by `omega`. ∎

**Used in.** `cont_eq_canonicalDTree`, where the fuel carried down from an outer
restriction must be reconciled with `canonicalDTree`'s own `ρ.numFree + 1`.
