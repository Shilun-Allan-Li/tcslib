<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/CanonicalDTree.lean :: extend_update_self -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Fixing a free variable to its own input value does not change the extension

**Claim.** Let `ρ : Restriction n`, `v : Fin n` free in `ρ`
(`hv : v ∈ ρ.freeVars`), `x : Fin n → Bool`, and `b : Bool` with `x v = b`.
Then `Restriction.extend (Function.update ρ v (some b)) x = ρ.extend x`. This
is a `private` helper.

**Proof.** `funext i` and unfold `Restriction.extend` (which is
`fun i => (ρ i).getD (x i)`); then `by_cases h : i = v`.

1. **`i = v`.** Freeness of `v` means `ρ v = none`
   (`Restriction.freeVars`, `Finset.mem_filter`,
   `Option.isNone_iff_eq_none`), so the right side is `x v`. The left side is
   `(some b).getD (x v) = b`, and `b = x v` by `hxv`
   (`simp [Function.update, hfree, hxv]`).
2. **`i ≠ v`.** `Function.update` leaves `ρ i` untouched, so both sides are the
   same term (`simp [Function.update, h]`). ∎

**Used in.** `termSubTree_extend_eq` (each `termSubTree` update assigns the
variable exactly `x l.var`, so the accumulated restriction extends `x` the same
way as `ρ`) and the branch step of `dtDepth_restrictFn_le_numFree`.
