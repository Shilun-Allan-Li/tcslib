<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: numFree_update_free -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Fixing a free variable drops numFree by exactly one

**Claim.** Let `ρ : Restriction n`, `v : Fin n`, `b : Bool`, and suppose `v` is free
in `ρ` (`hv : ρ v = none`). Then
`Restriction.numFree (Function.update ρ v (some b)) + 1 = ρ.numFree`.

**Proof.** Compute the free-variable set of the update.

1. `v ∈ ρ.freeVars`, by `simp [Restriction.freeVars, hv]`.
2. `Restriction.freeVars (Function.update ρ v (some b)) = ρ.freeVars.erase v`: by
   `ext i` and a case split on `i = v` — the `v` case uses `hv` and unfolds
   `Function.update`, the other case is `simp [hi]`.
3. Hence `numFree` of the update is `(ρ.freeVars.erase v).card`, and
   `Finset.card_erase_of_mem hv_mem` turns this into `ρ.freeVars.card - 1`.
4. `Finset.card_pos.mpr ⟨v, hv_mem⟩` gives `0 < ρ.freeVars.card`, so `omega`
   converts the truncated subtraction into the stated `+ 1` equality.

**Used in.** `numFree_update_some_ge`, the `processClauseLits` accounting at line
857, and line 1098 — the exact-decrement fact that keeps the encoder's path length
in step with the number of remaining free variables.
