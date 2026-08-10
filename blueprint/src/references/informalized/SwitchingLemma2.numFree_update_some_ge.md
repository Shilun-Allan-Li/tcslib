<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: numFree_update_some_ge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Fixing any variable drops numFree by at most one

**Claim.** For any `ρ : Restriction n`, `v : Fin n`, `b : Bool`,
`Restriction.numFree (Function.update ρ v (some b)) + 1 ≥ ρ.numFree`. Unlike
`numFree_update_free` this needs no hypothesis on `ρ v`: the update either frees
nothing new or removes exactly one free variable.

**Proof.** `by_cases hv : ρ v = none`.

1. Free case: `numFree_update_free ρ v b hv` gives the exact equality, and `omega`
   weakens it to the inequality.
2. Fixed case (`ρ v = some _`): `Restriction.freeVars (Function.update ρ v (some
   b)) = ρ.freeVars`, shown by `ext i` and a split on `i = v` — at `i = v` both
   sides are false (using `hv`), elsewhere `Function.update_of_ne hiv` applies.
   Then `numFree` is unchanged and `omega` concludes.

**Used in.** Line 944, on `ρ₀` updates whose freeness is not known — the "at most
one" direction needed when the encoder's path may or may not consume a free
variable at a given step.
