<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionFourier.lean :: chiS_extend -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A character through a restriction splits into a free part and a constant sign

**Claim.** For `U : Finset (Fin n)`, a restriction `ρ`, and an input
`x : BoolCube n`, writing `J = ρ.freeVars`,

`chiS U (ρ.extend x) = chiS (U ∩ J) x * signProd ρ (U \ J)`.

The Walsh character `χ_U` evaluated on the extended input factors into the
character of the free part of `U`, which still depends on `x`, and the constant
`±1` sign that `ρ` fixes on the rest of `U`.

**Proof.**

1. `unfold chiS signProd Restriction.extend` turns the goal into an identity
   between `∏ i ∈ U, boolToSign ((ρ i).getD (x i))` and the stated product.
2. `rw [← Finset.prod_inter_mul_prod_diff U ρ.freeVars]` splits the left product
   over `U` into the part on `U ∩ J` and the part on `U \ J`; `congr 1` reduces
   to matching the two factors separately.
3. On `U ∩ J`: `mem_freeVars.mp` gives `ρ i = none`, so
   `(ρ i).getD (x i) = x i` and the factor is `boolToSign (x i)` (`simp [hfree]`).
4. On `U \ J`: `mem_freeVars.mpr` gives `ρ i ≠ none`; `cases hv : ρ i` discards
   the `none` case by `absurd`, and in the `some b` case both defaults are
   ignored so the factors are equal by `rfl`.

**Used in.** `fourierCoeff_restrictBF` — this is the step that turns the Walsh
expansion of `f` at `ρ.extend x` into an expansion in the characters of `x`.
