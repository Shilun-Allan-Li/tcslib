<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/CanonicalDTree.lean :: termSubTree_extend_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The assignment fold does not change the extension by `x`

**Claim.** Let `ρ_x` be the left fold of `lits` over `ρ` that fixes each
literal's still-free variable to `x l.var`. Then `ρ_x.extend x = ρ.extend x`.
That is, the extra bits recorded by the fold are exactly the bits `x` already
supplies, so the total assignment `Restriction.extend · x` is unchanged.
`private`.

**Proof.** Induction on `lits`, generalizing `ρ`.

1. `nil`: the fold is `ρ`, so `rfl`.
2. `cons l rest`: unfold one `List.foldl` step and `split` on
   `l.var ∈ ρ.freeVars`.
   - Free: `rw [ih]` reduces to the single step, closed by
     `extend_update_self ρ l.var x (x l.var) hfree rfl` — updating a free
     variable to the value `x` already gives it leaves `extend` alone.
   - Not free: the step is the identity, so `exact ih ρ`.

**Used in.** `canonicalDTree_go_correct`, where it turns
`restrictFn f.eval ρ' x` back into `restrictFn f.eval ρ x` after the sub-tree
has fixed a clause's variables.
