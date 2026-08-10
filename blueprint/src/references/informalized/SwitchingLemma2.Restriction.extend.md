<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Restriction.lean :: Restriction.extend -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Completing a restriction to a total assignment

**Definition.** For `ρ : Restriction n` and `x : Fin n → Bool`,

`extend ρ x : Fin n → Bool := fun i => (ρ i).getD (x i)`.

Coordinate `i` takes `ρ`'s fixed bit when `ρ i = some b`, and falls back to
`x i` when `ρ i = none`. So `ρ.extend x` is the total input obtained by reading
the fixed coordinates off `ρ` and the free coordinates off `x`. A plain
definition; no proof.

**Remark.** Only the values of `x` on `ρ.freeVars` matter, which is why the
restricted function `restrictFn f ρ := fun x => f (ρ.extend x)` is defined on
all of `Fin n → Bool` rather than on the free coordinates alone — it lets
`dtDepth (restrictFn f ρ)` reuse the unrestricted decision-tree machinery
verbatim.

**Used in.** `restrictFn` (and through it `IsBadRestriction`),
`Literal.killedBy_eval_false`, `Literal.fixedBy_eval_true`,
`fixedTerm_implies_dtDepth_zero`, `killedAll_implies_dtDepth_zero` (same file),
and `Switching/CanonicalDTree.lean` plus the `LMN/Restriction*` files.
