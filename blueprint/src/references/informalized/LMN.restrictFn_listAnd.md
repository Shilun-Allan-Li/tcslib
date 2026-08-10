<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/Depth3Switching.lean :: restrictFn_listAnd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Restriction distributes over the pointwise AND of a list

**Claim.** For a list `fs` of Boolean functions on `Fin n → Bool` and a
restriction `ρ : Restriction n`, restricting the conjunction equals the
conjunction of the restrictions: for every `x`,
`restrictFn (listAnd fs) ρ x = listAnd (fs.map (fun f => restrictFn f ρ)) x`.

**Proof.** Fix `x` and induct on `fs` (`intro x; induction fs`), with
`simp_all +decide [List.map]` unfolding `List.map` and both `listAnd` clauses.

1. Empty list: both sides are `true`, closed by `rfl`.
2. Cons case `f :: fs`: the left side is `f (ρ.extend x) && restrictFn (listAnd fs) ρ x`
   and the right side is `restrictFn f ρ x && listAnd (fs.map …) x`; the two
   conjuncts match — the first by definition of `restrictFn`, the second by the
   induction hypothesis — so `convert congr_arg₂ (fun a b => a && b) rfl ‹_›`
   closes it.

**Remark.** Purely structural: `restrictFn f ρ = fun x => f (ρ.extend x)` is
precomposition, which commutes with any pointwise operation. The list form is
what the depth-3 compression argument needs.
