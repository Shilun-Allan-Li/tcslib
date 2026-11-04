<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/CircuitDegree.lean :: stepLayerFamily -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Extending a layer polynomial family by one layer

**Claim.** Let `F` be a feed-forward circuit over `Fin 2` all of whose gates lie in
`ACp_GateOps p` (`hUses`), let `d < F.depth`, and let `A : LayerPolyFamily p F ℓ d`
be a randomized polynomial family for layer `d`. Then `stepLayerFamily` builds a
`LayerPolyFamily p F ℓ (d+1)` with seed space `A.Seed × Tail`, where
`Tail := (u : F.nodes (d+1)) → (Fam u).Seed` holds one `gatePolyFamily` seed per
node of the new layer.

**Proof.** `refine` the four structure fields.

- `card_pos`: `Fintype.card_pos_iff` turns `A.card_pos` and each `(Fam u).card_pos`
  into nonemptiness; `Classical.choice` assembles a pair.
- `poly`: feed `(Fam u).poly` the previous layer's polynomials
  `fun i => A.poly st.1 ((F.gates dF u).inputs i)` with tail seed `st.2 u`.
- `degree`: `(Fam u).degree` bounds the composite by
  `(p-1) * ℓ * ⨆ i, (A.poly …).totalDegree`; `ciSup_le'` with `A.degree` bounds the
  supremum, then `Nat.mul_le_mul_left` and
  `simp [circuitDegreeBound, Nat.pow_succ, …]` yield `circuitDegreeBound p ℓ (d+1)`.
- `bad`: fix `x`, set `y := boolInput x`, and define `PrevBad r` (some layer-`d`
  node is wrong), `GateBad r t` (some new gate's approximator disagrees with the
  gate applied to the bitified inputs) and `StepBad st` (some layer-`(d+1)` node is
  wrong), with `Sstep`, `Sprev`, `Sgate` the corresponding filtered finsets. Then
  1. `hsub : Sstep ⊆ Sprev ∪ Sgate` — if `PrevBad st.1` fails then all layer-`d`
     values are correct (`hcorr`), so `bitify_boolVal` rewrites the gate arguments
     (`hargs`) and `evalNode_succ_eq` matches the gate output against `F.evalNode`
     at layer `d+1` (`htarget`); the failure is therefore a gate failure.
  2. `hcard_union` from `Finset.card_le_card` and `Finset.card_union_le`.
  3. `hprev`: `prod_left_filter_card` factors `Sprev.card` as
     `#{PrevBad} * Fintype.card Tail`, then `A.bad x` gives the inherited-error
     bound `gateCountBefore F d * Fintype.card (A.Seed × Tail)`.
  4. `htail_bad`: for good `r`, `pi_exists_bad_card_mul_le` over the nodes of layer
     `d+1` — its per-gate input being `(Fam u).bad`, applicable since `hcorr` plus
     `boolVal_mem` shows the evaluated inputs are `0/1` — bounds the bad tail seeds
     by `Fintype.card (F.nodes curr) * Fintype.card Tail`.
  5. `hgate`: `prod_filter_fiber_mul_le` lifts (4) to `Sgate.card`, then
     `Finset.card_le_univ` and `Fintype.card_prod`.
  6. A final `calc` adds (3) and (5) via `Nat.add_le_add` and recognizes the total
     as `gateCountBefore F (d+1) * Fintype.card (A.Seed × Tail)`
     (`simp [gateCountBefore, …]`, `ring_nf`).

**Used in.** `buildLayerFamily`, which iterates it from `inputLayerFamily` to depth.
