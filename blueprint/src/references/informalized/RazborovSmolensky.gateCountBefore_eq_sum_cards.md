<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/CircuitSize.lean :: gateCountBefore_eq_sum_cards -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# `gateCountBefore` as a sum of layer cardinalities

**Claim.** For a circuit `F` with finite node layers and every `d ≤ F.depth`,

`gateCountBefore F d hd = ∑ j : Fin d, Fintype.card (F.nodes (gateLayerIdx F hd j))`.

The recursively defined gate count agrees with the explicit sum over the first `d`
non-input layers.

**Proof.** Induction on `d` (`induction d with`), generalizing over the proof `hd`.

- Base: `simp [gateCountBefore, gateLayerIdx]` — both sides are `0`.
- Step: with `hd' : d ≤ F.depth`, two `Fin.ext`/`rfl` facts reconcile the index
  conventions: `hcast` (`gateLayerIdx F hd j.castSucc = gateLayerIdx F hd' j`) and
  `hlast` (`gateLayerIdx F hd (Fin.last d) = ⟨d+1, _⟩`); `hsum` transports the
  inductive sum along `hcast` via `Finset.sum_congr`. A `calc` then unfolds with
  `gateCountBefore_succ`, rewrites by the induction hypothesis `ih hd'`, applies
  `hsum` and `hlast`, and finally reassembles the sum with
  `Fin.sum_univ_castSucc` (used symmetrically, after a `change` to the abbreviated
  summand `f`).

**Used in.** `gateCountBefore_depth_eq_size`.
