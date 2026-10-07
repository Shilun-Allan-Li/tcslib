<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/CircuitSize.lean :: gateCountBefore_depth_eq_size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# At full depth the gate count is the circuit size

**Claim.** For a circuit `F` with finite node layers,

`gateCountBefore F F.depth (Nat.le_refl F.depth) = F.size`.

**Proof.** A three-step `calc`.

1. `gateCountBefore_eq_sum_cards` at `d := F.depth` rewrites the left side as
   `∑ j : Fin F.depth, Fintype.card (F.nodes (gateLayerIdx F _ j))`.
2. `Finset.sum_congr` replaces each index by `j.succ`, using
   `hidx : gateLayerIdx F (Nat.le_refl F.depth) j = j.succ` (`Fin.ext`, then
   `rfl`).
3. `size_eq_sum_cards` (used via `symm`) identifies
   `∑ j : Fin F.depth, Fintype.card (F.nodes j.succ)` with `F.size`.

**Used in.** All three `*_size` theorems in this file, which `simpa` with it to
restate the error bounds of the `CircuitDegree` results in terms of `F.size`
instead of `gateCountBefore`.
