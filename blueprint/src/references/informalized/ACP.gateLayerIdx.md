<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/CircuitSize.lean :: gateLayerIdx -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Index of the `(j+1)`-st node layer

**Definition.** For a circuit `F`, a bound `hd : d ≤ F.depth` and `j : Fin d`,
`gateLayerIdx F hd j : Fin (F.depth + 1)` is `⟨j.1 + 1, _⟩`, the layer index one
above `j`. The proof obligation is `Nat.succ_lt_succ (Nat.lt_of_lt_of_le j.2 hd)`.

Note the target is `Fin (F.depth + 1)`, the type of *all* node layers including the
input layer `0`, while the domain `Fin d` ranges over gate layers only.

**Remark.** Purely bookkeeping: it lets the non-input layers `1, …, d` be indexed
by `Fin d` so they can be summed over, avoiding `Fin`-arithmetic in the statement
of `gateCountBefore_eq_sum_cards`. It is a plain `def` with no proof content beyond
the index bound.

**Used in.** `gateCountBefore_eq_sum_cards` and `gateCountBefore_depth_eq_size`,
where `gateLayerIdx F (le_refl _) j` is shown to equal `j.succ` by `Fin.ext` and
`rfl`.
