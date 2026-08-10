<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitTreeManip.lean :: absorbOneLevel_general -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Absorbing one level of a depth-≥-2 top circuit

**Claim.** Let `data : Layer2Data n`, let `c_top : Circuit data.numGates` have
`2 ≤ c_top.depth`, let `0 < l`, and suppose every gate `data.gates i` is computed by a
clean width-`l` DNF (`hDNF_fn`) and by a width-`l` CNF (`hCNF_fn`). Then there are new
`data' : Layer2Data n` and `c_top' : Circuit data'.numGates` with
`c_top'.depth ≤ c_top.depth - 1`, `data'.width ≤ l`, and
`c_top.eval (fun i => (data.gates i).eval x) = c_top'.eval (fun j => (data'.gates j).eval x)`
for all `x`.

**Proof.** Pure repackaging of `exists_circuit_depth_reduction` into the `Layer2Data`
record.

1. `obtain ⟨m', gates', c', hd, hw, hvi, hnd, he⟩ := exists_circuit_depth_reduction c_top
   (fun i => (data.gates i).eval) l hl (by omega) hDNF_fn hCNF_fn` — the depth hypothesis
   `1 ≤ c_top.depth` comes from `2 ≤ c_top.depth` by `omega`.
2. Assemble `data' := ⟨m', gates', l, hw, hl, hvi, hnd⟩`: the returned width bound, the
   positivity `0 < l`, and the per-term `varInj` / `Nodup` facts are exactly the record's
   `widthBound`, `widthPos`, `varInj`, `nodup` fields. `data'.width ≤ l` is `le_refl l`.

**⚠ Incomplete.** Inherits the `sorry` in `reduce_children` (same file, line 400) through
`exists_circuit_depth_reduction`. Since the hypothesis here is `2 ≤ c_top.depth`, the
depth-2 case is genuinely proved but every deeper case is not.

**Used in.** `absorbOneLevel` (the `c_top.depth > 1` branch).
