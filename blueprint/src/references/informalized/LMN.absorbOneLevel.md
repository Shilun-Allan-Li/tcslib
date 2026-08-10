<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitTreeManip.lean :: absorbOneLevel -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Absorb one level of the top circuit

**Claim.** Let `data : Layer2Data n`, let `c_top : Circuit data.numGates` have
`1 ≤ c_top.depth`, let `0 < l`, and suppose every gate `data.gates i` has a clean
width-`l` DNF (`hDNF_fn`) and a width-`l` CNF (`hCNF_fn`). Then there are
`data' : Layer2Data n` and `c_top' : Circuit data'.numGates` with
`c_top'.depth ≤ c_top.depth - 1`, `data'.width ≤ l`, and
`c_top.eval (fun i => (data.gates i).eval x) = c_top'.eval (fun j => (data'.gates j).eval x)`
for all `x`.

**Proof.** A two-way case split that dispatches to the two specialised lemmas.

1. `by_cases h1 : c_top.depth ≤ 1`.
2. **Depth exactly 1** — `absorbOneLevel_depth1 data c_top l hl h1 h_depth hDNF_fn hCNF_fn`
   returns `c_top'.depth = 0`; the required `≤ c_top.depth - 1` follows by `omega`.
3. **Depth ≥ 2** — `push_neg at h1` then `absorbOneLevel_general` with `2 ≤ c_top.depth`
   supplied by `omega`; the returned bound is already the goal's, re-derived by `omega`.

The width bound and the evaluation equality are passed through unchanged in both branches.

**⚠ Incomplete.** The depth-≥-2 branch inherits, via `absorbOneLevel_general` and
`exists_circuit_depth_reduction`, the `sorry` in `reduce_children` (same file, line 400 —
the `cons` case of the gate-merge induction). The depth-1 branch is fully proved. Despite
being advertised in the module header as the main combined result, this lemma is not used
anywhere else in the repository yet.
