<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitTreeManip.lean :: reduce_children -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Merging the per-child reduction results into one gate set

**Claim.** Let `cs : List (Circuit m)` with gate functions `gates`, a width bound
`l`, and a per-child depth bound `bound : Fin cs.length → ℕ`. Suppose every child
`cs.get j` has already been reduced: there are `m_j`, gates `g_j : Fin m_j → DNF n`
and `c_j : Circuit m_j` with `c_j.depth ≤ bound j`, all `g_j k` of width `≤ l`
with variable-injective `Nodup` terms, and `c_j` computing the child. Then there
is a *single* merged gate family `merged : Fin M → DNF n` and re-indexed circuits
`new_cs : Fin cs.length → Circuit M` with the same width / `var_inj` / `Nodup`
properties, `(new_cs j).depth ≤ bound j`, and
`(new_cs j).eval (fun k => (merged k).eval x) = (cs.get j).eval (fun i => gates i x)`.

**Proof.**

1. `choose m_j g_j c_j … using h_results` names the per-child data.
2. `induction' cs` on the child list. The empty case takes `M = 0`, `merged _ = ∅`,
   and `new_cs = fun _ => Fin.elim0 ‹_›` (no indices exist), all goals by `simp`.
3. **The cons case is `sorry`** — the source comment records the intended route
   (concatenate the two gate sets with `mergeGates` and re-index the circuits
   through `Circuit.reidx` along `Fin.castAdd` / `Fin.natAdd`, whose evaluation
   lemmas live in `LMN/GateMerge.lean`) and the reason it was left open:
   type-synthesis failures in the `refine'`.

**Anomaly.** This is an incomplete proof. Its `sorry` is inherited by
`exists_circuit_depth_reduction` (depth ≥ 3 branch), and hence by
`absorbOneLevel_general` and `absorbOneLevel`.
