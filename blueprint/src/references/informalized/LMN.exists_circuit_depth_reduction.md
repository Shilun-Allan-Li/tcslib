<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitTreeManip.lean :: exists_circuit_depth_reduction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# One level of a circuit can be absorbed into its gates

**Claim.** Let `c : Circuit m` have `1 ≤ c.depth`, let `0 < l`, and suppose every gate
function `gates i` has a clean width-`l` DNF (`hDNF`: width `≤ l`, correct, per-term
`varInj` and `Nodup`) and a width-`l` CNF (`hCNF`). Then there exist `m'`, gates
`gates' : Fin m' → DNF n` and a circuit `c' : Circuit m'` with `c'.depth ≤ c.depth - 1`,
all `gates' j` of width `≤ l` and clean, and
`c.eval (fun i => gates i x) = c'.eval (fun j => (gates' j).eval x)` for all `x`.

**Proof.** Strong induction on the depth. `suffices key : ∀ D, …` restates the goal with
`c.depth = D` and is discharged by `key c.depth c gates rfl h_depth hDNF hCNF`; then
`induction D using Nat.strongRecOn`.

1. **`D = 1`** — `exists_circuit_depth_reduction_depth1` gives one signed width-`l` DNF
   `φ`; take `m' := 1`, `gates' := fun _ => φ`, `c' := Circuit.lit ⟨0, sign⟩` (depth `0`
   by `simp [Circuit.depth]`), evaluation by `simp only [Circuit.eval, Lit.eval]`.
2. **`D = 2`** — `exists_circuit_depth_reduction_depth2` already returns the triple with
   `c'.depth ≤ 1`; the bound `1 ≤ 2 - 1` is `omega`.
3. **`D ≥ 3`** — `Circuit.exists_node_of_depth_ge_one` writes `c = Circuit.node isAnd cs`.
   A list induction (`h_elem_le_foldr`) bounds each child's depth by the node's `foldr max`,
   hence `(cs.get j).depth ≤ D - 1`. For each child: if its depth is `≤ 1` use
   `child_depth_le1_has_signed_dnf` (one gate, `Circuit.lit ⟨0, sign⟩`), otherwise apply
   the induction hypothesis `ih` at `(cs.get j).depth < D`. `reduce_children` merges all
   per-child gate families into one `Fin M → DNF n` with re-indexed child circuits.
   The new top circuit is `Circuit.node isAnd ((List.finRange cs.length).map new_cs)`; its
   depth bound follows from `hdep j`, `h_child_depth j` and `omega` plus a `max_le`
   list induction, and evaluation from `node_eval_eq_of_finRange_map`.

**⚠ Incomplete.** Step 3 depends on `reduce_children` (same file, line 400), whose `cons`
case is `sorry` ("type-synthesis failures in mergeGates/reidx refine'"). This theorem is
therefore *not* sorry-free: the depth-1 and depth-2 branches are complete, but the
depth-≥-3 branch — the actual inductive content — rests on an unproved lemma.

**Used in.** `absorbOneLevel_general`, and through it `absorbOneLevel`; both inherit the
`sorry`.
