<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitTreeManip.lean :: absorbOneLevel_depth1 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Absorbing a depth-1 top circuit into a single gate

**Claim.** Let `data : Layer2Data n` and `c_top : Circuit data.numGates` with
`c_top.depth ≤ 1` and `1 ≤ c_top.depth` (so depth exactly `1`), let `0 < l`, and suppose
every gate `data.gates i` has a clean width-`l` DNF (`hDNF_fn`) and a width-`l` CNF
(`hCNF_fn`). Then there are `data' : Layer2Data n` and `c_top' : Circuit data'.numGates`
with `c_top'.depth = 0`, `data'.width ≤ l`, and
`c_top.eval (fun i => (data.gates i).eval x) = c_top'.eval (fun j => (data'.gates j).eval x)`
for all `x`. In other words the entire two-level circuit becomes one width-`l` gate read
through a bare literal.

**Proof.** Split on the gate type of the top node.

1. `Circuit.exists_node_of_depth_ge_one` gives `c_top = Circuit.node isAnd cs`, then
   `by_cases h : isAnd <;> simp_all only`. In both branches
   `Circuit.depth1_all_lits` supplies that every child of `cs` is a literal.
2. **AND (`isAnd = true`)** — `and_of_lit_children_cnf` yields a width-`l` CNF `ψ` for the
   composed function (the DNF/CNF hypotheses are weakened to their width+correctness
   parts). Take `data'` with `numGates = 1` and single gate `cleanDNF (cnfToDualDNF ψ)`
   (width by `cleanDNF_width_le` and `cnfToDualDNF_width`, cleanliness by
   `cleanDNF_var_inj` / `cleanDNF_nodup`), and `c_top' := Circuit.lit ⟨0, false⟩` — the
   *negative* literal, which undoes the dualisation. Evaluation by `cleanDNF_eval` and
   `cnfToDualDNF_eval` against `hψ₂`.
3. **OR (`isAnd = false`)** — `or_of_lit_children_dnf` yields a width-`l` DNF `φ` directly.
   Take the single gate `cleanDNF φ` and `c_top' := Circuit.lit ⟨0, true⟩`; the four record
   side goals are `cleanDNF_width_le`, `linarith` (for `0 < l`), `cleanDNF_var_inj`,
   `cleanDNF_nodup`, and evaluation is `cleanDNF_eval` composed with `hφ.2`.

The sign of the output literal is the only asymmetry between the branches: an AND of
literals is only width-`l`-representable as a CNF, so it is stored as a dualised DNF and
read negatively.

**Used in.** `absorbOneLevel` (the `c_top.depth ≤ 1` branch). This branch is fully proved —
it does not touch `reduce_children`.
