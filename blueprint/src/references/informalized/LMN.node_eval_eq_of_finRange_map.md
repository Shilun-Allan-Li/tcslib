<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitTreeManip.lean :: node_eval_eq_of_finRange_map -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Replacing a node's children index-by-index preserves its value

**Claim.** Let `cs : List (Circuit m)` and `new_cs : Fin cs.length → Circuit M`,
with inputs `g : Fin m → Bool` and `g' : Fin M → Bool`. If
`(new_cs j).eval g' = (cs.get j).eval g` for every index `j`, then

`(Circuit.node isAnd cs).eval g = (Circuit.node isAnd ((List.finRange cs.length).map new_cs)).eval g'`

for either gate type `isAnd`.

**Proof.** `unfold Circuit.eval`, then `cases isAnd` — both branches are the same
`foldr` argument, once for `||`/`false` and once for `&&`/`true`.

1. OR case (`isAnd = false`): prove `h_foldr_eq`, the disjunction-`foldr`
   equality over an *arbitrary* index list `l` (list induction, `aesop`, closed
   by `heval`), then `convert` it at `l := List.finRange cs.length`. The two
   remaining bookkeeping goals identify `cs` with `(finRange).map (cs.get ·)`
   via `List.ext_get` and `List.ofFn_eq_map`.
2. AND case (`isAnd = true`): direct induction on `cs`, with the inductive
   hypothesis specialised to the tail's children `fun i => new_cs i.succ`, again
   finished by `simp`/`aesop` with `List.ofFn_eq_map`.

**Used in.** `exists_circuit_depth_reduction` (depth ≥ 3 branch), as the
`eval_correct` step: after each child is reduced and re-indexed, the top gate is
rebuilt as `Circuit.node isAnd ((List.finRange cs.length).map new_cs)` and this
lemma is what says the rebuilt gate computes the same function.
