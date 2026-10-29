<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitTreeManip.lean :: exists_circuit_depth_reduction_depth2 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Depth-2 circuits collapse to depth ≤ 1 over new gates

**Claim.** Let `c : Circuit m` have `c.depth = 2`, driven by gate functions
`gates : Fin m → (Fin n → Bool) → Bool` each of which has both a width-`≤ l`
DNF and a width-`≤ l` CNF representation. Then there are `m'`, a new gate family
`gates' : Fin m' → DNF n`, and `c' : Circuit m'` with `c'.depth ≤ 1`, every
`gates' j` of width `≤ l` with variable-injective `Nodup` terms, and
`c.eval (fun i => gates i x) = c'.eval (fun j => (gates' j).eval x)` for all `x`.

**Proof.**

1. `c` is a node: `obtain ⟨isAnd, cs, hc⟩ := Circuit.exists_node_of_depth_ge_one c`.
2. Each `c ∈ cs` has depth `≤ 1`: unfolding `Circuit.depth` in `h_depth` gives
   `1 + foldr max 0 cs = 2`, and an auxiliary `h_max_depth` (list induction,
   `aesop`) bounds any member's depth by that `foldr max`; `linarith`.
3. `list_child_signed_dnfs` then supplies `φs : Fin cs.length → DNF n` and
   `signs`, with the width, `var_inj`, `Nodup`, and signed-evaluation properties.
4. `build_literal_circuit isAnd cs.length signs` returns the new top circuit
   `c' = Circuit.node isAnd ((List.finRange cs.length).map (fun j => Circuit.lit ⟨j, signs j⟩))`
   together with `c'.depth ≤ 1`. Take `m' := cs.length`, `gates' := φs`.
5. Evaluation: `rw [hc, hc'_eval]` then `cases isAnd`. Each branch proves a
   `foldr` identity over an arbitrary index list by induction (rewriting each
   child's value with `h_eval`, splitting on `signs j` in the AND branch), then
   transports it to `List.finRange cs.length` via `convert`, `List.foldr_map`,
   and `List.ext_get`.

**Used in.** `exists_circuit_depth_reduction`, as the `D = 2` base case of the
strong induction on depth.
