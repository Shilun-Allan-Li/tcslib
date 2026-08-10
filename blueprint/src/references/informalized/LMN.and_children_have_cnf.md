<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RecursiveReduction.lean :: and_children_have_cnf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# An AND node with shallow children has a width-`l` CNF

**Claim.** Let `cs : List (Circuit n)`, `ρ : Restriction n`, `l : ℕ`, and suppose
every child satisfies `dtDepth (restrictFn c.eval ρ) ≤ l`. Then there is a
`ψ : CNF n` with `CNF.width ψ ≤ l` and `CNF.eval ψ x = restrictFn (Circuit.eval
(Circuit.node true cs)) ρ x` for all `x`.

**Proof.**

1. `have h_compression`: there is a width-`l` CNF computing
   `(cs.map (fun c => restrictFn c.eval ρ)).all (fun f => f x)`. Obtained by
   `convert compression_and_of_cnfs _ _ _`, whose hypothesis (each member of the
   list has a width-`l` CNF) is supplied by destructuring `List.mem_map.mp hf`
   into a child `c` and applying `restricted_has_small_cnf_of_dtDepth_le` to
   `h_all _ hc`.
2. `obtain ⟨ψ, hψ₁, hψ₂⟩ := h_compression; use ψ` — the width bound `hψ₁`
   transfers verbatim.
3. For the evaluation, `simp +decide [*, restrictFn_node_eval]` rewrites the goal
   into the `&&`-fold form of the restricted AND node; `induction cs <;> aesop`
   then identifies that fold with `List.all` over the mapped list.

**Remark.** All the switching content is upstream — this lemma only lifts
`compression_and_of_cnfs` from a list of Boolean functions to the children of a
circuit node.

**Used in.** `compress_and_switch` (same file), `isAnd = true` branch.
