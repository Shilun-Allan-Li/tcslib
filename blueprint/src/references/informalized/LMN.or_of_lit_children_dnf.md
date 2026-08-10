<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitTreeManip.lean :: or_of_lit_children_dnf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# OR of literal children has a width-l DNF

**Claim.** Let `cs : List (Circuit m)` consist entirely of literals
(`∀ c ∈ cs, ∃ lr : Lit m, c = Circuit.lit lr`), and let every gate function
`gates i` have both a width-`≤ l` DNF and a width-`≤ l` CNF representation. Then
the OR node over `cs` has a width-`≤ l` DNF: there is `φ : DNF n` with
`φ.width ≤ l` and `φ.eval x = (Circuit.node false cs).eval (fun i => gates i x)`
for all `x`.

**Proof.** The point is that a *negated* gate reference still has a small DNF,
obtained by dualising the gate's CNF.

1. `h_child_functions`: each `c ∈ cs` is `Circuit.lit lr`, so its value is
   `gates lr.idx x` or its negation depending on `lr.sign` (`Circuit.eval`,
   `split_ifs`). Positive sign: use `hDNF` directly. Negative sign: take the
   gate's CNF `ψ` from `hCNF` and use `cnfToDualDNF ψ`, whose width is `ψ.width`
   (`cnfToDualDNF_width`) and whose value is `!(CNF.eval ψ x)`
   (`cnfToDualDNF_eval`). `choose!` extracts the child functions `f` with their
   DNFs (`hf₁`) and their agreement with the children (`hf₂`).
2. `h_eval_or`: unfolding `Circuit.eval` for `isAnd = false` and inducting on
   `cs` shows the node computes `cs.any (fun c => f c x)`.
3. `compression_or_of_dnfs (cs.map f) l` merges the per-child width-`l` DNFs into
   one width-`l` DNF computing their disjunction; `aesop` matches it against
   `h_eval_or`.

**Used in.** `absorbOneLevel_depth1` (OR branch) and
`child_depth_le1_has_signed_dnf`; `and_of_lit_children_cnf` is the dual statement.
