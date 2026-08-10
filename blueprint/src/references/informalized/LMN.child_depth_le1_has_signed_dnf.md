<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitTreeManip.lean :: child_depth_le1_has_signed_dnf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A depth-≤-1 child has a signed width-l DNF

**Claim.** Let `c_j : Circuit m` have `c_j.depth ≤ 1`, and let every gate function
`gates i` have both a width-`l` DNF (`hDNF`) and a width-`l` CNF (`hCNF`). Then there
are `φ : DNF n` and a polarity `sign : Bool` with `φ.width ≤ l` such that the *signed*
evaluation matches the child, `(if sign then φ.eval x else !(φ.eval x)) =
c_j.eval (fun i => gates i x)` for all `x`, and `φ` is clean: within each term, two
literals on the same variable are equal (`varInj`) and each term is `Nodup`.

**Proof.** Case split on the depth, then on the gate type; every branch produces `φ`
via `cleanDNF`, whose width/cleanliness facts come from `cleanDNF_width_le`,
`cleanDNF_var_inj`, `cleanDNF_nodup`, and correctness from `cleanDNF_eval`.

1. **`c_j.depth = 0`** — `Circuit.depth0_is_lit` gives `c_j = Circuit.lit lr`, so the
   child function is `gates lr.idx` up to `lr.sign` (`simp [Circuit.eval]`). Take `φ`
   to be the DNF from `hDNF lr.idx`, cleaned; `sign := lr.sign`.
2. **`c_j.depth ≠ 0`** — `Circuit.exists_node_of_depth_ge_one` applied via
   `Nat.pos_of_ne_zero` writes `c_j = Circuit.node isAnd cs`,
   and `Circuit.depth1_all_lits` shows every child of `cs` is a literal.
   - `isAnd = true`: `and_of_lit_children_cnf` yields a width-`l` CNF `ψ` for the node;
     set `φ := cleanDNF (cnfToDualDNF ψ)` and `sign := false`, correctness by
     `cnfToDualDNF_eval` (width by `cnfToDualDNF_width`).
   - `isAnd = false`: `or_of_lit_children_dnf` yields a width-`l` DNF `φ` for the node
     directly; take it cleaned with `sign := true`.

The `sign` bit is what lets a single DNF cover both gate types: an AND of literals is
representable only as a CNF at width `l`, so it is recorded as the negation of a DNF.

**Used in.** `exists_circuit_depth_reduction_depth1` and the depth-≤-1 branch of
`exists_circuit_depth_reduction`; also `list_child_signed_dnfs`.
