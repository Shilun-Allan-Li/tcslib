<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RecursiveReduction.lean :: or_children_have_dnf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# An OR node with shallow children has a width-`l` DNF

**Claim.** Let `cs : List (Circuit n)`, `ρ : Restriction n`, `l : ℕ`, and suppose
every child satisfies `dtDepth (restrictFn c.eval ρ) ≤ l`. Then there is a
`φ : DNF n` with `DNF.width φ ≤ l` and `DNF.eval φ x = restrictFn (Circuit.eval
(Circuit.node false cs)) ρ x` for all `x`.

**Proof.** `convert compression_or_of_dnfs (cs.map (fun c => restrictFn c.eval ρ)) l _`
leaves two goals.

1. The evaluation goal: after `rename_i x`, `convert congr_fun
   (restrictFn_node_eval false cs ρ) x using 1` replaces the restricted OR node by
   the `||`-fold over the children, and `induction cs <;> aesop` identifies that
   fold with `List.any` over the mapped list.
2. The hypothesis of `compression_or_of_dnfs` — each mapped function has a
   width-`l` DNF — from `dtDepth_le_implies_small_dnf_cnf _ _ (h_all c hc) |>.1`
   (the `.1` projection is the DNF half of that lemma's conjunction), after
   `simp +zetaDelta at *` clears the `map`.

**Remark.** Exact dual of `and_children_have_cnf`; note it goes through
`dtDepth_le_implies_small_dnf_cnf` directly rather than a `restricted_has_small_*`
wrapper.

**Used in.** `compress_and_switch` (same file), `isAnd = false` branch.
