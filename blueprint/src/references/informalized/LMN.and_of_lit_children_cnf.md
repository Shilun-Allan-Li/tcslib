<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitTreeManip.lean :: and_of_lit_children_cnf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# An AND of literal children has a width-l CNF

**Claim.** Let `cs : List (Circuit m)` be a list of circuits all of which are single
literals (`h_all_lits`), and let `gates : Fin m → (Fin n → Bool) → Bool` be gate
functions such that every gate has a width-`l` DNF (`hDNF`) **and** a width-`l` CNF
(`hCNF`). Then the function computed by the AND node `Circuit.node true cs` under the
substitution `i ↦ gates i` itself has a width-`l` CNF: there is `ψ : CNF n` with
`ψ.width ≤ l` and `CNF.eval ψ x = (Circuit.node true cs).eval (fun i => gates i x)`
for all `x`.

**Proof.** Reduce to the CNF compression lemma for a conjunction of functions.

1. `convert compression_and_of_cnfs _ l _`, instantiating the child-function list as
   `cs.map (fun c x => c.eval (fun i => gates i x))` (`case convert_2`).
2. *Shape goal:* `(Circuit.node true cs).eval` is `foldr (· && ·) true` by definition
   (`simp [Circuit.eval]`), which matches `List.all` over the mapped list; closed by
   `induction cs <;> aesop`.
3. *Hypothesis goal:* each mapped child function needs a width-`l` CNF. Given
   `f ∈ cs.map …`, recover the child (`List.mem_map`) and then the literal
   `lr : Lit m` it is (`h_all_lits`), so the child function is `x ↦ (gates lr.idx x)`
   or its negation depending on `lr.sign` (`simp [Circuit.eval]`, `split_ifs`).
   - positive sign: use `hCNF lr.idx` directly;
   - negative sign: take `dnfToDualCNF φ` for the DNF `φ` from `hDNF lr.idx`, with the
     width bound from `dnfToDualCNF_width` and correctness from `dnfToDualCNF_eval`.

The CNF representation of a *negated* gate is why the hypotheses demand both a DNF and
a CNF for every gate: the AND node may read a gate under either polarity.

**Used in.** `absorbOneLevel_depth1` (AND case) and `child_depth_le1_has_signed_dnf`
(AND case).
