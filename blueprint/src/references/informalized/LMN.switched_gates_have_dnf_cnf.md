<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitTreeManip.lean :: switched_gates_have_dnf_cnf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# After switching, every gate has both a clean DNF and a CNF

**Claim.** Let `gates : Fin m → DNF n`, `ρ : Restriction n`, and suppose the
switching step succeeded: `dtDepth (restrictFn (gates i).eval ρ) ≤ l` for every
`i`. Then simultaneously

- every restricted gate has a DNF `φ` with `φ.width ≤ l` computing it, all of
  whose terms are variable-injective (`l₁.var = l₂.var → l₁ = l₂`) and `Nodup`;
- every restricted gate has a CNF `ψ` with `ψ.width ≤ l` computing it.

**Proof.** Term-mode, one line per component.

1. Both components call `dtDepth_le_implies_small_dnf_cnf _ l (h_switch i)`,
   which converts the decision-tree depth bound into a width-`l` DNF *and* a
   width-`l` CNF for the restricted gate.
2. DNF component: replace the raw `φ₀` by `cleanDNF φ₀`. Width is preserved by
   `cleanDNF_width_le` composed with `hw₀` (`le_trans`), the value by
   `cleanDNF_eval` then `he₀`, and the two side conditions are exactly
   `cleanDNF_var_inj φ₀` and `cleanDNF_nodup φ₀`.
3. CNF component: take `ψ₀` and its two properties unchanged.

**Remark.** The only content beyond `dtDepth_le_implies_small_dnf_cnf` is the
`cleanDNF` normalisation, which is there because the downstream absorption
lemmas (and the next round of switching) require variable-injective `Nodup`
terms, not merely bounded width.

**Status.** Currently unused: it packages exactly the `hDNF_fn` / `hCNF_fn`
hypothesis pair that `absorbOneLevel` takes, but no caller in the repository
references it — the file's own callers assemble that pair inline.
