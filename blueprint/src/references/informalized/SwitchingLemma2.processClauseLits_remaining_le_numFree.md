<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: processClauseLits_remaining_le_numFree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The path-length ≤ numFree budget survives processClauseLits

**Claim.** If `path.length ≤ ρ₀.numFree`, then
`(processClauseLits lits path ρ₀ σ).1.length ≤ (processClauseLits lits path ρ₀ σ).2.1.numFree`
— the invariant "there is at least one free variable left per remaining path
entry" is preserved.

**Proof.** Induction on `lits`, generalizing `path`, `ρ₀`, `σ`.

- *Nil*: outputs are the inputs, so this is `h0` (`simpa [processClauseLits]`).
- *path = []*: the remaining length is `0` (`simp [processClauseLits]`).
- *Cons* `hd :: tl` against `p :: ps`: the path loses exactly one entry while
  `numFree` loses at most one — `numFree_update_some_ge ρ₀ hd.1.var p.2` gives
  `numFree (update ρ₀ hd.1.var (some p.2)) + 1 ≥ ρ₀.numFree`. With
  `(p :: ps).length = ps.length + 1` and `omega` this yields
  `ps.length ≤ numFree (update ρ₀ hd.1.var (some p.2))`, which feeds `ih`.

*Anomaly.* This lemma is currently **unused** — no other declaration in the
repository references it. `razborovEncode_go_numFree_invariant` carries the
corresponding budget through `processClauseLits_path_length_eq` and
`processClauseLits_numFree_ρ_eq` instead.
