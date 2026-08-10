<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: processClauseLits_len_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Aux output plus remaining path never exceeds the input path

**Claim.** For all `lits`, `path`, `ρ₀`, `σ`,
`(processClauseLits lits path ρ₀ σ).2.2.2.length + (processClauseLits lits path ρ₀ σ).1.length
≤ path.length`: the aux block emitted for the clause, together with the path left
over, is bounded by the path we started with.

**Proof.** Induction on `lits`, generalizing `path`, `ρ₀`, `σ`.

- *Nil*: aux is `[]` and the path is returned untouched (`simp [processClauseLits]`).
- *path = []*: aux is `[]` and the remaining path is `[]` (`simp [processClauseLits]`).
- *Cons* `hd :: tl` against `p :: ps`: `simp only [processClauseLits, List.length_cons]`
  shows one entry is appended to aux while one path entry is consumed; the
  induction hypothesis at `ps` with the two `Function.update`d restrictions plus
  `omega` closes the arithmetic.

**Used in.** `encode_go_wellformed` (`hpcl_len`) and
`razborovEncode_go_numFree_invariant` (`hlen_add`), both times to show the
encoder's fuel/length budget shrinks. The exact-equality strengthening is
`processClauseLits_path_length_eq`.
