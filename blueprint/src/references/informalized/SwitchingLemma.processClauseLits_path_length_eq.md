<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: processClauseLits_path_length_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# processClauseLits consumes exactly min(#lits, #path) path entries

**Claim.** `(processClauseLits lits path ρ₀ σ).1.length + min lits.length path.length
= path.length`. Exactly one path entry is consumed per processed literal, and
processing stops as soon as either the literal list or the path is exhausted.

**Proof.** Induction on `lits`, generalizing `path`, `ρ₀`, `σ`.

- *Nil*: the path is returned unchanged and the `min` is `0` (`simp [processClauseLits]`).
- *path = []*: the remaining path is `[]` and the `min` is `0` (`simp [processClauseLits]`).
- *Cons* `hd :: tl` against `p :: ps`: after `simp only [processClauseLits,
  List.length_cons]`, the induction hypothesis at `ps` with `ρ₀`, `σ` updated at
  `hd.1.var` gives the equation one step down, and `omega` handles
  `min (tl.length + 1) (ps.length + 1) = min tl.length ps.length + 1`.

**Used in.** `razborovEncode_go_numFree_invariant` (`htight`) — the tight version
of `processClauseLits_len_add`, needed so that the `numFree` drop can be equated
with the *full* path length rather than merely bounded.
