<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Encoding.lean :: processClauseLits_path_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# processClauseLits never lengthens the remaining path

**Claim.** For all `lits : List (Literal n × ℕ)`, `path : List (Fin n × Bool)` and
restrictions `ρ₀ σ`, the returned remaining path is no longer than the input path:
`(processClauseLits lits path ρ₀ σ).1.length ≤ path.length`.

**Proof.** `induction lits generalizing path ρ₀ σ`.

- *Nil*: the path is returned unchanged, so the goal is `path.length ≤
  path.length` (`simp [processClauseLits]`).
- *Cons* `hd :: tl`, then `cases path`:
  - `path = []`: the result is `[]` (`simp [processClauseLits]`).
  - `path = p :: ps`: after `simp only [processClauseLits]` the remaining path is
    that of the recursive call on `ps`, so `ih _ _ _` gives
    `… ≤ ps.length` and `le_trans` with `Nat.le_succ _` lifts it to
    `ps.length + 1`.

A deliberately granular helper: the sharp form
`processClauseLits_path_length_eq` (remaining `+ min lits.length path.length =
path.length`) is proved separately; this inequality is the weak consequence that
suffices for termination/monotonicity arguments about the encoding loop.
