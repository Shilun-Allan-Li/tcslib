# PR #126's body, as retrieved 2026-10-17 (head `5333b29b`)

## C1-E: the exponential decider becomes a hypothesis of `exists_diagonalizer` (a statement PR)

**The cycle (gate 40's review, X2).**
- The diagonalizer's fill E-D needs BF (`Turing.exists_ndAcceptsWithin_decider`), stated in
  `Diagonalization/NTimeHierarchy`.
- That module's `ntime_hierarchy` must import `NTimeDiagonalizer`.
- So neither file can import the other.

**The ruling (user, 2026-10-17):** BF becomes a hypothesis, after #121 merges, by a statement PR
with its own gate, before E-D's brief.

**Stacked on #125** (the §13d G4 partial's landing), keeping the replay chain linear. Merge #121
through #125 first.

### What

`Diagonalization/NTimeDiagonalizer` only.
- **`exists_diagonalizer`** takes `hBF`, exactly the conclusion of
  `exists_ndAcceptsWithin_decider c`.
  - Its docstring says why the decider is a hypothesis, and the sketch's top rung reads `hBF`.
  - `ntime_hierarchy`'s proof will call `exists_diagonalizer hf hg c
    (exists_ndAcceptsWithin_decider c)`.
- **Gate 40's X3:** two docstring lines no longer call the middle query word R's input. `D`
  rewrites its budget field first.

### Checks (maintainer, against `oleans-lndiag2`)

- **Elaboration:** 0 errors; the two contracts' `sorry`s, as before.
- **Consumer probe:** in a file importing both modules, the new statement (inline) accepts
  `exists_ndAcceptsWithin_decider c` as `hBF` (`audits/evidence/c1/c1e/x2/Consumer.lean.txt`).
- **Freeze:** 22 → 22 publics. The statement change is `exists_diagonalizer`'s (intended); the
  other body change is `query`'s docstring.
- **Lint:** `Diagonalization/` 0 FAIL, 1 WARN, unchanged.
- **Screen** (gate 39's 7-file population): 49 → 49 declarations, 6 → 6 pairs, no new pair.
- **Replay:** `replay-lx2.sh`, 2 modules (`NTimeDiagonalizer` and the `Diagonalization` facade),
  chained from `oleans-lg4c1`.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

