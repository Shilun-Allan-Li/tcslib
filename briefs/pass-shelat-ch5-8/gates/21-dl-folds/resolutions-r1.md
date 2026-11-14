# Gate 21 · resolutions, round 1 · CLOSED

The verdict is **CLEAR**, with 0 blockers, 0 majors, 1 minor and 0 notes.
- **Findings:** `findings/gate21-dl-folds-findings.md` (SHA-256
  `005e6f268996e8d6f9b84b2d60cb9f16435fb889184356a6b72d83c2565d0af5`). Codex mentions a companion ZIP, but it was not
  received. It is not needed, because the Markdown carries the verdict, the counts and the finding.
- **Audited head:** `fcdb65794698395f8eaa377df0789f7552681633`.
- **Pins:** records `b2427e514c2eb73d71dcbd7e2e88f25001f35592`, exchange `64feab16512bc2ba7fd69c67088d4c8ebdda318f`.

| # | Severity | Disposition |
|---|---|---|
| G21-01 | minor | **Fixed** by **LE-gate21** `d20fbed3beb3710b4db1c0cdf5fb788ff1b2cf9f`, following Seyoon's ruling of 2026-11-14: add `finA_eq` now and split later. |

## G21-01 · LE-gate21

`Games/Efficiency.lean` gains `InteractiveHandler.finA_eq`, the documented equation reader of the promoted `finA`:

```lean
/-- `finA w = pairFstD (pairSndD (pairSndD w))`. -/
theorem finA_eq (w : List Bool) : finA w = pairFstD (pairSndD (pairSndD w)) := rfl
```

- It is the old `NMCCA2.finA_eq` statement in its new home, without `@[simp]`. Nothing else changes.
- The file goes from 979 to 982 lines.
- `finA_eq` reads only `finA`, a definition of its own file, so Rule 10 holds.
- No module in TCSlib or `audits` names a `finA_eq`. The three selective `open … InteractiveHandler (… finA)` lines
  are unaffected.

**The split note (amended).** The Gate 21 pack said that the next change that grows `Games/Efficiency.lean` must
split it first. Under the ruling, this 3-line reader is allowed. The rule now reads: split `Games/Efficiency.lean`
before any change that would take it past about 990 lines. This is recorded in the hand-off.

## Checks at `d20fbed3`

The evidence is in `landing-r1/`.

- **Build:** `Games/Efficiency` and its 42 downstream modules were rebuilt on the consolidation's full tree, through
  root `TCSlib`. All 43 have rc 0 and 0 errors, and each record's `source_sha256` matches the head
  (`le-build-results.jsonl`, order `le-build-order.txt`).
  - No other module imports `Games/Efficiency`, directly or indirectly. Every other module's olean is unchanged
    from the review's 1199/1199 tree.
- **Axioms:** `finA_eq` depends on no axioms (`axioms-finA_eq.log`). The probe file was deleted.
- **Lint:** 216 FAIL and 102 WARN, the same lines as at `fcdb6579` (`lint-head.log`).
- **Widths:** no new line over 100 characters; the file's single over-width line is inherited.
- **Diff:** `LE-gate21.patch`, one file, +3 lines.
- **Base:** every commit on the base after `934eac64` changes records only.

**PR [#299](https://github.com/Shilun-Allan-Li/tcslib/pull/299)** is now at `d20fbed3` and has been marked ready.
