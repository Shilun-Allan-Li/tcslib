# External audit pack, round 2 — the polynomial bounds' constructibility moves to `Constructible` (PR #175, an API gate)

**Round 1** (`pack.md`, at `6ae641a2`; findings `findings.md`): **FAIL, 0 blockers, 2 majors,
3 minors, 10 notes.** The move, the freeze, rule 10, the screen and the integrity were confirmed
(notes 6–14). Both majors asked for the user's explicit acknowledgment of duplication debt. The
minors: the copy search's wording (3), the replay driver's exit status (4), the records' and the
module docstrings' campaign prose (5). The maintainer's resolutions are `resolutions.md`.

**The user's rulings (2026-10-27).** Finding 1: the inline `logSpace n ≤ n + 1` is **accepted as
debt**, retired in the dedup window (12.2c) by moving `logSpace_le_succ` to `SpaceComplexity/Basic`
(ledger LS-1). Finding 2: **re-point `hD'` now** to `computesFunInTime_decideEq []`, and **accept**
`WordTests`' source-inclusive census (1 of 4 declarations, 25%), the `SAT` and `CookLevin` twins
re-pointed in 12.2c (ledger PL-1, corrected).

**The PR now:** #175 on `lean/scp-constructible`, head `ca0eafb83a97b020e054556598b340b55a648461`:
round 1's head with the fix commit `00d5ff05` (`evidence/round1-fix/round1-fix.patch`) and the
campaign's records merged in (no Lean change). The blobs: `Constructible` `9fb71337`, `Savitch`
`b4157d58`.

## What changed since round 1 (verify)

| Class | Change |
|---|---|
| **Code** (`evidence/round1-fix/code-only-diff.txt`) | `Constructible` imports `TuringMachine/Build/WordTests`; `spaceConstructible_poly` takes its empty-input decider as `obtain ⟨D, cD, hD'⟩ := FinTM.computesFunInTime_decideEq []`, and the inline conversion of `computesFunInTime_ifEq [] [true] [false]` (seven lines) is gone; its proof sketch cites the new row. Nothing else in the code of either file |
| **Text** (finding 5) | both module docstrings without their phase, plan, gate and audit history; `Savitch`'s `## Main definitions` heading; four declaration docstrings without audit or phase labels (`spaceConstructible_logSpace`'s and `_linear`'s sketches, `_linear`'s statement docstring, `PSPACE_eq_NPSPACE`'s sketch) |
| **Records** | the ledger's LS-1 and PL-1 entries (`evidence/round1-fix/ledger-excerpt.txt`); the seal generator's "eight"; the replay generator's exit status (`devtools/seyoon/mkreplay.py`, finding 4); the copy search per ref (finding 3) |

## Brief for the auditor

1. **Findings 1 and 2.** Do the recorded rulings and the corrected census (`ledger-excerpt.txt`)
   discharge the two majors? Is the re-pointed `hD'` the published row's exact statement, so that
   no copy of the fixed-word test is left in `Constructible`?
2. **The fix's code.** Is the import's cost as stated (`Build/WordTests` imports only
   `Build/Primitives`, already in `Constructible`'s closure; no cycle)? Does the proof still use
   only published readings (`evidence/round1-fix/inspection-args.txt`, round 1's classification
   less the two arguments of the removed block)?
3. **Finding 3.** Does `api-copy-search.txt` support "at most one file on every ref"?
4. **Finding 4.** Does `replay-lscp2.sh` exit nonzero whenever a module fails or the static check
   finds a mismatch?
5. **Finding 5.** Are the module docstrings now public-facing? The remaining design-note references
   in two inherited proof sketches (`P11`, `§12 R3`, `R8.5c`) are left for the deferred docstring
   cleanup: is that acceptable?
6. **Anything else** in the fix diff.

## Repository-side attestations (verify or challenge)

- **Elaboration** against `oleans-lhh` at `00d5ff05`: `Constructible` with four axiom prints, 0
  diagnostics, all four theorems on `[propext, Classical.choice, Quot.sound]`
  (`ConstructibleAx.*`); `Savitch`, its one expected sorry warning (`Savitch.out`).
- **Rule 10:** the same 12 definitions sealed and 3 erased, 0 diagnostics (`ConstructibleSealed.*`,
  generator `evidence/scripts/mkseal_scp.py`); the 15 controls' output identical to round 1's
  (`ConstructibleSealControl.*`).
- **Freeze** (`freeze-*.txt`, against the base and against round 1): no statement changed; the
  "body changes" of three declarations are docstring-only (`freeze-note.txt`, `code-only-diff.txt`).
- **Lint:** `SpaceComplexity` 0 FAIL, 82 WARN over 107 files, the base's but for the two files'
  INFO lines; the policy linter 0 findings on both files (`lint-head-*`, `style-lint-head.txt`).
- **Screen** (13 files: round 1's 12 and `Build/WordTests`; base at `940671e0`, head at `ca0eafb8`;
  `evidence/round1-fix/screen/`): 848 declarations and 1,146 pairs at both, none new and none gone
  (`pairdiff.txt`); no pair involves the moved block. The removed conversion was an inline step,
  not a declaration, so the pair count is unchanged.
- **Replay:** `replay-lscp2.sh`, the same 53 modules from `oleans-lnfapi4`, pinning both blobs; its
  precheck passed. **Pending** (a merge condition of its own).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/86-scp-constructible-api/findings-r2.md`. The gate closes when it has zero blockers
and zero majors.

**Deliver your findings as a downloadable Markdown file named `scp-constructible-api-r2-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
