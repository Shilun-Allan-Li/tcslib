# External audit pack, round 2 — the controller-stopped writer and one guess-then-run host (PR #174, an API gate)

**Round 1** (`pack.md`, at `1045624d`; findings `findings.md`): **FAIL, 0 blockers, 1 major, 2
minors, 13 notes.** The proofs, the generalization and the screen dispositions were confirmed
(notes 3–11, 13, 15). The major (finding 1): the three new public definitions had no reading
lemmas. The minors: a docstring (finding 2) and a sentence of the pack (finding 12). The
maintainer's resolutions are `resolutions.md`.

**The PR now:** #174 on `lean/nf-ndhost-api`, head `086c0ef0f99a696f76c0f213f27c85a71902157a`:
round 1's head with the fix commit `4c0a5943` (`evidence/round1-fix/round1-fix.patch`, 140 lines)
and the campaign's records merged in (no Lean change; `NDHost`'s blob is `c01cd773` at both).

## What changed since round 1 (verify)

| Class | Declarations |
|---|---|
| **New public, the readings** (finding 1) | the state family's fibers `Turing.GuessRunPhase.ctlState_pre`, `_guess`, `_skip`, `_back`, `_run`, `_out`; the phases `Turing.guessCtlRunPhases_pre`, `_guess`, `_skip`, `_back`, `_run`, `_out`; the redirects `Turing.guessCtlRunRed_pre`, `_guess_done`, `_guess_run`, `_skip`, `_back`, `_run`, `_out` |
| **Text** (finding 2) | `guessCtlRunTM`'s docstring: the step right and the rewind, qualified by the run lemmas' delimiters |
| **Unchanged** | every other declaration (the patch touches only these) |

## Brief for the auditor

1. **Finding 1.** Do the 19 lemmas meet policy §1's second form, "case lemmas that together cover
   every input"? In particular: the redirect lemmas `_pre`, `_skip`, `_back` and `_run` are each
   stated for every state of their phase (as an `if`), `_guess_done` and `_guess_run` together
   cover the writer's states, and `_out` every verdict bit. Are any stated wrongly, or under a
   `@[simp]` attribute (there is none)? Check 8's list for `NDHost` is again the base's three names
   (`evidence/round1-fix/lint-head-TuringMachine.txt` against `evidence/lint-base-TuringMachine.txt`).
2. **Finding 2.** Is `guessCtlRunTM`'s docstring now accurate for every writer flavor and controller?
3. **Finding 12.** Is the erratum in `resolutions.md` accurate? Round 2's seal covers eight regions
   (round 1's five and the three blocks of the new lemmas; `evidence/round1-fix/NDHostSealed.*`,
   generator `mkseal_nf3.py`): 0 diagnostics.
4. **Duplication.** The new case lemmas are short and parallel. The screen at `4c0a5943` against the
   same base (`evidence/round1-fix/screen/`): ⟨SCREEN⟩. Are its dispositions right?
5. **Anything else** in the fix diff.

## Repository-side attestations (verify or challenge)

- **Elaboration** against `oleans-lhh`: the head module with 20 axiom prints
  (`evidence/round1-fix/NDHostAx.*`): 0 diagnostics; the 16 theorems of the host family on
  `[propext, Classical.choice, Quot.sound]`, the four sampled case lemmas
  (`ctlState_pre`, `guessCtlRunPhases_skip`, `guessCtlRunRed_skip`, `guessCtlRunRed_run`) on none.
- **Freeze** (`evidence/round1-fix/freeze-NDHost.txt`): 25 → 56 public, 7 → 13 private, nothing
  removed, no signature changed; the same five pattern-matching artifacts and four disclosed body
  changes as round 1 (`freeze-note.txt`).
- **Lint:** `TuringMachine` 0 FAIL, 68 WARN over 85 files; `NDHost`'s check 8 the base's three names;
  the policy linter its one size finding (`style-lint-head-NDHost.txt`). No line over 100
  characters.
- **Replay:** `replay-lnfapi4.sh` (`evidence/round1-fix/`), the same 4 modules from `oleans-lhh`,
  pinning blob `c01cd773`. ⟨REPLAY⟩

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/85-nf-ndhost-api/findings-r2.md`. The gate closes when it has zero blockers and zero
majors.

**Deliver your findings as a downloadable Markdown file named `nf-ndhost-api-r2-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.
