# Gate 04 (Pass–shelat ch. 5–8, S2b), round 2: external closing audit pack

**What is audited:** PR [Shilun-Allan-Li/tcslib#195](https://github.com/Shilun-Allan-Li/tcslib/pull/195)
(`cryptography/pass-shelat-ch5-8-s2b` into `cryptography/pass-shelat-ch2-4`) at its head
`243598b7cb0c3fdd50b22a92a011f1b77f55c8c6`.
- **Round 1** audited `afe5982f612081bba2fbcec9ab41adcbbc118b13` and found **0 blockers, 2 majors,
  4 minors** (`gate04-s2b-findings.md`, in the bundle, verbatim). The maintainer's review added N1
  (proposed major: T1/T2 do not cover the reductions they are cited for) and N2–N7 (minor).
- **The repairs:** two commits after `afe5982f`: `f6d57307` (F01–F04, F06, N5, N6) and `243598b7`
  (N1, ruling R-04-3). Their full diff is `evidence-r2/repair.diff.txt`; each item's resolution is
  in `resolutions-r1.md` (both in the bundle).
- **The deliverable:** **`gate04-s2b-r2-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10] (PDF; book page = PDF page − 12).

## Brief for the auditor

Round 2 does two things.
1. **It verifies the round 1 resolutions.** For each of F01–F06 and N1–N7 say whether the resolution
   is adequate: **fixed** (the defect is gone, and the fix introduces no new one), **recorded**
   (accepted as declared or scheduled work, and the record is accurate), or **not resolved** (say
   why).
2. **It audits the changed surface afresh:**
   - the codec: is `decodeIdx` now exact, and do the converse lemmas characterize `decodeBitMove`
     on every word?
   - the equation lemmas: does each state its definition's defining equation (and nothing
     stronger or weaker)? Do the re-pointed proofs avoid reading other files' definitions?
   - **the efficiency layer, restated (R-04-3):** `seedIn`; the new handler fields (`advIn`,
     `out`; `outLen`, `finCall`, `finRun`); T1 with exact output; T2 with the finalization and
     budget `q·perCall + finCall`; the companion `exists_toCompOn_of_toComp`; T4
     `exists_toOracleAdversary_of_bitCodec`. Restate each new or changed definition in your own
     words before reading its docstring, and say whether each statement is what its docstring
     claims. Are T1, T2 and T4 **usable contracts** for the reductions listed in the resolutions'
     table (one adversary run, polynomial input and finalization, exact output)? Is any hypothesis
     missing or vacuous?

Attempt at least **three adversarial instantiations** of the new handlers. Look for regressions:
anything round 1 accepted that the repairs broke. Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Round 1 findings, resolutions, repair diff | `gate04-s2b-findings.md`, `resolutions-r1.md`, `evidence-r2/repair.diff.txt` |
| Changed Lean, at `243598b7` | the 25 files of `evidence-r2/changed-files.txt` (S2b's files, S2a's `Advantage`, `Simulate`, `OracleComp`, `Protocols`, and ch. 2–4's `Interaction`, which gained equation lemmas) |
| Context | `policy.md`; `design/S2b-efficiency.md` (stale on the efficiency layer's statements: superseded by R-04-3, see the resolutions) |

## Attestations (maintainer execution claims; `evidence-r2/`)

- **Elaboration** (`replay.log`): the 60 modules downstream of the files changed since `afe5982f`,
  in import order, from a fresh copy of the `afe5982f` olean tree: **all pass, 0 errors**.
  `sorry` warnings only in `Games/Efficiency` (4: T1, T2, the companion, T4) and the
  pre-existing 3-colouring stubs (3).
- **Axioms** (`axioms.log`): every public theorem of the 25 changed files, 379; **375 standard**;
  `sorryAx` exactly in T1, T2, `exists_toCompOn_of_toComp` and T4.
- **Lint** (`lint.log`): 0 findings in each of the 25 files. **Check 8** (`check8.log`, N2/N7):
  0 failures in `Games/`; 3 warnings on older S2a definitions. The **rule-10 seal** check (each
  re-pointed consumer compiled with the other files' definitions `local irreducible`) was run by
  the repair worker (script `seal.py.txt`).

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Plus one line per round 1 item: `F01: fixed / recorded / not resolved — <reason>` (also N1–N7).

Severity guide: **blocker** (a downstream phase would build on a wrong statement); **major** (fixable
but materially misleading, or debt that needs explicit acknowledgment); **minor** (an edge case,
naming or attribution); **note** (no change required). The gate closes at **0 blockers and 0
majors**.
