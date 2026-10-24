# External audit pack — C1, the replay canonizer (PR #160, a fill gate)

Campaign: the Arora-Barak chapters 3-4 plan, C1 (the timed universal NDTM behind the
nondeterministic time hierarchy, [AB09, Theorem 3.2, Exercise 2.6]). The target is
`Turing.exists_replayCanonizer` (`TCSlib/Complexity/TuringMachine/NDCodeSimulator.lean`): per
effective nondeterministic scheme, a finite machine computing, from a code, the serialization of
the decoded machine's replay machine. It was the last admission of the interpreter core
`Turing.exists_ndInterpreterCore` (#151) and of the universal NDTM
`Turing.exists_timed_universal_NDTM` (#154).

- **Provenance.** Megafill C's drafting agent drafted a fill brief for this target
  (`campaign/fills/c1/drafts/c1-fill-replaycanon.DRAFT.md`, with its pre-ship
  `drafts/c1-fill-replaycanon/preship-77f1eb4f/`). The maintainer's review of that draft
  (`campaign/fills/megafill/reviews/megafill-c-drafts/c1-cover/REVIEW.md`, F1) went further and
  proved the target on the draft's recommended definitions
  (`probe/C1RCReviewFeasibility.lean.txt`, sealed over 21 definitions there). **The user ruled
  (2026-10-24): land that proof directly**, by a maintainer PR with a fill gate and a replay; C1
  leaves megafill C. No fill brief was issued; the draft is the contract this landing is held to
  (its route, ground rules 10 and 11, and the house rules).
- **The landing:** PR #160 on `lean/c1-replaycanon` at `73c99430`, one commit on the campaign
  branch at `cbdb860c` (records only since #156's merge `21d53053`)
  (`campaign/fills/c1/evidence/c1-replaycanon-landing/c1-replaycanon.patch`):
  - in `NDCodeSimulator`, region (a) between the bridge `Turing.CodeNDTM.serialize_eq_tableBitsK`
    and the target: the review's declarations under `rc_` names, private, with docstrings and a
    proof sketch (`rc_table_eq`); some long lines rewrapped;
  - the target's body (the review's `rvc_target`), and an `**Implementation.**` paragraph after
    its frozen docstring;
  - the module's main-results entries: the canonizer and the core "(proved)";
  - `Diagonalization/NTimeHierarchy`'s **Status** paragraph: the universal NDTM is proved (text
    only; it was already stale, calling the core sorried).

## What changed (verify)

| Class | Declarations |
|---|---|
| **Target proved** | `Turing.exists_replayCanonizer`, with no `sorryAx`; its statement byte-identical; its docstring the frozen text plus the `**Implementation.**` paragraph |
| **Privates** | 22 → 49: 27 new (`rc_widen`, `rc_round`, `rc_table`, `rc_g`, `RcT`, `rc_body`, and 21 lemmas); none changed or removed |
| **Frozen** | 3 → 3 public declarations; every other public statement and docstring; imports unchanged |
| **Text** | the target's `**Implementation.**` paragraph; `NDCodeSimulator`'s main-results entries and its "Main definitions" sentence; `NTimeHierarchy`'s status paragraph |

## Brief for the auditor

1. **Faithfulness.** Does the proof establish the frozen statement? The correctness lemma is
   `rc_g_serialize`: `rc_g M.serialize = serializeK M.tm.replayTM` for every `M : CodeNDTM`.
   Check that `rc_g` (keep the header; locate the `true` table after `27 (n + 1)` records; `27
   (n + 1)` lockstep rounds; the bit-level widening `rc_widen`) matches the published layouts:
   `Turing.serializeK`, `Turing.tableBitsK`, `Turing.actionBitsK`, `Turing.workReadsK`,
   `Turing.NDTM.replayTM` (the choice read innermost, a blank selecting `false`). Check `n = 0`,
   and that `rc_g`'s values off serializations (its `[]` branches) are never needed.
2. **The composition.** `Turing.codePrim_machine` compiles `rc_g`; its bound is made monotone by
   `fun n => (Finset.range (n + 1)).sup TG` through `Turing.FinTM.computesFunInTime_iff` and
   `ComputesInTime.mono`; `Turing.FinTM.computesFunInTime_comp` composes it with the scheme's
   canonizer (`EffectiveNDMachineCode.canonizer_computes`). Exact?
3. **Primitive recursiveness.** `rc_widen_primrec`, `rc_body_primrec`, `rc_round_primrec`,
   `rc_table_primrec`, `rc_g_primrec`, from Mathlib's combinators and `MathlibBridge`'s blocks
   (`codePrimPrefix`, `codePrimDrop`, `codePrimSkipActionK`, `codePrimRepeat`, `codePrimUnary`,
   `codePrimBitsNat`, `codePrimPair`). Is each `of_eq` step's closing `rfl` a reduction of this
   file's definitions and of core/Mathlib only?
4. **Rule 10** (the scope of 2026-10-23: it binds TCSlib's own definitions; core and Mathlib
   definitions may reduce in `rfl`/`decide`/`show` but are never passed to `simp`/`rw`/`unfold`).
   The seal on the integrated file (`NDCSSeal.lean.txt`/`.out`): a section around region (a) and
   the target with `FinTM.ComputesFunInTime`, `FinTM.ComputesInTime`,
   `MultiTapeTM.ComputesInTimeAndSpace`, `serializeK`, `NDTM.replayTM`, `NDTM.fixChoice`,
   `CodeNDTM.serialize`, `tableBitsK`, `workReadsK`, `actionBitsK`, `signBits`, `optOptBoolBits`,
   `pairEncode`, `unaryFin`, `optBoolBits`, `optStateBits`, `codeSkipActionK`, `codeSkipRepeat`,
   `codeReadUnary`, `pairDecode` and `codeBitsNat` locally irreducible; the proof elaborates, and
   the only errors are the 22 controls at its top (lines 89–166), which close unsealed
   (`NDCSControl.*`). Inspect every `rw`, `simp`, `unfold` and `exact` argument: the review's
   inspection table (`probe/C1RCReviewFeasibility.inspection.tsv`) found theorems and this file's
   definitions only. Is the seal complete for what the proof reaches? **Rule 11:** no R3 row, no
   other file's private.
5. **Duplication.** ⟨SCREEN⟩ Is any new private a re-derivation of a published lemma (record
   splitting, `serializeK`/`tableBitsK` field lemmas, `Primrec` list helpers)?
6. **The text.** The docstrings, the proof sketch, the `**Implementation.**` paragraph and the two
   status texts: accurate, and public-facing (no campaign labels, paths or dates in Lean text)?
   Does the paragraph describe the refinement of the frozen sketch correctly (records widened at
   the bit level rather than decoded, equal by `rc_widen_record`)?

## Repository-side attestations (verify or challenge)

- **Elaboration** (against `oleans-lphl2`, the campaign's tree after #156): `NDCodeSimulator` with
  no diagnostic at all (the base had the target's sorry warning); `NTimeHierarchy` with only
  `Complexity.ntime_hierarchy`'s sorry warning, as at the base
  (`campaign/fills/c1/evidence/c1-replaycanon-landing/`).
- **Axioms** (the module with `#print axioms` appended): `exists_replayCanonizer`,
  `exists_ndInterpreterCore` and the bridge on `[propext, Classical.choice, Quot.sound]`
  (`NDCSAx.out`). The universal NDTM's chain is re-walked on the replayed snapshot.
- **Freeze:** `freeze-NDCodeSimulator.txt` (3 → 3 public, 22 → 49 private, only the target's body
  changed among existing declarations); the target's statement byte-identical.
- **Lint:** `TuringMachine` 0 FAIL, 68 WARN over 83 files; `Diagonalization` 0 FAIL, 2 WARN, both
  as at the base; no added line over 100 characters.
- **Replay:** `replay-lrcan.sh`, the two changed files' downstream closure (4 modules:
  `NDCodeSimulator`, `Diagonalization/NTimeHierarchy`, the `Diagonalization` and `TuringMachine`
  facades) at `73c99430`, chained from `oleans-lphl2`. **Pending:** as for gates 64–71, this gate
  is dispatched before the replay; the PR is clear to merge only when both have passed.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/72-c1-replaycanon-fill/findings.md`. The gate closes when it has zero blockers and
zero majors.

**Deliver your findings as a downloadable Markdown file named `c1-replaycanon-fill-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
