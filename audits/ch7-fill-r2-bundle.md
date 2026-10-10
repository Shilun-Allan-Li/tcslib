# External audit pack — Chapter 7 fill gate, round 2: the duplication question

**Audited surface:** the Chapter 7 fill surface on the **merged tree**, branch
`complexity/arora-barak-ch3-4` of `https://github.com/Shilun-Allan-Li/tcslib`,
at the commit named in the dispatch. It comprises:

- `TuringMachine/Build/EmitIterEmbed.lean` and `Build/EmitIterBody.lean`;
- `ClassNP/PolyTimeBlockLoop.lean`, `PolyTimeBlockTests.lean` and
  `PolyTimeBlockMajority.lean`;
- the three block headlines `mem_P_of_blockAny`, `mem_P_of_blockMajority` and
  `mem_P_of_blockXorAny` in `ClassNP/PClosure.lean`.

Record findings in `audits/ch7-fill-r2-findings.md`. **The gate closes on zero
blockers and zero majors.**

## Why a second round

Round 1 (`audits/ch7-fill-findings.md`, attached) returned 0 blockers, 0
majors, 2 minors and 2 notes. It ran on the bundle from Aparna's fork
(`00be8b1d…`, sources at `a-gupte/tcslib@0c22ae33`), not on this repository's
merged-tree adaptation. That adaptation added a duplication question, which
round 1 therefore never answered. **This round asks only that question, plus
a check of the round-1 sweep.** Questions 1–6 are not reopened. Their
transfer to the merged tree rests on the attestation below; challenge it if
it does not hold.

## Questions

1. **Duplication** (`audits/TEMPLATE.md` failure mode 5, attached). Screen the
   surface for duplicated proved material, and verify the maintainer's
   pre-screen (`audits/evidence/ch7/ch7-fill-duplication-screen.md`, its
   script, and the re-run at this commit, all attached).
   - **What the pre-screen reports.** No copies of pre-existing repository
     material. One family of renamed re-proofs inside the stack: the OR, XOR
     and majority loops each carry their own copy of the same orbit, length
     and init lemmas. That puts `PolyTimeBlockMajority` at 4 of 14
     declarations (28.6%), over the one-fifth threshold.
   - **How to report.** Report each confirmed copy family at **major**, with
     the proposed fix "human acknowledgment required"; the gate may not close
     over it until the human maintainer accepts the debt and names its
     resolution.
   - **The family above is already acknowledged** (the human maintainer,
     2026-10-10: it is resolved in the 12.2c refactor as one generic lemma
     set, with statements unchanged; `audits/duplication-ledger.md`,
     `backlog.md` CH7-D1). Confirm its extent. It then does not hold the
     gate, though any further family you find does.
   - **Coverage.** Say whether the screen missed any copy, including
     re-derivations it cannot detect: the screen matches contiguous text,
     exact or consistently renamed, and does not see restructured proofs.
   - **Classification.** Judge the screen's mirror pairs (Class B) and its
     two borderline cases.
2. **The EmitIter layer against §12, as facts.** Compare the public
   `EmitIterEmbed` embedding layer (`SafeRun`, `padAction`, `embedCfg`,
   `embed_step`, `embed_run`) with the §12 layer `Build/Embed.lean`
   (attached). Report what each states that the other does not, for example:
   - state injection;
   - padding-tape contents;
   - relocation along an arbitrary tape embedding;
   - emission handling;
   - first-return and avoidance clauses.

   Do not propose a merge. It is already scheduled as 12.2c item 6, and your
   facts will scope it.
3. **The round-1 sweep.** Verify that `audits/evidence/ch7/ch7-fill-r1-minor-sweep.diff`
   is comment-only and accurate:
   - finding 1's corrected XOR bullet;
   - finding 2's corrected *Main results* and "control steps" bullet;
   - note 3's paragraph in `PClosure`'s "Block-query closure" section.

   Check that the paragraph describes the three headlines' behaviour on
   malformed words exactly, nested pairs included, and that no new text
   misstates anything.

## Repository-side attestations (verify or challenge)

- **Transfer** (`audits/logs/ch7-fill-r2-transfer.log`). Of the nine Lean
  files round 1 audited, six are byte-identical here to `0c22ae33`.
  `EmitIterEmbed`, `PolyTimeBlockLoop` and `PClosure` differ in comments only
  (comment- and whitespace-stripped identical): the P0 finding-5 docstrings
  and the round-1 sweep.
- **Screen re-run** (`audits/evidence/ch7/ch7-fill-duplication-screen-rerun.txt`).
  The unmodified script at this commit screens 112 declarations against 562
  files, one more file than the recorded run (the new `Build/CounterLoop.lean`).
  All 24 overlaps of at least 50% it reports (3 exact, 21 renamed) are among
  those the recorded classification lists, and none is new, so the
  classification is unchanged.
- **Re-check after the sweep** (`audits/logs/ch7-fill-r2-docfix-sweep.log`).
  The seven-module chain from `Build/EmitIterEmbed` to
  `Randomized/PolyTimeModel` re-checks with 0 errors and 0 sorry warnings.
  Lint reports 0 FAIL in `ClassNP` and `TuringMachine/Build`.
- **Earlier evidence carried from round 1:** the merged-tree sweep, 23/23
  (`audits/logs/ch7-fill-merged-sweep.log`), and the 36 axiom prints.

## Brief for the auditor

This round is narrow. Answer the three questions with evidence, in the
standard findings table (blocker / major / minor / note). Justify an empty
table with the screen facts you verified and any non-mechanical comparison
you made.

## ===== audits/TEMPLATE.md =====

# External audit pack — TEMPLATE

Copy this file to `audits/phaseN-pack.md`, fill every `⟨…⟩`, and hand the result (plus
the listed attachments) to an external LLM from a different vendor, in a fresh context
with no access to this repository's development history. Record the findings in
`audits/phaseN-findings.md`. A phase's findings must be addressed (fixed, or explicitly
waived with a reason) before the next phase begins.

---

## Brief for the auditor

You are auditing the **trusted surface** of a Lean 4 formalization: definitions, theorem
statements, and remaining `sorry`s. The proofs that exist are machine-checked — do not
review tactic scripts for correctness. The failure modes you are hunting are:

1. **Infidelity** — a definition that does not mean what the cited source means.
2. **Trivialization** — a definition or statement satisfiable for degenerate reasons
   (vacuous hypotheses, a class that collapses, an encoding that makes a theorem empty).
3. **Unprovability** — a `sorry`d statement that is false as stated, or whose stated
   form is subtly weaker/stronger than intended (boundary cases: empty input, `n = 0`,
   `k = 0` tapes, constant absorption).
4. **Missing hypotheses** — especially finiteness, positivity, and well-formedness side
   conditions the informal source leaves implicit.
5. **Debt** — wholesale duplication of existing proved material (private copies of
   another file's declarations, re-derivations of registry routines), even when
   disclosed and mechanically forced by file ownership. Report it at **major** with
   the proposed fix "human acknowledgment required": it does not block the gate on
   soundness, but the gate must not close without the human maintainer explicitly
   accepting the debt and naming its scheduled resolution. Screen for it
   cumulatively — verify the pack's duplication ledger (per-file copied-material
   totals) rather than assessing each copy in isolation.

   **Accounting inside an acknowledged family is a minor.** Once the human
   maintainer has acknowledged a debt family and named its resolution, a later
   correction to that family's *accounting* is reported at **minor**, not major.
   Examples are a missed member, a miscounted span, or an imprecise description of
   the screen. Such a correction does not change what was approved. It is a
   **major** again only if it changes the approval itself: the correction pushes a
   further file past the one-fifth threshold, reveals copies outside the
   acknowledged family's named scope, or shows the named resolution cannot work.

For **every definition** in scope: restate it in your own mathematical English *without
looking at the docstring first*, then compare your restatement against the cited source
location, and report any daylight. For **every `sorry`d theorem**: argue in 2-5 sentences
why it is true as literally stated, or exhibit the problem (ideally a concrete
counterexample or degenerate instance). Attempt at least ⟨3⟩ *adversarial
instantiations* — concrete pathological objects plugged into the definitions to check
they behave as the theory intends. Propose any machine-checkable sanity theorems you
believe are missing.

Do not give a blanket approval. Your deliverable is the findings table; an empty table
must be accompanied by the per-definition restatements that justify it.

## Scope

| Item | Where |
|---|---|
| Lean files under audit | ⟨list of files, with line ranges if partial⟩ |
| Source text | ⟨book/paper, edition, page/theorem numbers — auditor must have it at hand⟩ |
| Plan/context documents | `AroraBarakChapter1Plan.md`, `policy.md` §2-3 ⟨adjust⟩ |
| Out of scope | tactic proofs; vendored files' upstream design ⟨adjust⟩ |

## Known deviations (declared by the authors — verify they are benign, flag any others)

⟨Bulleted list: every deviation the docstrings declare, one line each.⟩

## Specific questions for this phase

⟨Numbered list of the doubts the authors actually have. Be concrete.⟩

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide: **blocker** = a downstream phase would build on a wrong statement;
**major** = statement is fixable but materially misleading as is, **or** accumulated
debt (failure mode 5) that the gate may not close over without explicit human
acknowledgment (accounting corrections inside an already-acknowledged family are
minors; see failure mode 5); **minor** = edge case or naming/attribution defect; **note** =
observation, no change required.

## ===== audits/duplication-ledger.md =====

# Cumulative duplication ledger

The standing per-file accounting of copied proved material that
`workflow.md` §4 requires at every epoch boundary. Created as the
retrofit-R1 round-1 repair (R1-2); **rebuilt at round 2** (R2-1/R2-2 of
`audits/retrofit-r1-r2-findings.md`): the first version's arithmetic was
inconsistent (summands 261 against a printed 249), its inclusion rule was
applied asymmetrically, and it **misclassified an exact three-file copy
family as "design-harvest reimplementation"** — the round-2 auditor
proved the four relocation declarations byte-identical across `Loop`,
`Primitives`, and `Hardness` after consistent identifier substitution,
and found the 13 exact Loop-internal H3 copies omitted. This version
adopts one inclusion rule, enumerates every family, and uses the
auditor's independently computed figures wherever they exist.

## Counting convention (one rule)

**Primary rule — expanded correspondence membership**: a declaration is a
ledger member iff it belongs to a *recorded cross-declaration
correspondence* — the retrofit inventories' twin maps **including their
strengthened-counterpart rows**, the A2/F2A reports' declared copies, and
the round-2 audit's verified relocation and H3 families. Each member is
counted **once per file it inhabits**. (Secondary, where it differs: the
*strict normalized-byte-twin* count excludes the five strengthened
counterparts — Loop's `loopHost_prepare`/`loopHost_contracts`,
Primitives' `splitSolve_of_body`/`_source`/`_closed` — and H3's one
near-copy `_init` pair.) Fractions are members over the file's total
declarations. Line figures use the round-2 audit's span rule — attached
docstring and intervening closure note through the last code line,
excluding separating blank/module-note blocks — with the auditor's
computed values where available and estimates under the same rule marked
`≈`.

## State after retrofit epoch R1 (the merged PRs #9/#10)

| File | Total decls | Original-side members | Copy-side members | All members | Fraction | Lines in member blocks |
|---|---:|---:|---:|---:|---:|---:|
| `Build/Loop.lean` | 212 | 87 →Catalog (of the historical 95; strict 85) + 4 relocation originals (`emCallAction`/`emCallCfg`/`emCall_apply`/`emCall_relocate_run`, the batch-L source of the three-file family) | 13 H3 exact copies (`emLoopHost_*`; their `loopHost_*` originals are already in the 87 and are not double-counted; the `_init` and `_anchor_return` near-copies are counted as source-side members since round 7 — Catalog twins reproduce them cross-file) | **98** after RB4 (merged, PR #13 `b2833d46`; was 117 — generated, pass 4): 88 historical + 10 from pairs. RB4 deleted 12 H3 copies, the 4 relocation originals and `emLoopHost_init`; `emLoopHost_anchor_return` and `emLoopHost_start` no longer reproduce a Catalog proof after the agreement-transfer rewrite | **49.2%** (98/199) | **2,647** (was 3,153; both totals from the script's span routine, which reproduces the audited 3,153) |
| `Build/Primitives.lean` | 272 | 146 →Catalog (of the historical 150; strict 143) + **6 public originals** reproduced in Catalog (round-5 screen: `computesFunInTime_stripLast` → the adaptation `f2_strip_linear`; `_prepend`, `_pairEncodeFixed`, `_pairFst`, `_pairSnd`, `_pairConcat` → their strengthened `_spaceUsed` counterparts) | 4 relocation copies (`emitterP2Action`/`emitterP2Cfg`/`emitterP2_apply`/`emitterP2_relocate_run` — **byte-identical to Loop's after identifier substitution**, round-2 verified) | **173** — generated (pass 4): 150 historical + 23 sources of like-kind MEMBER pairs (the 6 round-5 publics, round-6 `emitterP2_control`, and 16 found by the complete round-7 pass: `emitterAppend_run`, `emitterP2EraseTM`, `emitterP2StateDecidableEq`, `emitterP2_erase_scan`, `emitterP2_prepare_rewind_candidate`/`_suffix`, `emitterSplit_find`/`_loop_bound`/`_of_body`/`_result`, `emitterTokenTM`, `emitterToken_double`/`_separator`, `emitter_first_entry`, `mapCfg`, `mapStart`) | **63.6%** | **3,790** (3,415 + 375 round 7) |
| `CookLevin/Hardness.lean` | 549 | 0 | 4 relocation copies (`clSlotAction`/`clSlotCfg`/`clSlot_apply`/`clSlot_run` — likewise byte-identical) | **4** | **0.73%** | 73 |
| `Build/Catalog.lean` | 423 | 2 in-file originals (`f2_finSumEquiv`, `f2_sum_add` — their `a2_` copies are normalized-identical, round-3 verified) | 150 Primitives-sourced + 95 Loop-sourced + 17 Wrappers-sourced (10 `f2_timed*`, 7 `catalog_redirect*`) + 2 in-file `a2_` copies + **3 Composition-sourced** (`f2_idTM`, `f2_idTM_run`, `f2_constTM` — maintainer-reconciled normalized-identical to `Composition.lean`'s originals) + **20 counter-block members** (`f2_counterInc` … `f2_counter_computes` — maintainer reconciliation, declaration by declaration: **19 normalized-identical** to `ClassP/TimeConstructible.lean`'s originals, and `f2_counter_computes` a **near-copy adaptation** of the proof body of the public `timeConstructible_id`) + **7 strengthened public counterparts** whose time conjuncts reproduce a public source proof (`computesFunInTime_id_spaceUsed`/`_const_spaceUsed` ← `Composition.lean`, round 4; `_prepend`/`_pairEncodeFixed`/`_pairFst`/`_pairSnd`/`_pairConcat_spaceUsed` ← `Build/Primitives.lean`, round 5 — 89-100% of each source proof reproduced) + **2 F2A adaptations** of public proofs (`f2_strip_linear` ← `computesFunInTime_stripLast`, 86% of the source reproduced — round-5 finding R5-1; `f2_counter_heads` ← `timeConstructible_id`, 64% — round-5 screen) + **20 round-6 members** from the exhaustive screen: R6-1's `f2_counter_count_space` (80.3% of the private `counter_count`) and 19 further cross-file adaptations — 4 F2A (`f2_exists_loopFind_space` 97.8% of `exists_loopFindTM`, `f2_cond_time` 92.0% of Wrappers' `computesFunInTime_cond`, `f2_rewind_heads` 90.8% of `catalogRewind`, `f2_cond_ledger` 70.3% of `timed_start`), 13 A2 (`a2_map_block`/`_suffix`/`_backA`/`_backB`/`_parse`/`_setup`, `a2_mapVirtual_run`, `a2_mapSetup_stationary`/`_run`/`_heads`, `a2_call_run`, `a2_loop_prepare` 86.8% of `loopHost_prepare`, `a2_loop_round`), and 2 public rows (`computesFunInTime_pairLenCheck_spaceUsed` 71.4% of `computesFunInTime_pairFst`; `exists_loopTM_spaceUsed` 85.5% of `exists_loopCfgTM`, 81.0% of `exists_loopTM`) | **318** | **75.2%** (strict — excluding the 34 strengthened counterparts/adaptations and the 1 near-copy: **283, 66.9%**, unchanged) | **7,539** (6,267 round-4 measured + 224 round 5 + 52 R6-1 + 996 for the 19) |
| `Build/Wrappers.lean` | 29 (10 pub + 19 priv) | 17 + 1 round-6 source (the public `computesFunInTime_cond`) | 0 | **19** — generated (pass 4): 17 historical + `computesFunInTime_cond` (round 6) + `captureCfg` (round 7) | **65.5%** | **355** (297 + 40 + 18) |
| `ClassP/TimeConstructible.lean` | 21 | 20 (the 19 identical counter originals + `timeConstructible_id`, the source of both the near-copy `f2_counter_computes` and the adaptation `f2_counter_heads`; the private `counter_count` is likewise the source of R6-1's `f2_counter_count_space`) | 0 | **20** | **95.2%** (strict: 19, 90.5%) | 355 (round-4 measured) |
| `TuringMachine/Composition.lean` | 19 | 5 (`idTM`, `idTM_run`, `constTM` + the public `computesFunInTime_id`, `computesFunInTime_const` whose proofs the Catalog rows reproduce) | 0 | **6** — generated (pass 4): + `controlCfg_run` (R7-1) | **31.6%** (strict: 3, 15.8%) | **109** (97 + 12) |
| `Build/Embed.lean`, `Build/Seam.lean`, `Build/VirtualInput.lean`, `Build/Zone.lean`, `Simulation.lean` | — | 0 | 0 | 0 | 0% | 0 |
| `Codes2Tape.lean` (ZF-B/B2/B3, integrated 2026-10-10) | 49 (9 pub + 40 priv; B3 added 16 new, non-copy privates) | 0 | **23 format-specific adaptations** of `CodeParser.lean`'s / `MathlibBridge.lean`'s one-tape top layer (20 retargeted + `zfBParse_full`/`zfBCanonical`/`zfBCanonical_eq`; agent-measured 60–100% body share) — the 46 format-independent copies were deleted after the promotion (f171767f) | **23** | **46.9%** (strict 3, 6.1%) | 290 code lines (agent-measured) — over one fifth: `backlog.md` §1 CH34-D2, **ACKNOWLEDGED (user, 2026-10-10) → 12.2c tasklist item 8** |
| `Robustness/SingleTape.lean` (ZF-C2) | 100 | 0 | 0 — **3 in-file near-duplicates noted, uncounted** per the in-file convention (maintainer screen: `dgPos_move` 93.1% of `sweepPos_move`, `dgStart` 72.9% of `sweepStart`, `dgInput_read` 64.3% of `sweepInput_read`; the agent disclosed the first and third as borderline) | 0 | 0% | 0 |

**Reconciliation notes (rounds 3-4 repairs)**: the F2A report's 306
inventory entries decompose as **150 Primitives + 94 Loop + 10 Wrappers +
3 Composition copies + 20 counter members + 2 in-file originals + 7
adaptations (`f2_strip_linear`, `f2_counter_heads`, round 5;
`f2_counter_count_space`, `f2_exists_loopFind_space`, `f2_cond_time`,
`f2_rewind_heads`, `f2_cond_ledger`, round 6) + 20 nonmembers** (the
round-4 correction: the old "29 outside" wrongly included the two counted
in-file originals); the 20 share no member-level material with any
declaration of the five source files (round-6 exhaustive screen below) (the `f2_polyHeads`/`f2_space_of_time`/
`f2_segment_heads`-class engines and strengthenings — round-4 sampled and
accepted). The A2 report's 45 declarations contribute 2 in-file copies +
`a2_loop_halted_run` (in the Loop 95) + **13 cross-file adaptations**
(round-6 screen) + 29 new constructions. Catalog's union:
`318 = 286 F2A + 16 A2 + 7 earlier redirect + 9 public counterparts`.

**The public-proof screen (round-5 repair of R4-1; R5-1/R5-2/R5-3).**
Published as `audits/evidence/retrofit/r1-public-proof-screen.py` with its
output `r1-public-proof-screen.out`. *Erratum:* the round-4 run tested
whether a source proof was contained **whole** in its counterpart, but the
round-4 text described "segments ≥ 60 characters". The round-5 auditor ran
the method as described and found six fragment hits that the containment
test could not see. The method below is the one actually run.

- **Method.** Strip comments and all whitespace. Rename each source
  identifier `h` to `f2_h` wherever Catalog declares `f2_h` (dotted names
  split). Report two measures:
  - the **longest common contiguous segment** (LCS), with the literal ≥ 60
    candidate threshold;
  - the **shared length**: greedy string tiling with blocks of at least 25
    characters, as a fraction of the **source** proof.
- **Rule.** A pair is a **member** when at least half of the source proof
  reappears in the target, with an absolute floor of 60 shared characters
  so that a one-line citation of a public lemma counts as reuse. Any other
  shared tiling of at least 60 characters is a recorded **fragment**, not
  counted. The rest are citations or no match.
- **Population (R5-3).** 17 eligible pairs: 2 from Composition (`id`,
  `const`) and **15** from Primitives, not the 16 stated in round 4. Five
  source theorems have no `_spaceUsed` counterpart: `ifEq`, `comp`,
  `splitSolveWith`, `unaryToken`, `appendBit`.
- **Pass 1, direct pairs.**
  - Members (7): `id` 96.5%, `const` 97.1%, `prepend` 93.9%,
    `pairEncodeFixed` 100%, `pairFst`/`pairSnd` 88.8%, `pairConcat`
    88.7%.
  - Fragments, recorded and not counted (3): `polyUnary` (119 characters
    shared, 46.7%); `pairLenCheck` (305, 21.9%; its LCS is the 91-character
    `Nat.pow_one` bound); `stripLast` (221, 11.7%; its LCS is the
    121-character `have hn` weakening).
  - Citations or no match (7): `lengthBits`, `polyBits`, `pairValid`,
    `pairDup`, `pairMapSnd`, `splitSolve` (the auditor's 27-character
    citation), `incFixed`.
  - The literal ≥ 60 LCS screen reproduces the auditor's hit set exactly
    (`id` 776, `const` 273, and 62/75/75/75/91/121 for the six Primitives
    pairs). One member falls below the 60-character LCS threshold:
    `pairEncodeFixed`, whose longest block is 53 characters but whose whole
    91-character source proof reappears. This is why the rule measures
    coverage, not contiguity alone.
- **Pass 2, residual helpers.** Each of the 27 nonmembers recorded in
  round 4 is screened against every public proof of Composition,
  Primitives and TimeConstructible, taking the best match by shared length.
  - Members (2): `f2_strip_linear` (86.0% of `computesFunInTime_stripLast`;
    R5-1) and `f2_counter_heads` (64.1% of `timeConstructible_id`; the
    auditor's 215-character partial-reuse candidate, which crosses the
    member bar once measured by tiling).
  - Fragments, recorded (6): `f2_counter_count_space` 6.5%,
    `f2_unary_sharp` 35.7%, `f2_cond_time` 30.0% (vs
    `bufferedCompTM_computesInTime`, a candidate the auditor did not list),
    `f2_rewind_scan_heads` 7.4%, `f2_rewind_heads` 6.0%,
    `f2_cond_ledger` 11.7%.
  - The remaining 19 share under 60 characters with any public proof.
- **Round-6 repair (R6-1, R6-5): pass 3, exhaustive.** Round 6 found
  R6-1, which the public-only residual pass could not see. Pass 3 replaces
  that scope limit. **Every one of Catalog's 124 non-members** (all of
  Catalog minus the post-R6-1 299-member union, computed by name in the
  script) is screened against **every declaration, public and private, of
  Composition, Primitives, TimeConstructible, Loop and Wrappers** (553
  declarations, of which 542 have an extracted body of at least 25
  characters; the other 11 cannot reach the 60-character floor). An exact 25-character prefilter is used; it loses nothing,
  because every tile is at least 25 characters. Verdicts compare like with
  like, proof with proof and term with term, so a proof that spells out a
  definition's term is reported as a restatement and not counted. **Every**
  qualifying pair is printed, not just each target's best match (R6-5).
  - Result: **19 cross-file members**, all counted in the Catalog row
    above. *Round-7 correction:* the round-6 text derived the source side
    from each target's best match only, giving "6 new source-side members"
    (R7-1). Pass 4 below replaces that hand step.
  - Five A2 members reproduce just over half of one 129-character Loop
    proof, `emLoop_run_prefix`. They are counted, as the rule requires,
    and flagged as low-coverage.
- **Round-7 repair (R7-1, R7-2): pass 4 generates the census.** No
  per-file member count is assembled by hand any more. **Pass 4** runs the
  like-kind rule over **all 423 Catalog declarations**, not only the
  non-members, against all five source files: 537 like-kind MEMBER pairs.
  **Every** pair's source joins its file's member set, together with the
  historical rules, stated by name in the script: f2_-twins, the
  `a2_loop_halted_run` twin, the relocation family, the 13 H3 copies, the
  counter block and `catalog_` twins. The script prints each file's count
  and every member beyond the historical rules, with spans. The rows above
  quote it.
  - Pass 4 reproduces the auditor's R7-1 additions (`controlCfg_run`,
    `emCall_right_run`, `exists_emitLoopTM`).
  - It also finds **24 further source-side members** (Primitives 16, Loop
    7, Wrappers 1). These are source declarations that a Catalog twin of a
    *sibling* declaration reproduces by more than half, so their material
    is duplicated in Catalog. Two of them are Loop's H3 near-copies
    `emLoopHost_init` and `emLoopHost_anchor_return`, previously
    "noted, uncounted"; they are now counted through the cross-file path.
  - Catalog is unchanged at 318.
  - **R7-2:** the body extractor now handles equation-style definitions and
    inductives (text from the first depth-0 `|` or `where`). The population
    labels are exact: 553 source declarations, 542 with an extracted body
    of at least 25 characters; the other 11 are genuinely shorter. Pass 3b
    carries the kind guard: **107 like-kind in-file pairs over 62 targets
    (12 at 90% or more), plus 2 restatements** (`f2_cond_ledger` ~
    `f2_timedReadyCfg`, `a2_loop_prepare` ~ `f2_loopReady`).
- **The membership rule in one sentence.** A declaration is a member when
  it is a historical twin or copy, or when it is either side of a
  like-kind cross-file pair in which at least half of the source's
  extracted body, and at least 60 characters, reappears in the target. The
  **exception** is in-file near-duplicates, which are recorded (pass 3b)
  and not counted; in-file exact copies are counted.
- **Standing in-file convention, stated explicitly.** Pass 3b lists
  in-file near-duplicates among the non-members: **109 raw printed
  pairs, of which 107 are like-kind, over 62 targets**. Twelve like-kind
  pairs reach 90%, and the other 2 are kind-mismatched restatements. They
  are led by the §12 sibling
  machine rows (`transferTM` against `copyTM` 99.8%, and the
  clear/compare/increment rows), which are public constructions audited at
  the §12 and F1 gates. Per the ledger's standing convention, which counts
  in-file **exact** copies (the H3 thirteen, the `a2_mapSumEquiv`/
  `a2_map_sum` pair) and **notes in-file near-duplicates without counting
  them**, they are recorded, not counted. None is an exact copy. Their
  disposition is the 12.2c per-theme split, which factors these families.
  An in-file near-match alone never adds a member. A declaration can still
  be a member independently through a cross-file pair: Loop's
  `emLoopHost_init` and `emLoopHost_anchor_return` count because their
  Catalog twins reproduce them.
- **Coverage qualification.** The screen covers the five source files of
  Catalog's copy families, in full, at the stated thresholds. Copies from
  files outside those families, or adaptations restructured below the
  25-character tile size, are outside it.

Copy-side counts deliberately include copies whose originals were deleted
in R1 (the copies persist; deletion of an original does not shrink the
copy side). The Loop inventory's recorded dispositions — the 8 dead
Loop-twin copies in Catalog (`f2_loop_silent_prefix`,
`f2_loopBody_capture`, the six `f2_loopDebit*`/`f2_loopBorrow*`) and the
orphans' dead twins — are **dispositions for 12.2c, not subtractions
here**; sole-owner/dead labels require Catalog's reference graph and are
settled at that window. Internal near-duplicates flagged by the
inventories but outside the rule (`clCountTape ≡ bufferTape`) are noted,
uncounted. The H3 `_init` pair, once in this list, counts since round 7
through its cross-file Catalog correspondence.

**Epoch R1 delta**: new copies **0**; the historical maps lost **eleven
dead originals plus one live original eliminated by replacement**
(`catalogPair_inverse`, the human-approved E1) — 245 → 233 surviving
→Catalog originals (R2-3 wording); net −1,639 lines, −83 private
declarations (76 dead + 7 replaced).

## Watch items (design-parallel, no byte-copies)

| Item | Status |
|---|---|
| **ch7 EmitIter layer vs the §12 layer** (merged with PR #11, 2026-10-10): `Build/EmitIterEmbed.lean` exports a **public** tape-padding, state-injecting embedding layer (`padAction`/`embedCfg`/`embed_step`/`embed_run`/`SafeRun` — 18 public declarations, none private; *corrected 2026-10-10: the first version of this row called them private*), written against main (which lacks `Build/Embed.lean`) and structurally parallel to the §12 bank-embedding transformers; the emit-iteration host (`Build/EmitIterBody.lean`, 1 public, 17 private) parallels the §12/Loop host family. **Body-level screen** (`audits/evidence/ch7/ch7-fill-duplication-screen.md`; the first version of this row rested on a name screen alone): **no copies of pre-existing repository material** — none of the §12 or loop-library material matches; the ch7 modules consume main's public `exists_emitLoopTM`/`exists_emitCallTM`/`exists_installCallTM` rows by citation. This row is design duplication; the stack's own copy family is ledgered below. | **12.2c docket** (user, 2026-10-10): harmonize to one embedding layer and one host family at the per-theme split; the naming of the shared block primitive is settled there too. The ch7 fill gate (`audits/ch7-fill-pack.md`, run on the merged tree; question 7) compares the two layers as facts. Consumption embargo until that gate closes. |

## Acknowledgment and disposition state

| Debt family | Acknowledgment | Cleanup owner and window |
|---|---|---|
| Catalog's 318 expanded members (↔ Primitives/Loop/Wrappers/Composition/TimeConstructible + in-file) | **D-R2** (user, 2026-10-09) | the **12.2c** per-theme refactor, promoted to the next window after R1; precondition (shrunken `Build/` files) met |
| Loop's 13 H3 copies (+1 near-copy) | **D-R3** (user, 2026-10-09) commissioned the collapse mechanism — §13 Z5, **now proved** (vhost-f1) | **ACKNOWLEDGED (user, 2026-10-09): retrofit batch RB4** (Loop), consuming Z5, window: after the A-S1 fill gate closes — **RB4 merged (PR #13, 2026-10-10): 12 of 13 H3 copies deleted by Z5 transfer; `emLoopHost_prepare` survives with a rewritten proof, still counted.** The inlined residue is the row "RB4's inlined residue in Loop" below |
| The three-file relocation family (4 decls × 3 files; pre-policy legacy, disclosed at its batches as "private harvest" but verbatim in fact) | **the user, 2026-10-09** (the round-2 audit's R2-2 disposition) | **ACKNOWLEDGED (user, 2026-10-09): the same RB4** (all three files), replacing the family with the R1 selected-tape exports (D-R1, proved) + Z5 agreement transfer, per the inventories' own analysis of what unlocks it — **RB4 (2026-10-10): Loop's 4 originals DELETED** (R1 embedding + injective state transport + Z5). **Primitives' and Hardness's 4 + 4 copies REMAIN.** Their generic interfaces are stronger than R1 (aliased host slots, non-injective state maps), so a literal replacement would weaken surviving statements. Continuation: **RB5 (revision 2, 2026-10-10)** promotes `runFrom_mapState_of_agreeOn` into `Build/Embed.lean` (it needs both `StateRenaming` and Z5, and only Embed already imports both), then specializes per concrete layout, Primitives before Hardness |
| **RB4's inlined residue in Loop** (post-merge copy-text finding, 2026-10-10): the forwarding host's consumers reproduce the original loop host's phase proofs. `emLoopHost_round` reproduces 100% of `loopHost_reject`; `emLoopHost_prepare` 99% of `loopHost_prepare` and 100% of `loopHost_input_rewind`; `emLoopHost_anchor_return` 95%; `emLoopHost_start` 92%. The frame pairs `emCall_bank_*` (94%) and `emCall_finish_*` (79%) grew more alike. In all, 11,476 characters of the forwarding host reproduce the original (`audits/evidence/retrofit/copy-text-screen.py`) | **ACKNOWLEDGED (user, 2026-10-10)**: RB4 accepted as merged, and RB5's Loop task withdrawn. The residue is not removable phase by phase: the `loopHost_*` lemmas state endpoints only, and the anchor-return phase runs in body control from `t = 0`, exactly where the two hosts differ (RB5's first dispatch kernel-checked the counterexample) | the user's **12.2c**, tasklist item 11: unify the two hosts structurally |
| **ch7 block stack's per-loop lemma family** (PR #11, 2026-10-10): the OR/XOR/majority loops re-prove one orbit/length/init lemma set under renaming — 6 `private` members: `PolyTimeBlockMajority` **4/14 = 28.6% (85 lines), over one fifth**; `PolyTimeBlockTests` 2/25. Per-delivery ledger line: `audits/evidence/ch7/ch7-fill-duplication-screen.md` | **ACKNOWLEDGED (user, 2026-10-10)** — `backlog.md` §1 **CH7-D1**, opened under the one-fifth rule and answered | the **12.2c** per-theme refactor (the user's own window; colleagues spared deduplication work): one generic lemma set in `PolyTimeBlockLoop`, statements unchanged, coordinated with the ch7 owner, after the ch7 fill gate closes |
| **`Codes2Tape.lean`'s format-specific parse layer** (ZF-B/B2, 2026-10-10): 23/33 two-tape instances of `CodeParser.lean`'s one-tape top layer (69.7%; 3 strict) | **ACKNOWLEDGED (user, 2026-10-10)** — `backlog.md` §1 **CH34-D2** | the **12.2c** tasklist item 8: a format-parameterized parse layer (one-tape, two-tape, ND), statements unchanged |

Any new copy in a future delivery enters through the per-delivery ledger
and the one-fifth escalation rule of `workflow.md` §4.

## ===== backlog.md =====

# Backlog

The consolidated tracking file for the Arora-Barak campaign branch
(`complexity/arora-barak-ch1`) and adjacent repository work: human-review
design questions, queued and on-hold campaign work, deferred formalizations,
pending decisions, and housekeeping. Consolidated 2026-09-18 from the two
campaign plans, the audit resolutions records, and session assessments.

**Conventions.** This file is the *canonical home* of the human-review
question statements (§1) — the plans keep stable numbered stubs, since audit
documents cite the numbering — and the *tracking index* for everything else
(scope prose remains in the plans; decision-log history is never moved).
New items land here; an item leaves only by a decision recorded in the
relevant plan's decision log. From the next audit round onward this file
joins the bundle attachment set.

---

## 1. Human-review design questions (reserved — never closed by an automated gate)

Flagged for a **human** auditor/maintainer: the LLM audit rounds verify
correctness, but these are matters of architectural taste and trust-surface
policy.

### CH1-Q1 — the 3A Mathlib-computability bridge

*Origin: `AroraBarakChapter1Plan.md` §5 (epoch 3, batch A);
`MathlibBridge.lean`, `Turing.exists_effectiveMachineCode`.*

The audited docstring sketch called for the canonizer machine to be
**hand-assembled from this repository's composition combinators** ("its
construction uses the composition combinators", optionally with a polynomial
`canonizerTime`). The delivered proof instead (i) proves the canonization
*function* primitive recursive, (ii) compiles it through **Mathlib's verified
recursion-theory pipeline** (`ToPartrec.Code.exists_code` →
`PartrecToTM2.tr_eval`), (iii) simulates the resulting TM2 stack machine in
our model with a bespoke private `bridgeTM`, and (iv) lands in the binary
alphabet via the proved `alphabet_reduction`, extracting the time bound by
finite maxima (no polynomial bound claimed — permitted, since
`canonizerTime` is existential). The batch flagged the deviation itself; the
maintainer verification pass confirmed the proof is sorry-free with the
standard axiom footprint and zero public-interface drift. **Open questions
for a human:** (a) is the heavyweight `Mathlib.Computability.TMToPartrec`
import into the TM tree acceptable, or should the bridge be quarantined
behind the planned phase-5 `MathlibBridge` module boundary (it effectively
front-runs that module)? (b) is the enlarged trust/review surface (Mathlib's
TM2 semantics + the private `bridgeTM` simulation, ~150 private
declarations) preferable to a longer but self-contained combinator
construction? (c) should the abandoned polynomial-`canonizerTime` claim be
recorded as permanently out of scope, or re-derived later from the
combinator route if one is ever written? Since the epoch-3→4 merge the
bridge lives in the dedicated `MathlibBridge.lean`, which implements the
quarantine that part (a) contemplates — the `TMToPartrec` import is confined
to that one module and nothing outside `exists_effectiveMachineCode` depends
on it — but the implemented quarantine does **not** dispose of this
question: parts (a)-(c) remain open for human review (epoch-4 audit,
finding 3: an earlier version of this text misplaced the bridge inside
`Encoding.lean`).

*Cross-link: part (c) gained relevance in Chapter 2 — see §3, "Polynomial
canonizer for a concrete scheme".*

### CH1-Q2 — the 3B universal-interpreter proof architecture

*Origin: `AroraBarakChapter1Plan.md` §5 (epoch 3, batches B + B2);
`Universal.lean`, `Turing.universal`.*

The proof followed the audited sketch's outline (prefix-only startup,
canonizer capture onto a table tape, four-work-tape interpreter with a fixed
finite controller), but the realized architecture is by far the campaign's
most involved artifact: 2465 lines (2831 after the epoch-4A timed fill), 104
private declarations built across two agent sessions (WIP `f191b918` +
continuation), a bespoke checkpoint relation (`universalRelation`) with
generic block-simulation assembly (`universal_block_run` /
`universal_from_blocks`), a virtual left boundary via a marker tape, a unary
state tape with group-wise table scanning, and an *exact* per-phase cost
ledger realized to `universalBlockBound = 3L + 5N + 20`. The kernel checks
all of it, and the public statement is frozen and audited — but the *design*
was never itself an audit deliverable at this level of detail. **Open
questions for a human:** (a) is this the right load-bearing shape — and
which parts (the capture wrapper, the block-run/`universal_run_join`
assembly, the marker-directed rewind and unary-copy gadget patterns, all
flagged by the agents as promotion candidates) should graduate to shared
modules rather than being re-derived? (b) is the exact-ledger posture
(`3L + 5N + 20` proved to the transition) worth its brittleness against any
future change to `CodeTM.serialize`, or should the maintained invariant be
an existential bound with the exact ledger demoted to documentation? (c)
does the interpreter's claim to *be* the book's universal machine (as
opposed to satisfying the frozen statement, which the kernel settles)
deserve a targeted human read of the construction's core definitions
(`UniversalControl`, `universalInterpreter`, `universalRelation`), given no
executable diagnostics of the whole interpreter ever ran (the batch-B smoke
tests aborted on deep recursion and were discarded)?

*Cross-link: question (b)'s exact ledger is now also load-bearing for the
Chapter-2 `TMSAT_mem_NP` fill (the quantitative public bridge, §2), which
will expose a form of the constant publicly.*

### CH2-Q1 — generality of `HALT_not_mem_NP`

*Origin: `AroraBarakChapter2Plan.md` (phase-1, round-2 audit, finding 3);
`ClassNP/Reductions.lean`.*

The statement is currently at `Turing.EffectiveMachineCode` generality
because its proof route reuses Chapter 1's `HALT_not_computable`, whose own
proof runs the universal evaluator. The round-2 auditor showed this
restriction is **not mathematically necessary**: a direct diagonalization —
the public diagonal-pairing machine, the searcher's finite-control transform
with the halt/loop roles swapped, `Turing.exists_codeTM`, no evaluator —
proves `HALT` undecidable for *every* lawful `Turing.MachineCode` (and the
earlier "trivial-machine scheme" counterexample is unlawful: constant
decoding violates `decode_encode`). **The question:** add that diagonal
lemma as a new audited statement (a strengthening of Chapter 1's
uncomputability story that shares its main fill obligation, the
control-transform lemma, with `HALT_NPHard`) and generalize
`HALT_not_mem_NP` to `MachineCode` — or keep the conservative signature as a
documented API/proof-route restriction? Maintainer's provisional choice,
pending review: the conservative signature, with the docstring stating the
restriction honestly; the diagonal lemma is deliberately *not* slipped into
a repair round, since it would enlarge the audited surface of Chapter 1's
uncomputability chapter.

---

### CH7-D1 — the block stack's per-loop lemma family (duplication threshold crossed)

*Origin: the ch7 fill gate, run on the merged ch3-4 tree after PR #11
(`audits/ch7-fill-pack.md`, question 7); maintainer pre-screen
`audits/evidence/ch7/ch7-fill-duplication-screen.md`. This item is opened
under `workflow.md` §4, which leaves no discretion once a file passes one
fifth copied material.*

The OR, XOR and strict-majority block loops each re-prove the same orbit,
length and init lemmas under renaming. The proofs are identical up to the
step function's name, so a single lemma quantified over the step function
would serve all three. Six `private` members:

- four in `ClassNP/PolyTimeBlockMajority.lean`: **4 of its 14 declarations
  (28.6%, 85 lines), over the threshold**;
- two in `ClassNP/PolyTimeBlockTests.lean` (2 of 25).

No pre-existing repository material is copied. **The question:**
acknowledge the debt and name its owner and resolution window. The fill
gate's auditor is instructed to report the family at major ("human
acknowledgment required", `audits/TEMPLATE.md` failure mode 5), and the gate
cannot close until this is answered.

Maintainer's provisional proposal, pending review: the owner is the
Chapter-7 campaign (Aparna). The window is the post-gate cleanup her pack
already proposes for splitting the counting layer out of
`Randomized/Classes.lean`. The resolution is one generic orbit/length lemma
set in `PolyTimeBlockLoop.lean` consumed by all three loops, with statements
unchanged. The alternative is to fold it into 12.2c alongside the EmitIter
harmonization.

**Answered (user, 2026-10-10): fold into 12.2c.** The debt is acknowledged.
The owner is the user's own 12.2c per-theme refactor, not the ch7 campaign:
deduplication is being done there anyway, and colleagues are spared it. The
resolution is one generic lemma set with statements unchanged, coordinated
with the ch7 owner because the files are hers, and run after the ch7 fill
gate closes.

---

### CH34-D2 — `Codes2Tape.lean`'s format-specific parse layer (duplication threshold crossed)

*Origin: ZF-B/ZF-B2, integrated 2026-10-10
(`audits/zone-agent-reports/f1-B2-REPORT.md`). Opened under `workflow.md`
§4, which leaves no discretion past one fifth.*

After the promote-first step (f171767f) and ZF-B2's deletion of all 46
format-independent copies, **23 of `Codes2Tape.lean`'s 33 declarations
(69.7%; 3 strict twins)** remain two-tape instances of `CodeParser.lean`'s
and `MathlibBridge.lean`'s one-tape top layer: the record reader and table,
parse, decode, scan, canonize, and their laws. They cannot be cited across
formats. `NDCodes`'s pending `exists_effectiveNDMachineCode` will need the
same layer a third time. **The question:** acknowledge the debt and name
its owner and window. The maintainer's provisional assignment is 12.2c
docket item (iii), a format-parameterized parse layer serving all three
formats, with statements unchanged, under the user's standing preference.
It awaits the user's explicit confirmation; the A-S2 fill gate cannot close
over it until then.

**Answered (user, 2026-10-10): acknowledged**, and added to the 12.2c
tasklist (`AroraBarakChapters3-4Plan.md` §4d, item 8) as an explicit task.

---

## 2. Campaign work queued or on hold

* **Chapter-2 fill campaign (E1-E5)** — **active** (hold lifted
  2026-10-02 after the ch-6 integration and audit closed). All four
  statement-phase gates closed; 59 audited-true admissions.
  **Epoch/batch partition recorded** in `AroraBarakChapter2Plan.md` §4
  (fill-campaign subsection): E1 assemblies + poly-calculus + formula
  mathematics (batches 1A–1D, 28 targets), E2 enumerator + compilations +
  Ex 2.1/HALT + `TMSAT` (2A–2D, 11), E3 padding + SAT track + snapshot
  locality (3A–3D, 14), E4 the Cook-Levin summit + TAUTOLOGY dual (4A–4B,
  6), E5 closure. Padding moved E2 → E3 (recorded refinement);
  `EXP_subset_NEXP` 1C → 3A (recorded amendment). **E1 integrated 2026-10-02**
  (27/27 targets filled, nine agent commits, freeze audit clean, 32
  admissions remain, zero `sorryAx` across all fills); **epoch-1 gate CLOSED**
  2026-10-02, single round, 0 blockers/majors
  (`audits/ch2-epoch1-resolutions.md`); 27/59 proved, 32 remain.
  Deferred from E1: promotion of 1D's `foldr_max_le_of_forall` **and its
  companion `le_foldr_max_of_mem`** (auditor suggestion) to a shared list
  utility (disposition D3).
  **E2 briefs issued** 2026-10-02
  (`briefs/ch2-epoch2-batch{A,B,C,D}.md`; 10 targets + the mandated
  `timed_universal` bridge statement; inheritances embedded verbatim;
  hardened repo/branch headers; D1 axiom wording).
  **E2 checkpoints integrated 2026-10-03 — all four batches partial, epoch
  gate OPEN** (four Codex commits `da8bd091`…`4b4cd418` off `6c09453e`;
  maintainer verification clean — deleted-lines, surface, replay, fresh
  53-module sweep with 29 direct admissions, axiom-root traversal matching
  every REPORT; logs `audits/logs/ch2-e2-checkpoint-{sweep,axioms}.log`;
  decision-log row in the ch2 plan). 5 of 10 target bodies written;
  admission-free closure: `timeConstructible_poly` only. Uniform frontier:
  concrete machine construction/timed integration (147 helpers delivered,
  145 admission-free). Open sites: 2A's single `enumMachine_contracts`
  (closes `NP_subset_EXP` **and** both HALT targets), 2B's
  `choiceVerifier ∈ P` + untouched reverse direction, 2C's two verifier
  memberships (`CONTINUATION.md` shipped), 2D's `D-MEM`/`D-WRAP`/`D-EMIT`
  (+ the bridge escalation — **RESOLVED 2026-10-03**: Chapter 1 exports
  `Turing.timed_universal_concrete` and the TMSAT bridge is discharged
  via `tmsat_concrete_coefficient` + monotonicity; `TMSAT_mem_NP` now
  roots at `D-MEM` alone, tree admissions 46; decision-log rows in both
  plans). 2C also requests promotion of `prefixTM`/`fixedPair`
  fixed-prefixing lemmas (held with D3; subsumed by Build P3/P6 at the
  shared round).
  Next (sequencing per the frozen library design, 2026-10-03; spec
  layer and bridge export both landed 2026-10-03): the shared
  infrastructure audit pack (Build spec surface + the bridge export and
  its TMSAT discharge) → gate → library fills (harvest-adaptation
  batches; loop flagged for continuation budget) → E2 continuation
  briefs citing the library → epoch-2 audit.
* **Machine-construction library** (`machine-library-design.md`, design
  FROZEN 2026-10-03; decision-log rows in `AroraBarakChapter1Plan.md`):
  `TuringMachine/Build/{Convention,Wrappers,Loop,Primitives}.lean` — 12
  primitives (P1–P12, harvest-heavy), capture/silence + halt-redirect +
  timed cond wrappers, the bounded-loop combinator factored from 2A's
  `enumMachine_contracts`. **Spec layer LANDED 2026-10-03** (design §9a
  refinements recorded): `Cfg.ofWords` seam + pure vocabulary fully
  proved; 18 sorried contracts (4 wrapper, 2 loop, 12 primitive); order
  list and facade at 57 modules. **Bridge export landed 2026-10-03**
  (`Turing.timed_universal_concrete`; TMSAT bridge discharged, tree
  admissions 46). **Infra audit pack prepared 2026-10-03**
  (`audits/ch1-infra-{pack,bundle}.md`). **Round 1: gate OPEN** (blocker:
  `exists_loopTM` refuted by zero-step advances; majors: all-state-word
  round domain, D5 interface gaps). **Round-2 repairs executed +
  re-audit pack prepared 2026-10-03** (`audits/ch1-infra-r2-{pack,
  bundle}.md`): loop redesigned (positive duration, input-indexed `Inv`,
  input-dependent step/accept), `exists_loopFindTM` + P13 `pairConcat` +
  P14 `pairDup` + C1 `pairMapSnd` added, sketches corrected, errata
  acknowledged, historical evidence supplied, D5 re-issued as a concrete
  mapping; Build 22 contracts, tree 50 admissions. **Round 2: 0
  blockers, 1 major, 3 minors** (loops/P13-P14-C1/tables passed; the
  major: the final-answer loop conclusion cannot discharge
  `enumMachine_contracts`). **Round-3 repair executed + pack prepared**
  (`audits/ch1-infra-r3-{pack,bundle}.md`): `exists_loopCfgTM`
  configuration-level export + §9c translation, coefficient-shift and
  pairing-derivation notes adopted, D5 v3 narrowed to epoch-2 + P10;
  Build 23 contracts, tree 51 admissions. **GATE CLOSED 2026-10-03**
  (round 3: 0 blockers/majors, 3 documentation minors swept in the
  closing commit; `audits/ch1-infra-resolutions.md`): the spec surface
  is audited-true, D5 v3 approved (D-MEM explicitly limited; 2B
  component-level; E3/E4 deferred to their brief audits), the
  `enumMachine_contracts` translation certified exactly. **Fill briefs
  issued 2026-10-03** (`briefs/lib-fill-batch{W,P,L}.md`: 4 + 15 + 4
  targets, 14/34/18 pts, P and L with continuation anticipated;
  sanctioned roots `capture_run` → P/L and `exists_loopFindTM` →
  P-splitSolve; L carries the round-3 item-4 construction ledger as
  binding). **Checkpoints integrated 2026-10-03**: W complete (4/4,
  admission-free; `cond` multiplier 5; two promotion requests held for
  the fill-audit round), P 11/15 (frontier `pairLenCheck`; sanctioned
  roots unused), L the 2A pattern (`loop_run` + both summation lemmas
  proved; combinators at the single admitted `loopHost_contracts`;
  `capture_run` consumed in the helpers). Tree: 57/57 zero errors,
  **33 admissions**; size exceptions for `Primitives.lean` (1,687) and
  `Loop.lean` (1,466) recorded. **Continuation briefs issued 2026-10-03**
  (`briefs/lib-fill-batch{P2,L2}.md`, base `90273dd6`): P2 = targets
  12–15 (14 pts; one sanctioned root, `loopHost_contracts` via
  `exists_loopFindTM`, for `splitSolve` only); L2 = `loopHost_contracts`
  (10 pts; zero sanctioned admissions — completion ends the file
  admission-free; the checkpoint agent's continuation document is
  binding). Next: dispatch, then integration, then the library
  fill-audit round (carrying W's two promotion requests and the P/L
  size exceptions), then the E2 continuation briefs.
  **Round 2 integrated 2026-10-04: L2 COMPLETE** (`loopHost_contracts`
  proved; the loop admission-free end to end, realized constant 10),
  **P2 13/15** (12–13 filled via the proved W layer; target-14
  relocation support proved; frontier `pairMapSnd`/`splitSolve`).
  Tree: 57/57 zero errors, **30 admissions**; 21/23 contracts
  admission-free. **P3 closure brief issued 2026-10-04**
  (`briefs/lib-fill-batchP3.md`, base `b2f46419`; targets 14–15, 8 pts,
  zero sanctioned admissions; completion = 23/23, the whole `Build/`
  tree admission-free). **P3 integrated 2026-10-04: `pairMapSnd`
  PROVED (coefficient 40), 22/23**; `splitSolve` reduced to the body
  controller (`splitSolve_of_body` + proved components; one named
  gap). Tree: 57/57 zero errors, **29 admissions**. **P4 closure brief
  issued 2026-10-04** (`briefs/lib-fill-batchP4.md`, base `494d4835`;
  one target, 5 pts, zero sanctioned admissions; the P3 frontier
  document's ten steps are the work plan; completion = 23/23).
  **P4 integrated 2026-10-04: THE LIBRARY IS COMPLETE — 23/23,
  `Build/` admission-free, tree at 28 campaign-only admissions**
  (W 1 round, L 2, P 4; ~250 new privates; every sanctioned root
  closed at merge). **Fill-audit pack prepared 2026-10-04**
  (`audits/ch1-libfill-{pack,bundle}.md`; whole-span attestation:
  net deletions = exactly the 23 placeholders, zero non-private
  additions). **GATE CLOSED 2026-10-04, single round: 0 blockers, 0
  majors, 2 instrument/documentation minors swept in the closing
  commit** (`audits/ch1-libfill-resolutions.md`). **The library is
  complete and audited end to end.** D6 approved-deferred (serial
  promotion of `timed_input_bound`/`timed_rewind`, post-gate); D7
  approved-trailing (the `Loop`/`Primitives` split, ride-along
  audited, with the auditor's cross-file-privates qualification
  binding). **E2 continuation briefs issued 2026-10-04**
  (`briefs/ch2-e2cont-batch{A,B,C,D}.md`, base `64d82f84`).
  **Integrated 2026-10-04: A/C/D COMPLETE, B 1-of-3** — nine of ten
  epoch-2 targets admission-free (enumerator cluster incl. the HALT
  pair; Exercise 2.1; the full TMSAT package); B's one frontier is
  the integrated reverse NDTM host (guessing phase, coverage, and
  normalization banked; five-step plan in its REPORT). Tree: 57/57
  zero errors, **23 admissions**; ch2 ledger **36/59 proved**. Next:
  the B reverse-compiler continuation brief, then the epoch-2 audit.
  **B2 brief issued 2026-10-04** (`briefs/ch2-e2cont-batchB2.md`, base
  `e72d95bf`; 9 pts; zero sanctioned admissions; completion closes the
  epoch at 10/10). **B2 integrated 2026-10-05: EPOCH 2 CONSTRUCTION
  COMPLETE — all ten targets admission-free** (commit `1514fd6b`;
  Theorem 2.6 machine-checked both directions; 42 new `b2*` privates;
  scheduler seam closed by read-normalization, dispatch on the actual
  first halt, definitional table coincidence; independent kernel
  traversal `audits/logs/ch2-e2cont-B2-axioms.log`). Tree: 57/57 zero
  errors, **21 admissions** (5 padding + `EXP_subset_NEXP` + 15 E3/E4
  statement layer); ch2 ledger **38/59 proved**. **Epoch-2 audit pack
  prepared 2026-10-05** (`audits/ch2-epoch2-{pack,bundle}.md` + the
  whole-span attestation under `audits/evidence/ch2-epoch2/`; 34
  attachments). **GATE CLOSED 2026-10-05, PASS in one round: 0
  blockers, 0 majors, 2 minors (audit-material errata, swept via
  `audits/ch2-epoch2-resolutions.md`), 11 notes** — the auditor
  rebuilt all 57 modules from empty oleans and verified all 386
  privates / 1,167 kernel declarations admission-free. **Epoch 2 is
  complete and audited end to end.** The post-gate serial queue is
  unblocked, in order: **D6 promotions — EXECUTED 2026-10-05**
  (`Turing.MultiTapeTM.timed_input_bound` in `Deterministic.lean`,
  symbol-generalized; `Turing.FinTM.timed_rewind` in `Simulation.lean`
  verbatim; Wrappers privates removed, clients on the public API;
  57/57 zero errors, 21 admissions unchanged, promoted lemmas +
  epoch-2 closure regressions all clean —
  `audits/logs/d6-promotion-{sweep,axioms,lint}.log`), then **D7 —
  EXECUTED AS A MEASURED DEFERRAL 2026-10-05**
  (`audits/evidence/d7-split-analysis.md`; tool
  `scripts/d7_split_analysis.py`): pure relocation infeasible — each
  file is one private family (96–99.9% span); compliant splits need
  ≥ 125 cross-file promotions program-wide (34/43/24/16/8 per file),
  intersecting E5's live-replacement/deletion sets, so the physical
  splits run **after E5** via one internal-namespace visibility
  proposal, ride-along reviewed in the E3 pack (pilot: the
  Nondeterminism forward/reverse cut, cost 5); size justifications
  stand — then **E5 — EXECUTED 2026-10-05, deletion-only** (the three
  inventoried dead families removed: 28 privates, 549 lines; EXP
  2,887 → 2,534, Nondeterminism 2,627 → 2,454; live routes untouched;
  contract-evidence lemmas deliberately retained; 57/57 zero errors,
  21 admissions unchanged, closure regressions PASS —
  `audits/logs/e5-dedup-{sweep,axioms,lint}.log`; D7 re-measured
  post-E5: 34/43/24/13/8, deferral confirmed). **The post-gate serial
  queue is complete.** **E3 briefs issued 2026-10-05**
  (`briefs/ch2-epoch3-batch{A,B,C,D}.md`, base `b55180a8`; 3A padding
  cluster 26 pts / 3B SAT track 24 pts (continuation anticipated) / 3C
  snapshot locality 22 pts / 3D TAUTOLOGY membership 6 pts; zero
  sanctioned admissions; completion closes the E3 statement layer at
  15 targets). **Integrated 2026-10-05: C/D COMPLETE, B 2-of-3, A at
  the exponential split body** — 8 new closures (the five snapshot
  locality lemmas, both SAT memberships, TAUTOLOGY membership); tree
  57/57 zero errors, **13 admissions**; ledger **46/59 proved**. Two
  new size exceptions recorded (SAT 2,363; Tautology 1,278). A's
  frontier: the native exponential split-search body existential
  (five-step plan in its REPORT; 35 `e3_*` privates banked). B's
  frontier: run lemmas + time proof for `satRedTM`'s streaming states
  9–34 (startup proved; all reduction mathematics banked).
  **Emitter-increment design drafted 2026-10-05**
  (`machine-library-design.md` §11, awaiting decisions 11.1–11.3:
  `emitLoop` + `emitPhase` + P16–P18 + width-parametric split search;
  ≈ 27 pts; 3B-cont and 4A are the customers). **3A-cont brief issued
  2026-10-05** (`briefs/ch2-e3cont-batchA.md`, base `b75b6771`,
  bespoke in parallel with the design review; zero sanctioned
  admissions). §11 approved 2026-10-05 (11.1–11.3); **emitter spec layer
  landed** (5 sorried contracts + 2 transformers + 2 vocabulary defs;
  57/57 zero errors, 18 = 13 + 5 admissions exactly; regressions
  PASS) and the **emitter-infra audit pack prepared**
  (`audits/emitter-infra-{pack,bundle}.md`, 14 attachments; gate on
  zero blockers/majors, findings to
  `audits/emitter-infra-findings.md`). 3A-cont dispatched by the user
  (bespoke, independent); **integrated 2026-10-05 as a verified
  partial checkpoint** (69 `e3c*` privates banked — the full phase
  family for the split-search body; zero targets closed, zero new
  admissions; a maintainer base-hash erratum in the brief was caught
  by the agent and is recorded with its process correction). **Round 1: 0 blockers / 2 majors / 3 minors** (adequacy, not
  falseness); repairs landed (the two clean-call bridge contracts in
  `Loop.lean`, the 3B/4A mappings in §11b, the forwarding-host sketch
  correction, token/doc sweeps; 57/57 zero errors, 20 = 13 + 7
  admissions; full-print regressions PASS) and **round-2 pack
  prepared** (`audits/emitter-infra-r2-{pack,bundle}.md`, 31
  attachments incl. the evidence addendum both majors demanded).
  **Round 2: 0 blockers / 2 majors / 1 minor** (R1 3–5 closed;
  constructions validated); **round-3 repairs landed** (`0 < C.k` on
  both bridges — the zero-tape degeneracy; §11c's corrected 4A
  stage-to-seam mapping superseding §11b item 3; the §11a marker) and
  the **round-3 pack prepared** (36 attachments incl. the phase-4
  reaudit table and the A-cont `e3c*` provenance). **A-cont-2 brief issued
  2026-10-05** (`briefs/ch2-e3cont-batchA2.md`, base `d5ac2377`,
  rev-parse-verified; targets 2/4/5 only — 1/3/6 deferred to
  post-fill instantiation via `splitSolveWith`; ≈ 13 pts, zero
  sanctioned admissions, dispatches in parallel with the r3 audit).
  **EMITTER GATE CLOSED 2026-10-05** (round 3: 0/0/1 —
  `audits/emitter-infra-resolutions.md`; the attribution minor swept
  comment-only in the closing commit; binding fill/brief handoffs
  recorded). **Fill briefs issued 2026-10-05**
  (`briefs/emitter-fill-batch{L,P,W}.md`, base `d7b5b6f9`; L ≈ 17 pts
  bridges-then-emitLoop via the forwarding host, P ≈ 10 pts
  splitSolveWith under the gate disciplines, W 3 pts emit_run; zero
  sanctioned admissions each; the `e3c*` family as harvest template;
  completion drops the tree 20 → 13). **W integrated 2026-10-05**
  (`emit_run` proved, one private, Wrappers admission-free; spec
  7 → 6). **A-cont-2 integrated 2026-10-05**: the exponential
  reverse host closed (29 `a2*` privates; B2 host + native binary
  countdown); targets 4/5 escalated over a recorded maintainer
  scoping erratum (the Thm 2.22 route cites the excluded
  `EXP_subset_NEXP`) and move to **A-cont-3, now covering 1/6/3/4/5**
  post-`splitSolveWith`. **P integrated** (2/3: appendBit + unaryToken closed;
  `splitSolveWith` at the body wall with 83 privates banked incl.
  the whole-bank cleaner `emitterBankTM` + the conditional
  `emitterSplit_of_body`). **L integrated — COMPLETE 3/3**
  (`Loop.lean` admission-free, 5,713 lines, 119 privates; unified
  `emCallTM` bridge controller at the audited envelope; forwarding
  host + `emLoop_sum`). **The emitter layer stands at 6/7**; tree at
  **13 admissions** (12 campaign + `splitSolveWith`). **P2 brief issued 2026-10-05**
  (`briefs/emitter-fill-batchP2.md`, base `08884731`; the last
  contract against the predecessor's five-step plan, with the proved
  W/L layer now citable and L's `emCallTM` as the controller
  precedent; completion = emitter 7/7, tree 12). **P2 integrated 2026-10-05 — THE
  EMITTER LAYER IS COMPLETE (7/7, `Build/` admission-free)**: the
  split-search body closed via the proved install bridges in one
  round — the increment's thesis confirmed at first consumption; 68
  privates; tree at **12 admissions, all campaign**. **Fill-audit pack
  prepared 2026-10-05** (`audits/emitter-fill-{pack,bundle}.md`, 22
  attachments; whole-span attestation name-exact at 271 privates;
  gate on zero blockers/majors, findings to
  `audits/emitter-fill-findings.md`). **FILL GATE CLOSED 2026-10-05, PASS
  in one round (0/0/2/7)** — the emitter increment is complete and
  audited end to end (`audits/emitter-fill-resolutions.md`; both
  minors maintainer errata, swept). **The closing wave is dispatched-ready
  2026-10-05**: A-3 (`briefs/ch2-e3cont-batchA3.md`, 1→6→3→4→5 via
  `splitSolveWith`; zero sanctioned), 3B-cont
  (`briefs/ch2-e3cont-batchB.md`, the emit-loop rebuild under the
  r2-finding-5 schedule; zero sanctioned), 4A
  (`briefs/ch2-epoch4-batchA.md`, the summit under the embedded
  boundary table; one sanctioned root via 3B-cont for the SAT3
  pair; Astra distillation explicitly non-binding). **A-3 (run β of a
  recorded parallel-run incident; α discarded whole under logged
  criteria) and 3B-cont integrated 2026-10-05**: the padding cluster,
  `EXP_subset_NEXP`, and `SAT_reducible_SAT3` closed; tree at **6
  admissions** (`TAUTOLOGY_coNPComplete` + Hardness five); ledger
  **53/59**. **4A checkpoint integrated 2026-10-05**: 1/5 closed +
  77 privates banking the summit's whole pure layer (tableau,
  product encoding, chunk-exact serialization identity, quadratic
  ledger, oblivious normalization, certificate call, conditional
  emitter assembly); frontier = the packed-record producer, the
  round controller, equisatisfiability (four-step plan); tree at
  **5 admissions**; ledger **54/59**; Hardness 1,193 lines (new
  recorded exception). **4A-2 brief issued 2026-10-05**
  (`briefs/ch2-epoch4-batchA2.md`, base `f815da30`; the four-step
  plan binding; sanctioned root withdrawn — zero admissions
  sanctioned; producer = the checkpoint boundary).
  **4A-2 native-preparation checkpoint integrated 2026-10-06**
  (Codex `a4ca9302`): a verified partial *earlier* than the
  complete-producer boundary — **52 new proved privates** for the
  native preparation phase (the exact arithmetic header
  `clPrepHeader`, the all-false reference simulation
  `clRef*`/`clRefClock*` identified with the public
  `oblivious_schedule`, the in-place binary counter `clCount*`
  with carry/rewind re-proved on a silent absorbing machine, and
  the `clRefCount*` administrative frame); **no target closed,
  zero new admissions**, tree still at **5 admissions**, ledger
  **54/59** unchanged; Hardness.lean now 2,112 lines (size
  exception continues). Verification independently reproduced
  (checksums 25/25; freeze 919/0; byte-identical replay; 57/57
  sweep; whole-module traversal = 375 decls / 4 sorry roots; lint
  0 FAIL / 1 WARN; `audits/logs/e4A2-checkpoint-*`). **4A-3
  frontier**: the complete packed-record producer (trajectory +
  signed-position records + greatest-strictly-earlier last-visit
  search with a sequential-access ledger), genuine `initCfg`
  startup, the ordered emission controller under common budget
  `P` ≠ `T`, and the output-identity-then-equisatisfiability
  close. **4A-3 brief issued and the recording checkpoint
  integrated 2026-10-06** (Codex `9f1808a6`): **150 more proved
  privates** — the stored inclusive trajectory (`clRec_complete`,
  rows `0..T`, silence + `(4l+7)(T+1)²` cost + `2l(T+1)²` length),
  signed/clamped tracking, the cross-sum comparator, the charged
  sequential field reader — no target closed, zero new admissions,
  tree still at **5 admissions**, ledger **54/59**; Hardness.lean
  4,471 lines (exception continues); three-pass traversal 757
  decls / 4 roots / kernel surface = the five theorems
  (`audits/logs/e4A3-checkpoint-*`). **4A-4 frontier (still step 1,
  components complete — producer assembly is the minimum bar)**:
  header unpacking, row loader + greatest-strictly-earlier search
  with scratch resets and one charged ledger, the complete
  producer, then startup, the controller under `P` ≠ `T`, output
  identity, equisatisfiability. **4A-4 complete-producer checkpoint
  integrated 2026-10-06** (Codex `8e2d7ee1`): **step 1 closed** —
  `clPackedRecords_machine` proves the entire packed result (header +
  inclusive trajectory + full greatest-strictly-earlier visit table)
  from native input in one machine with total ledger `a*(|x|+1)^r`;
  176 new privates (455 total); no target closed, zero new
  admissions, tree still at **5 admissions**, ledger **54/59**;
  Hardness.lean 7,446 lines (exception continues; prime
  routine-layer retrofit target); three-pass traversal 1191 decls /
  4 roots / surface = five theorems
  (`audits/logs/e4A4-checkpoint-*`). **4A-5 frontier (the body,
  expected to close the gate)**: final install with the producer +
  genuine `initCfg` startup → ordered controller with common budget
  `P` (≠ `T`, ≠ producer ledger) → `clEmitter_of_body` +
  `clTableau_chunks` output identity → pure equisatisfiability;
  sanctioned checkpoint only at the proved output identity.
  **4A CLOSED 2026-10-06** (Codex `57507830`+`06ce95fa`): the
  five-target completion gate passes — Cook–Levin machine-checked
  end to end on the campaign's own audited model; `SAT_NPHard`,
  `SAT_NPComplete`, `SAT3_NPHard`, `SAT3_NPComplete` all empty
  roots at the standard triple; `Hardness.lean` admission-free
  (9,937 lines, 618 privates — THE prime routine-layer retrofit
  target); net deletions = exactly the four authorized `sorry`
  bodies; no-allowlist traversal 1550 decls / 0 sorryAx / surface =
  five theorems (`audits/logs/e4A5-closure-*`,
  `audits/programs/ch2-e4A5-ClosureAxioms.lean`). **Ledger 58/59;
  tree at 1 admission** (`TAUTOLOGY_coNPComplete`). **4B brief issued 2026-10-06**
  (`briefs/ch2-epoch4-batchB.md`, base `b133a3d4`; the docstring
  route binding; new DNF names binding; fallback-flips-sides and
  empty-term/empty-DNF pitfalls pinned; ≈ 7 pts; completion = the
  campaign tree admission-free). **4B CLOSED 2026-10-06** (Codex
  `9e9494aa`): `TAUTOLOGY_coNPComplete` via the audited dual route —
  the five definitional links + the `R(n)=0` one-round emit-loop
  transducer (28 privates, linear time); **ledger 59/59, the
  campaign tree at ZERO admissions** — the whole 65-module surface
  (11,436 kernel declarations) admission-free
  (`audits/logs/e4B-closure-*`,
  `audits/programs/ch2-e4B-ClosureAxioms.lean`). → the epoch-3/4
  audit pack — **GATE CLOSED 2026-10-06, PASS in round 3** (0 blockers /
  0 majors cumulative; findings/resolutions on record)
  (ride-alongs included: colleague's DNF adaptation, the parallel-run
  provenance, the discarded α hash, **colleague merge #2's 9-module
  private rewiring + the 57→65 order extension**) → E5 closure — **phase 1 complete 2026-10-06**
  (dedup 153 privates, drift attestation CLEAN, closure pack,
  zero-sorry sweep + traversal PASS); **phase 2 (blueprint
  increment) pending a user decision on the dep-graph refresh**
  (stale `dep_graph.json`; refresh needs the banned build —
  options: one-off artifact build in a throwaway worktree, or
  defer past the main merge) → the machine-routine layer +
  retrofit (recorded decisions).
  Subsumes 2C's
  `prefixTM`/`fixedPair` promotion requests. Dedup of superseded batch
  privates is an E5 closure task — **auditor-adopted live/dead guidance (epoch-3/4 round 1, finding 14)**: `clFill*` → producer path is LIVE; `clCertificateCall` and `clTrack_schedule` dead at source; `e3c*` mixed (`e3c_bits_injective` live); SAT's max-pass prefix live; dedup from a kernel-derived inventory, never by prefix or checkpoint label. Also queued for the retrofit: the 11 disclosed generated kernel artifacts (imported-definition equation lemmas + the private-structure `deriving` instance in SAT.lean). Mathlib TM2 rejected as substrate
  (evaluation recorded in the ch1 decision log).
* **Machine-routine layer (user decision 2026-10-06: build once
  chapter 2 is done, in the E5-closure/D7 window, before chapter 3).**
  Three pieces, sized by the A-chain's evidence (≈ half of the A2/A3
  deliveries' 202 native privates are hand-rebuilt universal routines;
  `emitterBank*`/`emitterP2*` relocation privately re-harvested three
  times; A3's proved costs `3|w|+3` copy / `2|w|+2` clear match the
  prior art's `3w+2`/`2w+2` to within one step):
  1. a generic **bank-embedding theorem** — a verified routine on its
     own small tape set runs on any selected tape subset of a `k`-tape
     machine, cost unchanged, all other tapes/heads framed (the public
     generic form of `emitterBank*`/`clBank*`/`clSlot*`);
  2. a generic **seam-composition lemma** — sequential composition of
     two controllers at a canonical `Cfg.ofWords` seam with first-return
     cuts and additive budgets (the generic form of the per-batch
     dispatch gluing);
  3. **catalog promotion** of transfer/clear/copy/compare/increment as
     public machines with exact costs, seeded from the already-audited
     A-chain privates (D6-style promotion, not new proof work).
  **Survey update 2026-10-06 (pre-§12, recorded ahead of the
  colleague meeting 2026-10-07)**: the colleague's ch6 merge already
  supplies the **function-level half** of this layer —
  `TuringMachine/CounterProg{,Run}` (goto programs over unary
  registers, compiled once into `FinTM`, `t` abstract steps ≤
  `t(2t+3)` machine steps, FP bridge), `ClassNP/Transducer` (Mealy
  machines as work-tape-free FinTMs in `|x|+1`), `ClassNP/
  PolyTimePairing`/`PClosure` (FP/`P` closure, built ON our audited
  catalog), `UnaryTape`. The §12 design must **consume, not
  duplicate** these; the remaining gap is the **config-level half**
  (bank-embedding, seam-composition at canonical `Cfg.ofWords`
  seams — the emitter r1 finding stands: function contracts cannot
  deliver clean-return seams) plus residual catalog promotions.
  Items for the meeting: colleague roadmap (more campaign-module
  rewiring?), `CounterProg` as general substrate vs. sibling
  module, `Build/*` ownership during the retrofit window, ch3/
  TimeHierarchy alignment. Citation duty now extends to the
  colleague's modules alongside lax-434930.
  Mechanism: a design addendum (`machine-library-design.md` §12) →
  statement gate → fills → audit, folded into the queued D7
  internal-namespace visibility proposal. **Citation discipline
  (binding, user guideline 2026-10-06): diligently cite the code this
  adapts — the design is inspired by Édouard Bonnet's
  `classical-complexity` (Lax Archive lax-434930), module
  `proofs/Lax434930Proofs/InclusionAux/TimeCompiler/` (StackProgram's
  `compile_correct`, StackRename's `rename_executes`/`executes_in_sum`,
  and the transfer/clear/copy/for/repeat routine catalog), commit
  `0c0840319318215fd7b36a9a822b81ce55cf6941`, Apache-2.0. The §12
  addendum, the affected module docstrings, and the blueprint entries
  must each carry this citation. Adapt design, never code: different
  toolchain (their Lean 4.33 / our 4.25) and machine model (TM2 keyed
  stacks vs FinTM tapes with heads); nothing is imported or
  transcribed, and the external files stay out of the repo.**
* **`Build/` catalog layout refactor toward per-theme files (queued;
  user decision 2026-10-08, §12 open decision 12.2).** The routine layer's
  new catalog rows land in a single `Build/Catalog.lean` (option (a)) to
  keep the audited `Primitives.lean` byte-identical; once the retrofit
  shrinks the `Build/` files, refactor the catalog toward the symmetrical
  per-theme layout (option (c): `Build/Catalog/{Transfer,Arith,…}.lean`),
  folded into the queued D7 split window. *Origin:
  `machine-library-design.md` §12, decision 12.2.*
* **Retrofit pass over chapters 1–2 with the routine layer (user
  decision 2026-10-06: queued as backlog, explicitly important — to be
  done at some point, not time-bound).** Once the machine-routine layer
  is audited, revisit the existing ch1 and ch2 formalizations —
  Cook–Levin included — and simplify them against it: replace the
  privately re-derived bank/relocation/dispatch/frame families
  (`emitterBank*`, `emitterP2*` relocation, `clBank*`/`clSlot*`,
  `clCopy*`/`clCmp*`/`clRead*`/`clCount*`, and their ch1 analogues in
  `Build/Primitives.lean`/`Build/Loop.lean`) with catalog citations and
  the two generic theorems. Expected effect: large private-count and
  line-count reductions in the five size-exception files, directly
  serving the deferred D7 splits. Statement freeze applies — public
  surfaces never change; every replacement batch goes through the
  standard sweep + traversal + audit protocol. Prerequisite: the
  machine-routine layer's gate is CLOSED.
  **Inventories + partition recorded 2026-10-09** (plan §4d; verbatim
  reports `audits/retrofit-inventory/`): realizable conservative scope
  ≈ −98 privates / −1,900 lines, dominated by dead code (`emitterBank*`
  itself is dead — delete, not port); the R1/R2/catalog-shaped glue is
  overwhelmingly LEAVE under the strict-simplification bar (monolithic
  hosts, loop back-edges, canonical-only rows, missing selected-tape
  exports). Batches RB1 (Loop) / RB2 (Primitives) / RB3 (Hardness),
  `Universal*` excluded; **integration by side branch + PR, user merges
  manually** (user rule 2026-10-09). Decisions D-R1 (Embed selected-tape
  exports, proposed to ride the §13 Z1 gate), D-R2 (Primitives ownership
  — option (a) deferred to 12.2c with feasibility proven; stretch (c)
  inside RB2), D-R3 (machine-agreement transfer lemma, deferred) are in
  §4d. The artifact-count note above corrects to **12** generated kernel
  artifacts, located in `Nondeterminism`/`EXP`/`SAT`, none in Hardness.
* **Audit-mandated fill-brief inheritances** (each brief must carry these
  verbatim from the cited records):
  - `NP_subset_EXP` enumerator: the contract-by-contract table —
    `audits/ch2-phase1-round3-findings.md` (via `…-resolutions.md`).
  - NTIME/Theorem-2.6 compilations: the simulator invariant tables and
    branch-correspondence contracts — `audits/ch2-phase2-findings.md`
    (note 3: no untimed composition or bare computability substitutions).
  - `TMSAT_mem_NP`: the `PolyBound` budget chain and the **new public
    quantitative bridge** for `timed_universal`'s constant — one simulator
    chosen before code and input, both success and timeout clauses, the
    suggested form `(3|α| + 14·canonizerTime(|α|) + 50)·(t+1)²` avoiding a
    `PolyBound` import into Chapter 1; Chapter-1 surface growth via the
    shared-file mechanism, flagged for its own audit —
    `audits/ch2-phase3-{findings,reaudit-findings,resolutions}.md`.
  - `TMSAT_NPHard`: exact-value emission case table and the explicit `T'`
    deadline formula (never majorize the certificate length) — same records.
  - Cook-Levin emitter (E4): the six-stage output-silence contract **and**
    the round-2 boundary-check table, the product snapshot encoding, and the
    exact serialization-length ledger (never constant-per-clause) —
    `audits/ch2-phase4-{findings,reaudit-findings,resolutions}.md`.
  - Locality fills: strict `s < t` in `prevVisit`; keep no-write and
    write-blank distinct (`some none` erases); writes on the halting
    transition count — phase-4 Derivation A.
  - `TAUTOLOGY_mem_coNP`: the DNF evaluation-congruence bridge as a private
    lemma — phase-4 round 1, note 6.
* **Chapter-2 blueprint increment** — at campaign closure (E5), per the
  Chapter-1 precedent (dep-graph merge, writer agents, validator).
* **P3.4 — Ladner's theorem (queued; user decision 2026-10-08: CH34-Q6
  core-late, moved to backlog at the P3.3 draft).** The last undrafted
  statement phase of the chapters-3-4 campaign
  (`AroraBarakChapters3-4Plan.md` §4): `Diagonalization/Ladner.lean` with
  `SAT_H` (SAT padded by the diagonal gaps of `H`), Ex 3.6(a) (`H`
  computable in polynomial time), the Claim of [AB09, Theorem 3.3]'s proof,
  Ex 3.6(b), and Theorem 3.3 itself (`P ≠ NP` gives an `NP`-intermediate
  language), ~6 sorried statements. Draft when the live rounds settle (the
  `Diagonalization.lean` facade unfreezes at the P3.2 close); it consumes
  the closed chapter-2 `SAT` surface and the received `polyTimeComputable`
  layer, and is independent of P3.3's code layer. *Origin:
  `AroraBarakChapters3-4Plan.md` §4 (P3.4 row), decision CH34-Q6.*
* **ARM extensions + colleague sync (moved to backlog 2026-10-09; user
  decision — outreach to Hydroxyi/Jason Dong initiated the same day).**
  The three proposed extensions to the co-owned `LogProg` tree
  (`AroraBarakChapters3-4Plan.md` §2.5), each a future infrastructure
  statement phase with its own audit gate once agreed: (1) a
  **nondeterministic ARM** — a `choose` instruction compiling to
  `FinNDTM` with the space theorem carried over (customers: `PATH ∈ NL`,
  Immerman-Szelepcsényi, Cor 4.21); (2) a **polynomial-width ARM
  variant** — `poly(n)`-bit registers for the `PSPACE`-level algorithms
  (`TQBF ∈ PSPACE`, `NP ⊆ PSPACE`, Savitch at polynomial level); (3) the
  **configuration codec as a program** — extends Hydroxyi's deterministic
  `ConfigCount` to NDTMs, adapting (citing, never vendoring) cslib's
  upstream `ConfigBound` design. Also on the sync agenda: `CounterProg`'s
  one-way input (the `2^O(S)` searches need indexed access or a rewind
  instruction), and the two citation-audit provenance questions, asked as
  questions (their `LogProg` compiler vs lax-434930's `TimeCompiler`;
  `ConfigCount.core` vs cslib `ConfigBound`'s `Cfg.core`). **Blocks fills
  only, never statements**: the machine-heavy P4.x fills named above plus
  the ARM interface statements deferred out of P4.1; every other fill
  epoch and the retrofit proceed. Returns to the plan on Hydroxyi's
  reply. *Origin: plan §2.5, §4a/§4b stage 1, CH34-Q2; the 2026-10-08
  citation-audit row.*

---

## 3. Deferred formalizations

### Chapter 1

* **Phase 5 (deliberately unscheduled; "a task for much later"):** the
  `O(T log T)` oblivious simulation ([AB09] §1.7 / Ex 1.6); the RAM-TM
  exercise (Ex 1.9); a fuller mathlib recursion-theory bridge beyond the
  `MathlibBridge` quarantine. *Origin: ch1 plan §5, decision of 2026-09-16.*
* **Waived model bridges** — revisit only if a downstream result ever needs
  a formal bridge: the append-only-output and start-marker-initialization
  conventions vs. [AB09]'s model (no read-write-output machine is
  formalized; no exact [AB09] step count is ever imported). *Origin: ch1
  plan §5 phase-2 notes; ch1 phase-2 audit findings 3/13.*
* **`Universal.lean` factoring** — 2831 lines (escalation recorded at
  epoch 4A): ~1100 lines are stopped-interpreter administrative copies
  forced by per-module `match` auxiliaries; the 4A report's three
  shared-lemma generalizations are the designated future factoring. Also
  CH1-Q2(a)'s promotion candidates. *Origin: ch1 decision log, epoch-4A row.*
* **Polynomial canonizer for a concrete scheme** (CH1-Q1(c) continued):
  Chapter 2's `TMSAT_mem_NP`/`TMSAT_NPComplete` now carry the hypothesis
  `PolyBound c.canonizerTime`; a combinator-built effective scheme with a
  *proved* polynomial canonizer would discharge the hypothesis for a
  concrete scheme and reconnect Q1(c). *Origin: ch2 phase-3 audit.*
* **Blueprint planner refinement** — writers flagged planner `\uses` edges
  not present in the cited proofs (reproduced verbatim per pipeline rules).
  *Origin: ch1 decision log, blueprint-extraction row.* **Ch2 increment
  instances (2026-10-06/07)**: `NPHard.polyTimeReducible` → `clLastRound`;
  `clA5Equisat` → `SAT_NPHard` (forward edge); `sat_comp_on_image` → `SAT`;
  `satHost_clean` → `SAT_reducible_SAT3` (forward edge);
  `choice_certificate_iff` → `capturedSummary`; `cont_split_bridge` →
  `contPairTM`; `goes_loop` → `run_pos_le`, `MOp`;
  `pairedVerifier_malformed` → `paddedVerifier`; `emit_run` → `redirectTM`;
  `taut_membership_of_verifier` → `TautSyntax`; `taut_machine_pair` →
  `tautSplit` (forward edge); `foldr_max_le_of_forall` →
  `falsifyingClause_eval_false`; `polyTimeComputable_of_linear` →
  `pairMapSnd`; `PolyTimeReducible.trans` → `mem_P_of_polyTimeReducible`;
  `acceptTM_halts_iff` → `prefixTM`. The forward edges (a helper "using" the theorem it serves)
  suggest the planner attributes by source-range adjacency or docstring
  mentions rather than by kernel dependency; the kernel walker used for the
  E5 dedup could supply exact edges.
* **Blueprint `\difficulty` calibration across writers** — parallel
  writers split on trivial structural inductions whose cases each close in
  one line: some rate them 3 (no real branching), others rubric-literal 4
  (any induction or case split). Observed in the ch2 increment (NP,
  Snapshot, CNFEncoding at 3; Nondeterministic, CounterProg at 4). The
  dataset would benefit from one normalization pass, which is mechanically
  detectable from the proof source; or tighten the rubric text in the
  writer agent definition. *Origin: blueprint-writer reports, ch2
  increment parts 2–3.*
* **For the colleague: `ClassNP/PClosure.lean` docstring/statement gap** —
  the `lenEq_mem_P`/`lenLe_mem_P` docstrings speak of *pairs*, but the
  languages range over all bit strings, the total projections sending a
  non-pair to the empty word (so every non-pair lies in the `lenEq`
  language). The statements are fine; the docstrings undersell their
  domain. The blueprint documents the Lean behavior. *Origin:
  blueprint-writer report, ch2 increment part 4.*
* **Blueprint-writer process fix: require the per-entry strict check** —
  in the ch2 increment, writers that ran `statement_quality.py` /
  `dataset_hygiene.py` from the command line were grading the dataset
  *cache*, not their chapter, and every one of the 178 strict-rubric
  flags came from exactly those five writers (SAT, Primitives, EXP, CoNP,
  PClosure); writers that imported `check(..., strict=True)` and ran it
  per entry produced zero. Fix: state the per-entry function-call check
  as a hard requirement in `.claude/agents/blueprint-writer.md` (and
  ideally add a `--chapter` mode to the scripts). The orchestrator-side
  uniform pass used here (`build_dataset.parse_blueprint` + both checks,
  names demangled via `PRIVATE_RE`) could also become a `/blueprint-
  extract` step. *Origin: ch2 increment, 2026-10-07.*
* **Stale module docstring: `Build/Primitives.lean`** — still says every
  theorem below is sorried; the emitter fill gate closed every one of them.
  Comment-only fix, eligible for the next comment-only sweep (comment-
  stripped byte-identity check per precedent). Same sweep: the
  `emitterP2EraseCfg` docstring says the input stays "at its origin", but
  the definition places the head at position 1 (the first input cell) —
  the blueprint now states the Lean behavior. *Origin: blueprint-writer
  reports, ch2 increment parts 1 and 6.*

### Chapters 2-3

* **§2.4 web of reductions** (`INDSET`, `0/1 IPROG`, `dHAMPATH`, exercise
  problems) — each needs a graph/arithmetic encoding surface; the legacy
  `Complexity/NPReductions/*` files may eventually be **retargeted** as the
  structure-level halves (see §5). *Origin: ch2 plan §1.*
* **§2.5 decision-versus-search** (Theorem 2.18). *Origin: ch2 plan §1.*
* **Parsimonious and Levin reductions** ([AB09] §2.3.6). *Origin: ch2 plan §1.*
* **Ex 2.6, the universal NDTM** — Chapter 3's tool. *Origin: ch2 plan §1.*
* **Ex 2.30, Berman's theorem.** *Origin: ch2 plan §1.*
* **General Boolean formulas** — `TAUTOLOGY` is deliberately stated on the
  documented DNF fragment; a general-formula carrier (AST, evaluation,
  serialization) is new work, and any future general `TAUTOLOGY` must not be
  silently identified with the fragment. *Origin: ch2 phase-3/4 audits.*
* **`MathlibBridge` poly-time upgrade** (open lever): `bridgeTM` costs O(1)
  native steps per TM2 operation, so a Mathlib `TM2ComputableInPolyTime`
  certificate would transfer. (The Chapter-6 bridges were built on native
  machines without it; see §3.)
  *Origin: ch2 plan decision log ("revisit at phase 3" — still open).*
* **Oracle complexity classes** (Chapter 3): `Oracle.lean` has the raw model
  and both lockstep embeddings, audited; the class layer, the
  persistent-vs-auto-erased query-tape statement (polynomial overhead only —
  constant overhead provably impossible), and relativization (Baker-Gill-
  Solovay) are future Chapter-3 work. *Origin: ch1 plan §5 phase-2 notes;
  session assessment 2026-09-18.*

### Chapter 6 (Arora–Barak §§6.1–6.5): what is proved, and what remains

The machine-facing Chapter-6 bridge theorems this section used to list are all
**proved, sorry-free** (headline `#print axioms`: `propext`, `Classical.choice`,
`Quot.sound` only), over the book's DAG model `BoolCircuit.DAGCircuit`:

* Thm 6.6 `P ⊆ P/poly` — `Complexity.P_subset_PPoly` (oblivious tableau,
  `CircuitComplexity/PSubsetPPoly*.lean`); `P ⊊ P/poly` (p. 110) —
  `Complexity.P_ssubset_PPoly`, with the machine-model `UHALT`
  (`Complexity.UHALT_not_mem_P`, `UHaltMachine.lean`).
* Lem 6.10 / 6.11 — `BoolCircuit.dagCktSatLang_NPComplete`,
  `BoolCircuit.dagCktSatLang_polyTimeReducible_SAT3`, and Cook–Levin via circuits
  `Complexity.SAT3_NPHard_viaCircuits` (the p. 111 alternative proof); CKT-SAT `∈ NP` is
  `BoolCircuit.dagCktSatLang_mem_NP`, circuit evaluation `BoolCircuit.CVAL_mem_P`.
* Remark 6.7, Thm 6.13 — `Complexity.tabFamily_isPUniform`,
  `Language.mem_P_iff_exists_isPUniform`; Def 6.14, Thm 6.15 and the logspace half of
  Remark 6.7 — `Complexity.tabFamily_isLogspaceUniform`,
  `Language.mem_P_iff_exists_isLogspaceUniform`.
* Def 6.16, Ex 6.17, Thm 6.18 — `Complexity.DTIMEAdvice`,
  `Complexity.mem_PAdvicePoly_of_le_allOnes` (with the named `UHALT` instances
  `Complexity.UHALT_mem_DTIMEAdvice_one`, `Complexity.UHALT_mem_PAdvicePoly`),
  `Complexity.PPoly_eq_PAdvicePoly`, and the book's advice length `n^d` literally:
  `Complexity.PPoly_eq_iUnion_DTIMEAdvice_pow` (`P/poly = ⋃ DTIME(n^c + 1)/n^d`,
  `PAdviceSubsetPPoly.lean`). The time `n^c + 1` is forced, not cosmetic: the literal
  `DTIME(n^c)/a` is empty for `c ≥ 1` (`Complexity.DTIMEAdvice_pow_eq_empty`, zero steps
  on the empty input), so the literal union collapses to constant time
  (`Complexity.iUnion_DTIMEAdvice_pow_eq`); also
  `DTIME(T)/0 = DTIME(T)` for `T(n) ≥ n + 1` (`Complexity.DTIMEAdvice_zero_eq_DTIME`)
  and `⋃_c DTIME(n^c + 1)/0 = P` (`Complexity.iUnion_DTIMEAdvice_zero_eq_P`).
* Thm 6.19 Karp–Lipton — `Complexity.PH_eq_SigmaP_two_of_NP_subset_PPoly`; Thm 6.20
  Meyer — `Complexity.EXP_eq_SigmaP_two_of_EXP_subset_PPoly`, and the p. 115 corollary
  `Complexity.not_EXP_subset_PPoly_of_P_eq_NP`.
* Thm 6.21 — `BoolCircuit.exists_hard_function_dag` (book bound `2ⁿ/(10n)`), with the
  p. 115 probabilistic form `BoolCircuit.prob_computableDAG_shannon_le`, proved by the
  book's steps: `BoolCircuit.prob_eval_eq_apply` (`Pr[C(x) = f(x)] = 1/2`),
  `BoolCircuit.prob_computes` / `prob_computes_eq_prod` (`Pr[C computes f] = 2^{-2ⁿ}`, the
  product of the per-input probabilities) and the union bound `BoolCircuit.prob_computableDAG_le_count`
  (`ShannonProbabilistic.lean`).
* p. 108 circuit remarks — Lupanov `O(2ⁿ/n)` (`BoolCircuit.exists_dagCircuit_faninTwo_size_le_div`,
  `Lupanov.lean`); fan-out two (`DAGCircuit.exists_fanoutTwo`, `FanOut.lean`), including
  `¬¬v` buffers under the literal fan-in-exactly-two convention
  (`DAGCircuit.exists_fanoutTwo_notNot`, `5S`; `DAGCircuit.IsStrict.exists_fanoutTwo`,
  `20S`; `StrictFanOut.lean`); the literal Def 6.1 (`DAGCircuit.IsStrict`,
  `Language.inPPoly_iff_inStrictPPoly`); formulas as fan-out-one circuits, both ways
  (`TreeCircuit.toDAG_fanout_le_one`, `DAGCircuit.exists_treeCircuit_of_fanout_le_one`,
  `FormulaFanOut.lean`).
* Def 6.5's literal `⋃_c SIZE(n^c)` — empty (`Language.not_inSIZE_pow`); `P/poly` is the
  literal bound from length 2 on (`Language.inPPoly_iff_eventually`, `PPoly.lean`).

Remaining Chapter-6 items (each documented as a divergence in its file):

* **Thm 6.22, the size hierarchy over the book's `SIZE`** — only the tree-circuit
  analogue exists (`BoolCircuit.treeSize_ssubset`, `Hierarchy.lean`); the DAG version
  needs a DAG-native padding/counting argument on top of `exists_hard_function_dag`.
* **Tree-circuit CKT-SAT** (`Encoding.lean`, `CircuitSat.lean`) carries no `≤ₚ` claim —
  only equisatisfiability and a clause count; the book's Lem 6.11 is the DAG version
  above.
* The `O(T log T)` oblivious simulation (Remark 1.7) is Chapter 1's Phase 5 above; the
  circuits of `P ⊆ P/poly` are quadratic instead, which suffices for every Chapter-6 use.

---

## 4. Decisions pending (user)

* **Chapter-6 integration** — the Chapter-6 theorem surface is complete up to the
  items listed in §3 (Chapter 6); resolved in part: ch6 was merged into the
  campaign branch (`a2a2728b`), and the circuit nomenclature pass agreed
  with the ch6 authors landed 2026-10-01 in three commits: `HasLogDepth`
  → `HasPolylogDepth`; the `ACP` namespace unbundled (generic circuit
  material → `BoolCircuit`, the Razborov–Smolensky chain →
  `RazborovSmolensky`, `AC_GateOps` → `BoolCircuit.stdGateOps`);
  `FeedForwardCircuit.lean` relocated to
  `Complexity/CircuitComplexity/FeedForward.lean` (since renamed
  `LayeredCircuit.lean`), so `Complexity` no
  longer imports from `BooleanAnalysis` (verification:
  `scripts/circuit_module_order.txt`, the 23-module dependency sweep).
  Still open: their `Formulas.lean` defines `Literal`/`Term`/`DNF`/`CNF`
  at the **root namespace** (policy §1 leak; future ambiguity against
  `Std.Sat.CNF`/`Std.Sat.Literal`) — namespace choice deliberately
  deferred (user: `BoolCircuit` is not the right home for formulas);
  three CNF ecosystems coexist (their width-indexed `CNF n`, legacy
  `NPReductions.CNFFormula V`, the audited `Std.Sat.CNF ℕ`) with three
  SAT→3SAT artifacts; `UHalt.lean` introduces a **second computability
  framework** (Mathlib `ComputablePred` vs. the campaign's quarantine and
  its own `HALT_not_computable`) — the machine-model counterpart
  `UHaltMachine.lean` (`Complexity.UHALT_not_mem_P`) now carries `P ⊊ P/poly`,
  so `UHalt.lean` is a parallel statement, not a dependency; the merged circuit
  surface **passed the external audit protocol**
  2026-10-02 (three rounds, 0 blockers throughout;
  `audits/ch6-circuits-resolutions.md`, CLOSED) — campaign statements may
  cite its definitions, subject to the recorded divergences (the audit's
  interface notes 12–15 in `audits/ch6-circuits-findings.md` were followed by the
  bridge theorems now listed in §3). The dangling `ch6/PLAN.md` references were repointed
  here in the round-1 repairs. Loose ends for the colleagues:
  `Basic.lean` at 691 lines (> 600 target); and the audit's sweep logs
  show the **LMN tree is not sorry-free** (five `sorry` warnings across
  `CircuitCompression`, `IterativeReduction`, `Depth3Switching`,
  `CircuitTreeManip`) — outside the audited surface, flagged for its
  authors.
* **Fill-campaign start** (§2) — on hold by the same instruction.
* **Disposition of the three §1 questions** — CH1-Q1, CH1-Q2, CH2-Q1.
* **`TCSlib.Tactics` blueprint exclusion** — 92 metaprogramming-scaffolding
  declarations deliberately excluded from the dataset; user may override.
  *Origin: ch1 blueprint-extraction row.*
* **Fate of `AroraBarakChapter1Plan.md` at merge** — graduate to `docs/` vs.
  superseded by the blueprint. *Origin: ch1 decision log (final row).*

---

## 5. Repository housekeeping

* **Legacy `Complexity/NPReductions/*`**: 14 pre-existing style-lint FAILs
  (missing docstrings/References), outside the campaign surface; eventual
  fate coupled to the §3 retargeting idea. The ch6 branch adds (clean,
  additive) counting lemmas to `SATTo3SAT.lean`.
* **Dependabot**: 88 alerts on the repository default branch (2 critical,
  16 high) — repo-level, unrelated to this branch's content.
* **`AGENTS.md` / `.claude/CLAUDE.md`** partially superseded by campaign
  practice (`workflow.md` §7 records the boundary): the `lean_proof/`-based
  flow and the LeanInfoView-only verification guidance predate the gate
  script; align or annotate eventually.
* **`audits/TEMPLATE.md`** predates the evolved pack format (attestation
  evidence separation, bundle conventions); refresh before the next fresh
  campaign starts from it.
* **Statements-only package split (idea; no near-term action):** a
  `concepts`/`proofs`-style two-package layout — frozen statement surfaces
  compiled without proof code, importable by downstream chapters — would
  mechanize the statement-freeze discipline the campaign currently enforces
  by protocol (statement gates, briefs, audit packs). Observed in external
  prior art: Lax Archive lax-429075/lax-434930 (Bonnet, Cook–Levin on Lean
  4.33; examined 2026-10-05, scratchpad-only, Apache-2.0, non-binding, never
  imported), where each claimed result is an `axiom` in a statements package
  and a platform replay checks the proof network closes. Composes with the
  §2 D7 internal-namespace visibility proposal; revisit no earlier than
  that proposal, if at all. *Origin: prior-art comparison, 2026-10-05.*
* **`HANDOFF.md`** — the have→lemma extractor campaign's own tracking
  document; deliberately *not* absorbed here.

## ===== audits/ch7-fill-pack.md =====

# External audit pack — Chapter 7, fill gate (the block-query loop and the closed machine surface)

Audited Lean surface: the **merged tree** on `complexity/arora-barak-ch3-4` at
`49658bb6`, where PR #11 and a follow-up merge brought the Chapter-7 campaign. The
summit landed at `d450376` on `complexity/arora-barak-ch7`; the closure sweep and this
pack's first draft sit on top of it at `0c22ae33`. Every ch7 module is byte-identical
on the merged tree to `0c22ae33`, except `ClassNP/PClosure.lean`, which also carries a
comment-only correction from the ch3-4 branch (attestation 1). This revision of the
pack (maintainer, 2026-10-10) re-runs attestations 1, 2, 4 and 5 on the merged tree
and adds question 7 (duplication). This is the **fill-audit gate of the Chapter 7
campaign**: the statement surface was audited and CLOSED at ch7-phase1
(`audits/ch7-phase1-{pack,findings,resolutions}.md`, zero blockers / zero majors at
`76fe2f46`); this gate covers everything the fill campaign **added** to the trusted
surface while discharging the last three machine closures. Record findings in
`audits/ch7-fill-findings.md`.

> **Provenance — read first.** After the phase-1 gate closed, the three remaining
> `PolyTimeModel` closures (`closedUnderMajority`/`closedUnderAny`/`closedUnderShiftOr`)
> were reduced to one chapter-neutral primitive — *`P` is closed under running a
> `P`-decider on polynomially many fixed-size blocks with OR / strict-majority /
> XOR-then-OR aggregation* (`briefs/ch7-pclosure-blocks.md`) — and that primitive was
> built and proved in this repository by the maintainer's agent. **No statement of the
> phase-1 audited surface changed** (attestation 1). What is new, and what you are
> auditing, is the surface the primitive added: two machine-infrastructure modules,
> three `P`-closure modules, and three additive headline lemmas in the frozen
> Chapter-1/2 file `ClassNP/PClosure.lean`.
>
> The product under audit is **definitions and theorem statements** — not tactic
> scripts, which Lean checks. Everything in scope is *proved*; remember that a
> wrong-but-proved statement is the worst outcome, so blind-restate each definition
> and statement before reading its docstring.

Source text: [AB09] ch. 7 (2007 web draft; reference pair under
`blueprint/src/references/`): the implicit machine-closure steps of Theorem 7.8
(`ZPP = RP ∩ coRP`: the OR amplifier), Theorem 7.10/Corollary 7.11 and Theorem 7.17
(majority repetition), and Theorem 7.18 (the XOR-shift OR of the Sipser–Gács proof).
The loop host itself is §1.2-folklore machine engineering ("simulate the machine on
each block"), audited for model fidelity rather than against a numbered theorem.

## Repository-side attestations (maintainer, remote machine — verify or challenge)

1. **Statement freeze / drift.** `audits/evidence/ch7/ch7-fill-drift-attestation.md`:
   of the 13 phase-1 modules, 12 are comment-stripped **identical** to the audited
   baseline `76fe2f46`; `Randomized/PolyTimeModel.lean` has the **same 20
   declarations, same order, zero signatures changed, import block byte-identical** —
   only the three `sorry` bodies became proofs. The frozen `ClassNP/PClosure.lean`
   gained exactly the three headline lemmas (additive; baseline sequence is an
   ordered prefix; one import added). No other pre-existing `.lean` file differs.
   **On the merged tree**, `PClosure.lean` additionally carries the ch3-4 branch's
   P0-gate correction (finding 5) to the docstrings of `lenEq_mem_P` and
   `lenLe_mem_P`. It is comment-stripped identical to `0c22ae33`. "No other file
   differs" holds relative to the ch7 branch. On the merged tree, the rest of
   `TCSlib/` is the ch3-4 campaign's own audited material and lies outside this gate.
2. **Elaboration.** Full **19-module** fresh-olean sweep (the 13 phase-1 modules plus
   the six fill modules, `scripts/ab_ch7_module_order.txt` order) via
   `scripts/lean_check_tree.sh` (Lean 4.25.0, Mathlib at the branch pin; **`lake
   build` not used** — banned on the campaign branch): every module exits 0, emits a
   fresh `.olean`, **zero `error:` lines** (`audits/logs/ch7-fill-sweep.log`).
   **Re-run on the merged tree** with the four touched facades (`Expanders`,
   `Randomized`, `ClassNP`, `TuringMachine`) appended: 23/23 modules exit 0, zero
   `error:` lines (`audits/logs/ch7-fill-merged-sweep.log`).
3. **Admissions inventory.** Exactly **1** `declaration uses 'sorry'` warning
   tree-wide: `Expanders/Chernoff.lean` — `walk_visits_concentration` (Theorem 7.41),
   **intentional and permanent** (book omits the proof; CH7-Q3, confirmed at
   phase-1). The fill campaign closed every other admission.
4. **Axiom hygiene (anti-tamper).** `audits/logs/ch7-fill-axioms.log`: 36 headline
   prints on the fresh olean tree — the Tier A/B results, all eight `polyTimeModel`
   closure/instantiation theorems, `adleman_polyTime`, `sipser_gacs_polyTime`,
   `zpp_eq_rp_inter_corp_polyTime`, the three `mem_P_of_block*` lemmas, the three
   block tests, `polyTimeComputable_emitIter`/`_xorD`, the slice lemmas, and
   `FinTM.exists_emitIterTM` — 35 print exactly
   `[propext, Classical.choice, Quot.sound]`; the single exception is the
   intentional Theorem 7.41 stub, which prints `sorryAx` as expected. **Re-run on
   the merged tree**: the 36 print lines are byte-identical
   (`audits/logs/ch7-fill-merged-axioms.log`).
5. **Policy conformance.** `audits/logs/ch7-fill-lint.log` over the 19-module
   surface: the fill modules and the closure's documentation sweep leave **one**
   standing finding — `Randomized/Classes.lean` is 1,328 lines (the documentation
   sweep grew it from the 1,266 lines first stated here; > 1,000, policy
   "must split"). Splitting a frozen, audited module is deliberately **not** done
   unilaterally at closure; the proposed disposition (split the counting layer out
   of `Classes.lean` post-gate, statements unchanged) is submitted to this round for
   approval. Flag if you believe the size bears on fidelity. **Re-run on the merged
   tree** (`audits/logs/ch7-fill-merged-lint.log`, five directories): 0 FAIL. This is
   the only WARN on the ch7 surface.

## What is under audit (the new trusted surface)

| Module | Key definitions | Key statements (all proved) |
|---|---|---|
| `TuringMachine/Build/EmitIterEmbed.lean` (18 public) | `SafeRun` (run avoiding a state strictly inside), `padAction`/`embedCfg` (tape-padding, state-injecting embedding of an `m`-tape module into a `k`-tape host) | `runFrom_output_prefix` (output-prefix commutation), `runFrom_output_extends` (append-only output), `embed_step`/`embed_run` (module runs embed step-for-step on live, off-exit states), `control_step`/`control_step'` |
| `TuringMachine/Build/EmitIterBody.lean` (1 public) | the body machine, copier and round lemmas are private | `FinTM.exists_emitIterTM`: machines for a step `g` and a chunk `e` within `C·(n+1)^c` budgets, plus an orbit length envelope `∀ w i, |g^[i] w| ≤ b·(|w|+1)^l`, yield one machine computing `w ↦ (range (a'·(|w|+1)^k' + 1)).flatMap (fun i => e (g^[i] w))` in `C·(n+1)^c` normal form |
| `ClassNP/PolyTimeBlockLoop.lean` (22 public) | `sliceTakeAt`/`sliceDropAt` (keep the first pair component, take/drop `a·(n+1)^k` of the second), `xorD` (truncating bitwise XOR of a pair's components), `blockDone`/`isNilB` (loop-state conventions) | `polyTimeComputable_emitIter` (the `FP`-level loop, consuming `exists_emitIterTM`), `polyTimeComputable_xorD`, the slice/`take1`/`headD`/`tail`/`isNil`/`or`/`not` `FP` helpers, `flatMap_range_eq_single`, `length_pair_components_le` |
| `ClassNP/PolyTimeBlockTests.lean` (3 public) | `blockAt a k z i` — the `i`-th length-`a·(n+1)^k` block of `pairSndD z`, `n = ‖pairFstD z‖` | `polyTimeComputable_blockAnyTest`, `polyTimeComputable_blockXorAnyTest` — the one-bit OR / XOR-then-OR aggregated block tests of a `P` indicator are poly-time |
| `ClassNP/PolyTimeBlockMajority.lean` (1 public) | private vote-counter loop | `polyTimeComputable_blockMajorityTest` — the strict-majority aggregated test is poly-time |
| `ClassNP/PClosure.lean` (**+3**, frozen file) | — | `mem_P_of_blockAny` (`{z \| ∃ i < a'·(n+1)^k', pairEncode (pairFstD z) (blockAt a k z i) ∈ V} ∈ P`), `mem_P_of_blockMajority` (strict majority of block indicators, `a'·(n+1)^k' < 2·countP`), `mem_P_of_blockXorAny` (nested pair `⟨⟨x,u⟩,v⟩`; blocks of `u` XORed with `v`, truncating) |

Consumption (already audited statements, proofs now closed): the three
`PolyTimeModel` closures reduce to the three headliners exactly as
`closedUnderRace` reduced to the slice primitives at phase-1.

## Known deviations and design choices (verify benign; flag others)

* **Truncating XOR.** `xorD` and the `mem_P_of_blockXorAny` statement use
  `List.zipWith xor` semantics (truncate to the shorter word) — the convention the
  phase-1 audit already confirmed for `shiftOrVerifier` (phase-1 finding 1 sweep).
* **The brief's sketch was wrong and is superseded.** `briefs/ch7-pclosure-blocks.md`
  sketched `xorD` as a one-register counter program; a one-pass register machine
  cannot pair bits across the separator. The landed `xorD` is instead a customer of
  the emit-iteration loop (one XOR bit per round). The *statement* is as the brief
  proposed; only the construction route changed.
* **Orbit-only envelope.** `polyTimeComputable_emitIter` demands
  `∀ w i, (g^[i] w).length ≤ b·(w.length+1)^l` — over **all** inputs and iteration
  counts, not only scheduled rounds. Customers discharge it with absorbing done
  states. (An earlier draft hypothesis quantifying over all state words was
  undischargeable and was replaced before any consumer landed; the statement was
  never part of an audited surface.)
* **Unary aggregation state.** Vote counts and countdowns are unary words inside the
  `pairEncode`d loop state; polynomial budgets enter only through
  `polyTimeComputable_polyUnary`-style unary schedules (the Argument-A discipline).
* **`blockAt`'s length source.** The block length and count schedules are evaluated
  at `(pairFstD z).length` — for the nested `blockXorAny` surface, at
  `(pairFstD (pairFstD w)).length`, i.e. the *inner* first component `x`, matching
  `shiftOrVerifier`'s `p x.length`.

## Specific questions for this gate

1. **Block fidelity.** Does `blockAt a k z i = ((pairSndD z).drop (i·q)).take q`,
   `q = a·(n+1)^k` at `n = ‖pairFstD z‖`, match the block conventions of
   `anyVerifier`/`majorityVerifier` (blocks of the random string at `p = polyLen a k`)
   and — through `blockAt a k (pairFstD w) i` with the *nested* length source — of
   `shiftOrVerifier`? Check off-by-one in `i·q`, the `+1` in the round count
   `a'·(n+1)^k' + 1`, and the degenerate schedules `a' = 0`, `a = 0`, `k = k' = 0`.
2. **Headline-statement fidelity.** Are the three `mem_P_of_block*` sets precisely
   the `some true`-sets of the three verifier constructions on `pairEncode`d inputs
   (given the efficiency witness's iff), so that complementation gives the
   `some false`-sets? Pay attention to the strict majority (`K < 2·count`, no
   off-by-one at even/odd `K`) and to malformed pairs (`pairFstD z = []` conventions).
3. **The loop statement.** Is `exists_emitIterTM`'s computed function — concatenation
   of `e (g^[i] w)` over `i ∈ range (a'·(|w|+1)^k' + 1)` — the right general form,
   and is its budget genuinely `C·(n+1)^c` (no hidden dependence on the orbit beyond
   the envelope)? Is the envelope hypothesis non-vacuous and dischargeable (the three
   customers and `xorD` discharge it; try to construct a natural customer that
   cannot)?
4. **Embedding soundness as stated.** Do `padAction`/`embedCfg` state the intended
   "module untouched on the padding tapes" semantics (no tape aliasing, inputs read
   through `Fin.castLE`, output preserved), and do `embed_step`/`embed_run`'s
   hypotheses (live states, off-exit, host transition equals padded module
   transition) match how a dispatch-style host actually behaves at its exit state?
5. **Output-prefix commutation.** Is `runFrom_output_prefix` the correct statement
   (the table never reads the output; output is append-only, per
   `runFrom_output_extends`), and is it strong enough for the round assembly's
   claim that the install call's own output stays empty?
6. **`PClosure` extension safety.** Do the three additions interact with the
   existing closure calculus only additively (no instance/namespace capture, no
   changed behavior of the pre-existing 13 declarations)?
7. **Duplication (this repository's `audits/TEMPLATE.md` failure mode 5, attached).**
   Screen the surface for duplicated proved material and verify the maintainer
   pre-screen (`audits/evidence/ch7/ch7-fill-duplication-screen.md`, attached). It
   reports no copies of pre-existing repository material. It does report one family of
   renamed re-proofs inside the stack: the OR, XOR and majority loops each carry their
   own copy of the same orbit, length and init lemmas, which puts
   `PolyTimeBlockMajority` at 4 of 14 declarations (28.6%), over this repository's
   one-fifth threshold. Report each confirmed copy family at **major** with the
   proposed fix "human acknowledgment required"; the gate may not close over them
   until the human maintainer accepts the debt and names its resolution. The family
   above is **already acknowledged** (the human maintainer, 2026-10-10: it is resolved
   in this repository's 12.2c refactor, as one generic lemma set with statements
   unchanged). Confirm its extent; it then does not hold the gate, though any further
   family you find does. Say whether
   the screen missed any copy, including re-derivations it cannot detect. Separately,
   compare the public `EmitIterEmbed` embedding layer (`padAction`/`embedCfg`/
   `embed_step`/`embed_run`) with the §12 `Build/Embed.lean` layer (attached). Report
   the overlap as facts, meaning what one layer states that the other does not, and do
   not propose a merge of the two; that merge is already scheduled in this
   repository's per-theme refactor (12.2c).

## Brief for the auditor

As at phase-1: audit the trusted surface (definitions and statements); do not review
tactic scripts. Hunt infidelity, trivialization, and missing hypotheses.
Blind-restate every definition before reading its docstring; attempt ≥3 adversarial
instantiations (suggested: `a' = 0`; `z` a malformed pair; `V = ∅` and `V = univ`;
`cE = cG = 0` budgets; an `e` emitting multiple bits per round). No blanket
approval; justify an empty table with the restatements. The gate closes only on a
round reporting **zero blockers and zero majors**.

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide: **blocker** = downstream work would build on a wrong statement;
**major** = statement fixable but materially misleading; **minor** = edge case or
naming/attribution; **note** = observation.

## ===== audits/ch7-fill-findings.md =====

# Chapter 7 fill-gate audit findings

**Result: 0 blockers, 0 majors, 2 minors, 2 notes.** I found no block-index, majority-threshold, nested-length, or missing-hypothesis defect in the added formal statements. The two minors concern inaccurate descriptions of the delivered implementation/API. This is a bounded statement audit, not a blanket approval of the repository, the earlier statement gate, or the execution attestations.

Audited artifact: the supplied `ch7-fill-bundle.md`, SHA-256 `00be8b1d71cf1e9512438c2b5ddfdf0987753c09e70ef4249b0636f61593e4b2`. All nine bundled Lean files match [a-gupte/tcslib at `0c22ae33a2321ea027261efa3608ad952b3cd9a5`](https://github.com/a-gupte/tcslib/tree/0c22ae33a2321ea027261efa3608ad952b3cd9a5), after removing the bundle's fences. Historical comparisons used baseline `76fe2f46333c9b1006c6dd8c8c27d55c76586024`.

I consulted Arora–Barak's January 2007 Chapter 7 draft, specifically Theorems 7.8, 7.10, 7.17, 7.18 and Corollary 7.11. The corresponding [author-hosted chapter](https://theory.cs.princeton.edu/complexity/bppchap.pdf) identifies the source. Theorem 7.8's proof is left as an exercise; the present OR machinery supplies an implicit closure used by the formalization. Majority repetition and the XOR-shift membership test have the intended chapter-level meanings. Probability estimates and previously accepted deviations were not reopened.

**Method.** I extracted declarations with comments removed and theorem proof bodies omitted; recorded independent restatements; then compared the docstrings. The audit pack's descriptions had necessarily been read first. I examined definitions and contracts, including private state definitions needed to understand the public functions, without reviewing tactic proofs. Questions 1–2 were checked before 3–6. Executable checks below are independent Python models of the definitions, not Lean execution or substitutes for proof.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | minor | `ClassNP/PolyTimeBlockLoop.lean` · module `Main results`, `polyTimeComputable_xorD` | The module summary still attributes XOR to the abandoned one-pass counter-program construction. | It says “polynomial-time (a one-pass counter program).” The delivered state definitions `xorPairStep`/`xorPairEmit`, the theorem's own explanation, and the pack describe the emit-iteration construction. | Replace that parenthetical with “via the emit-iteration loop.” No formal statement change. |
| 2 | minor | `TuringMachine/Build/EmitIterEmbed.lean` · module `Main results`; `audits/ch7-fill-pack.md` · scope row | Two advertised reusable embedding lemmas are actually private in another module. | `control_step` and `control_step'` are declared `private theorem` in `EmitIterBody.lean`; neither is a public declaration of `EmitIterEmbed.lean`. They cannot be consumed under the advertised public names `Turing.control_step` and `Turing.control_step'`. | Correct the module summary and pack inventory to describe private body helpers. If a public API is intended, explicitly export/move them and recheck the affected modules. |
| 3 | note | `ClassNP/PClosure.lean` · all three `mem_P_of_block*` | These languages are total extensions through default decoding, not languages that reject malformed encodings. This is compatible with `polyTimeModel`. | With `a'=1`, `k'=0`, and `V=univ`, the malformed word `[]` belongs to every headline language. Queries are re-encoded valid pairs; the efficiency witness constrains precisely those queries. | Keep the statements. State explicitly that exact verifier agreement is on encoded inputs, with default-decoding extensions elsewhere. |
| 4 | note | `EmitIterBody.lean` · `FinTM.exists_emitIterTM`; `PolyTimeBlockLoop.lean` · `polyTimeComputable_emitIter` | The all-iterations orbit bound is sufficient and usable here, but excludes some natural polynomially scheduled computations. | For `g s = s ++ [false]`, `\|g^[i] w\|=\|w\|+i`; no fixed `b,l` bounds every `i`. Nevertheless polynomially many such steps, even emitting each state, take polynomial time. | Preserve the explicit hypothesis. A future generalization can bound only the scheduled orbit, including the final state update; it is unnecessary for these customers. |

**Question 1 — block fidelity.**

Use the pack's `q = a·(n+1)^k` and `K = a'·(n+1)^k'`. On `z = pairEncode x r`, `n=|x|` and the definition reduces exactly to

\[
\operatorname{blockAt}\ a\ k\ (\operatorname{pairEncode}\ x\ r)\ i
= (r.\operatorname{drop}(i q)).\operatorname{take}(q).
\]

Thus `i=0` starts at the first symbol, adjacent full blocks meet at the correct boundary, and `range K` contains exactly indices `0,…,K−1`. Short final blocks remain short; blocks beyond the end are empty; surplus input after the scheduled blocks is ignored. No hidden padding or length rejection occurs. This is the identical slicing in `anyVerifier` and `majorityVerifier`.

For `w = pairEncode (pairEncode x u) v`, `pairFstD w = pairEncode x u`, so `blockAt a k (pairFstD w) i` slices `u` with `q` scheduled at `|x|`. The repetition count also uses `pairFstD (pairFstD w) = x`. It does not use the length of the encoded inner pair, of `u`, or of `v`.

The generic loop emits at indices `0,…,R`, where `R=a'·(|w|+1)^k'`. A block customer first constructs an initialized state containing a unary countdown of length `K`. For its orbit, the chunk is empty for `i<K`, the singleton aggregate is emitted at `i=K`, and the state becomes `blockDone` at `i=K+1`, after which chunks are empty. The generic bound is evaluated at the initialized state's length, which dominates `n`, so it covers the emission at `K` and can include harmless later rounds. There are exactly `K` decider queries. The `+1` permits the final emission; it does not add a vote.

**Definition restatements, recorded before reading the corresponding Lean docstrings:**

| Definition | Independent meaning |
|---|---|
| `polyLen a k` | The explicit schedule `n ↦ a·(n+1)^k`; no arbitrary bounded function is accepted in its place. |
| `boolVerifier M` | Return `some (M x r)` on every input; never return `none`. |
| `anyVerifier M p k` | OR `M` on the `k(\|x\|)` consecutive, possibly short or empty, length-`p(\|x\|)` slices of `r`. |
| `majorityVerifier M p k` | Count true answers on the same slices and test `k(\|x\|) < 2·votes`; a tie rejects. |
| `shiftOrVerifier M p k` | Slice `u` using schedules at `\|x\|`; zip-XOR each slice with `v`, truncating to their minimum length; OR the `M x` answers. This definition returns `Bool`. |
| `polyTimeModel` | Two existential languages in `P` agree with an option-valued verifier's true/false answers on every genuine pair encoding. The two-witness version uses one language and left-nested encoding. Malformed-word membership is unconstrained. |
| `ClosedUnderMajority`, `ClosedUnderAny` | For every efficient Boolean verifier and all four fixed natural schedule parameters, the specified aggregated Boolean verifier is efficient. |
| `ClosedUnderShiftOr` | Under the same premise and schedule quantification, the three-input shifted-OR Boolean predicate has an efficient nested-pair language. |
| `blockAt` | Default-decode, drop `i·q` from the second component, then take `q`, with `q` determined by the first component's length. |
| `sliceTakeAt`, `sliceDropAt` | Re-encode the decoded first component with, respectively, the `q`-prefix or the remainder after dropping `q` from the decoded second component. |
| `blockDone` | `pairEncode [] []`, the two-bit separator word, rather than the empty word. |
| `isNilB` | The Boolean test for the empty list. |
| `xorD` | `zipWith xor` of the two default-decoded components. Both projections of an invalid pair are empty, so invalid pairs produce `[]`. |
| Private `xorPairStep` | Drop one symbol from each decoded component and re-encode them. |
| Private `xorPairEmit` | Emit the XOR of the two heads if both components are nonempty; otherwise emit nothing. |
| Private `anyInit` | Initialize a one-bit false accumulator, a unary countdown of length `K`, and the normalized pair of input and remaining randomness. |
| Private `anyStep` | An empty accumulator or countdown goes to `blockDone`. Otherwise test the next block, replace the accumulator by `[true]` on success, retain it on failure, remove one countdown token, and drop one block. |
| Private `anyEmit` | Emit the nonempty accumulator only when the countdown is empty. On initialized orbits it is one bit; on arbitrary states it can be a longer word. |
| Private `xorInit` | Initialize `[false]`, a countdown scheduled at the inner `\|x\|`, and payload `pairEncode v (pairEncode x u)`. |
| Private `xorStep` | Use the OR guards and update, but query `pairEncode x (zipWith xor v block)`; keep `v` and `x`, advance `u`, and decrement the countdown. |
| Private `majInit` | Initialize marker `[true]`, a unary countdown, empty yes/no unary counters, and the normalized input/randomness pair. |
| Private `majStep` | Use the same termination guards; increment exactly the yes or no counter according to the next query; decrement the countdown and advance one block. |
| Private `majEmit` | At countdown exhaustion with a live marker, emit the negation of `yes.length ≤ no.length`, hence strict comparison `yes > no`. Otherwise emit nothing. |

The imported pairing conventions were also checked: `pairEncode x r` duplicates each bit of `x`, appends `[false,true]`, then appends `r`. `pairDecode` consumes equal bit-pairs until that separator and fails on any other pattern. `pairFstD` and `pairSndD` map decoding failure to `[]`. In particular, an empty first projection alone does not imply malformed input: genuine encodings with empty first component also have that projection.

**Question 2 — headline-statement fidelity.**

The three added theorems make these claims for every fixed `a,k,a',k'` and every `V ∈ P`:

| Headline | Independent statement restatement |
|---|---|
| `mem_P_of_blockAny` | The language of all words `z` for which some `i<K` satisfies `pairEncode (pairFstD z) (blockAt a k z i) ∈ V` belongs to `P`. |
| `mem_P_of_blockMajority` | The language of all words for which `K` is strictly less than twice the number of accepting block queries belongs to `P`; that count uses `MultiTapeTM.indicator V`. |
| `mem_P_of_blockXorAny` | Decode an outer pair and its first component; use the inner first component as `x`, inner second as `u`, and outer second as `v`. The language accepting some query `pairEncode x (zipWith xor v (blockAt a k (pairFstD w) i))`, with both schedules at `\|x\|`, belongs to `P`. |

Let `V` be the true-answer language in the efficiency witness for `boolVerifier M`. For every `x,r`, the witness gives `pairEncode x r ∈ V ↔ M x r = true`. Every individual block query is a genuine encoding, so its indicator equals the corresponding Boolean answer of `M`. Replacing indicators with those answers makes the first headline exactly `anyVerifier` and the second exactly `majorityVerifier` on `pairEncode x r`. Repeating the calculation with the three decoded components makes the third headline exactly `shiftOrVerifier` on `pairEncode (pairEncode x u) v`.

This needs no hypothesis on the lengths of `r,u,v`. In the book's equal-length shift setting, truncation disappears. On other inputs it agrees with the already audited verifier definition.

The majority state has yes-count equal to the number of successful queries and no-count equal to `K−yes`; both count exactly the scheduled queries, including queries on empty blocks. Consequently

\[
\neg(\mathrm{yes}\le K-\mathrm{yes})
\quad\Longleftrightarrow\quad K<2\,\mathrm{yes}.
\]

The required false-answer witness is the complement of the **final aggregate language**, because these Boolean verifiers never abort. Applying strict majority to `Vᶜ` would mishandle even ties: at one yes and one no, both strict majorities reject. The shifted-OR closure itself only needs a true-answer language through `EffTwoWitness`; a Boolean option-wrapping would permit the same complementation argument.

For malformed words the headline predicates evaluate the verifier on the default-decoded components. They therefore need not reject malformed encodings. This causes no dependence on the arbitrary values of the original witness language off valid encodings: every query to that language is re-encoded first. For a valid outer pair with an invalid inner pair, only the inner components become empty; the outer second component is retained as the XOR mask.

**Adversarial instantiations.** Here bit strings are written as lists of `0`/`1`, and each stated test is a total, polynomial-time predicate.

| Case | Predicted and checked behavior | Error exposed if present |
|---|---|---|
| `a'=0`, including `k'=0`, with `V=univ` | `K=0`. All three aggregate outputs are `[false]`; the initialized state emits once at index `0`, with zero decider queries. | An accidental first query or an empty-output result. |
| `a=0`, `K=3`; accept exactly the empty queried word | All three queries use an empty block; OR and majority accept. The XOR queries also remain empty for every mask. | Treating zero-size blocks as zero repetitions, or failing to advance the countdown. |
| `k=k'=0` | `q=a`, `K=a'`, independent of input length. No `0^0` ambiguity arises because the base is `n+1`. | Exponent-zero schedule errors. |
| `q=1,K=1,r=[1,0]`; accept `[1]` | OR and majority accept using the first bit. | One-based block indexing. |
| `q=1,K=2,r=[0,0,1]`; accept `[1]` | Both aggregates reject; the trailing `1` is outside the schedule. | An extra vote caused by the loop's `+1`. |
| `q=1,K=2,r=[1,0]`; accept `[1]` | OR accepts; majority rejects. At `K=3`, one true vote rejects and two accept. | Non-strict comparison or an off-by-one majority threshold. |
| `q=3,K=3,r=[0,1,1,1,0]`; accept only `[]` | Blocks are `[0,1,1]`, `[1,0]`, `[]`. OR accepts and majority rejects. | Padding, dropping a short block, or terminating queries when randomness ends. |
| `x=[0],u=[0,1,1,0],v=[1,1]`, `a=k=a'=k'=1`; accept `[0,1]` | `q=K=2`; shifted blocks are `[1,0]` and `[0,1]`, so shifted OR accepts. The encoded inner pair has length `8`, which would give a wrong schedule value `9`. The actual loop makes two queries and emits at index `2`. | Using the outer first-component length instead of inner `\|x\|`. |
| Same `x,u`, but `v=[1]`, `q=K=2`; accept `[0]` | Shifted words are `[1]` and `[0]`; shifted OR accepts. | Nontruncating XOR or a hidden equal-length requirement. |
| Malformed `z=[]` or `[1,0]`; `V=univ`, `a'=2,k'=1` | Both decoded components are empty; `K=2`. All headline predicates accept after two queries on canonical encodings of empty components. | An incorrect assumption that malformed inputs reject, or that `V` is queried on the original malformed word. |
| `w=pairEncode [1,0] [1,1]`, invalid inner pair; accept an empty randomness argument | Inner `x,u` become empty, the mask stays `[1,1]`, and each XOR query is empty. With `K=2`, shifted OR accepts. | Incorrect normalization of nested pairs. |
| `V=∅` and `V=univ` | For `∅`, every aggregate rejects. For `univ`, every aggregate accepts exactly when `K>0`, equivalently `a'>0`. | Vacuity or accidental positive-round assumptions. |

The executable model checked 6,696 raw-word/parameter/predicate combinations, 1,350 valid-pair cases, and 1,890 nested-pair cases: **29,808 aggregate checks**, all matching. Each comparison also checked that the output was a singleton, the sole emission occurred at `K`, and exactly `K` decider queries occurred. The raw words covered every bit string of length at most four; schedules included coefficients `0,1,2` and exponents `0,1`; the six predicates included always false, always true, emptiness, first bit, parity, and length equality. These finite checks support the explicit definitional arguments; they do not establish the general theorem.

**Question 3 — loop statement and budget.**

Blind restatement of `FinTM.exists_emitIterTM`: given fixed machines `G,E` computing the total word functions `g,e` within budgets `CG·(n+1)^cG` and `CE·(n+1)^cE`, and fixed naturals `a',k',b,l` satisfying the displayed bound for **every initial word and every iterate**, there exist one finite machine and fixed naturals `C,c` computing

\[
\bigl(\operatorname{range}(a'(|w|+1)^{k'}+1)\bigr)
.\operatorname{flatMap}\bigl(i\mapsto e(g^{[i]}w)\bigr)
\]

within `C·(n+1)^c`. `polyTimeComputable_emitIter` is its FP-level counterpart. No one-bit restriction is imposed on `e`, and no dependence of `C,c` on the individual input is permitted by the quantifier order.

The budget is substantively polynomial. For an orbit state of length at most `b·(n+1)^l`, the two given monomial budgets are polynomials in the original `n`. The one-symbol-per-step output model bounds the lengths of `g s` and `e s` by those budgets. The imported clean-call contracts bound a call by a constant times its original time, input length, output length, and one extra unit. Startup takes `3n+4` steps. Polynomial fuel computation and the imported loop bound `c·(T(n)+1)·(R(n)+2)` then preserve a polynomial bound. These are bounds on fixed contracts; testing whether a state belongs to an orbit is not a runtime operation.

The customers' stated envelopes genuinely cover arbitrary initial state words, not only well-formed initialized states: `2·(|w|+1)` for `anyStep` and `xorPairStep`, and `17·(|w|+1)` for `xorStep` and `majStep`. Countdown exhaustion and absorbing states bound the growing unary vote counters. Thus the hypothesis is nonvacuous for the actual clients.

Additional adversarial cases:

- With `g` the identity, `e s=[true,false]`, and `a'=2,k'=0`, the result consists of three two-bit chunks, `[true,false,true,false,true,false]`. With `a'=0`, the generic result is `e w`, whereas a zero-vote aggregate emits `[false]`. Both follow the specified inclusion of index zero.
- `cG=cE=0` is meaningful: take `g s=[]` and `e s=[true,false]`, with sufficiently large constant budgets and `b=l=1`. The initial state is covered and later states are empty. The constructed host can still have positive-degree overhead; the conclusion does not promise constant total time.
- Since the envelope includes `i=0`, choices `b=0` or `l=0` cannot satisfy it over all input lengths. These are unsatisfiable premises for those parameter choices, not a defect in the usable cases.
- The append-one-symbol function in finding 4 is a natural customer excluded by the all-iterations requirement, even though its scheduled computation is polynomial. The theorem is a sufficient closure principle with an explicit restriction.

**Question 4 — embedding and dispatch.**

| Definition or statement | Independent restatement and assessment |
|---|---|
| `SafeRun` | `runFrom c t=c'`, excluding the avoided state at every `j<t`. The start is included when `t>0`; the endpoint is excluded. There is no liveness requirement. |
| `SafeRun.zero`, `.cons`, `.trans` | Respectively: the zero-step identity; prepending a non-avoided step; concatenating two safe runs with additive durations. These use the same half-open interval. |
| `padAction` | Preserve input movement and optional output. Copy the first `m` tape actions, put no-write/zero-movement actions on all remaining tapes, and apply the supplied function to the optional next state. |
| `embedCfg` | Map the optional state; preserve input head/output; copy the first `m` work tapes and heads; initialize extra tapes blank with heads at zero. It does not carry arbitrary pre-existing padding-tape contents into its result. |
| `embedCfg_ofWords` | A word-initialized configuration embeds as the same word assignment padded with empty words. |
| `padAction_apply` | Applying the padded action to an embedded configuration gives the embedded module action result, even if the current host state was overwritten. |
| `embedCfg_workTapeSymbols` | Reading the initial tape indices through `Fin.castLE` recovers exactly the module's work symbols; changing the current state does not affect this. |
| `embedCfg_output` | Replacing the output field commutes with embedding. |
| `runFrom_one` | One step of `runFrom` equals `step`. |
| `runFrom_of_halted` | A `none` state freezes the whole configuration for every subsequent duration. |
| `state_isSome_of_runFrom` | If the endpoint state is live, every state at `j≤t` is live. |
| `embed_step` | Given a live module state `q` and a host state `b` whose transition is precisely the padded module transition on all symbol observations, one host step agrees with the embedded module step. |
| `embed_run` | If transitions match at every module state except `ex`, and the module is live and off `ex` at each `j<t`, then the entire `t`-step result embeds exactly. Arrival at `ex` or halting at the endpoint is allowed. |
| Private `control_step`, `control_step'` | A pure control transition changes only the state; with input movement, it additionally changes only the input head via `moveInputPos`. Their contracts are appropriate, but their advertised visibility is wrong: finding 2. |

`Fin.castLE` preserves the numerical tape index, so distinct module tapes remain distinct. Padding actions leave later tapes untouched. The two clean-call modules deliberately reuse the initial tape bank sequentially; their interface restores a canonical configuration before dispatch. The lemmas do not promise to preserve arbitrary nonblank padding configurations under `embedCfg` itself.

The parameter named `inject` is only a function; it has no `Function.Injective` hypothesis. That is harmless for the stated forward simulation: the exact transition-compatibility premise supplies what it needs. No theorem claims that state labels can be recovered. The actual body uses distinct constructors `callE` and `callG`, which do give disjoint tags.

The exit condition has the right endpoint convention. For a one-step module run reaching `ex`, only time zero must be off-exit; the theorem transports arrival at `ex`. Trying to transport the next host step would violate `hstate`, appropriately, because the host dispatches there instead of following the module transition. Entry-equals-exit is also handled: `anchor` and `gStart` execute the module's first action directly, and the remaining positive-time segment excludes the exit until its endpoint. The private `body_round` contract uses `0<t'<t`, unlike `SafeRun`'s startup interval `t'<t`; an anchor-to-anchor round cannot be a positive-duration `SafeRun` avoiding its starting anchor.

The remaining private definitions were independently restated as follows:

| Definition | Independent meaning |
|---|---|
| `BodyState` and its finite-type instance | Six distinct startup/dispatch states plus separately tagged emitter and installer states; the type is finite when the two machine state types are finite. |
| `emitIterBody` | Use `max Em.k Gm.k` tapes. Copy the input to tape zero, rewind that tape and the native input, enter `anchor`, call the emitter, dispatch its exit to `gStart`, call the installer, then return to `anchor`. Padding uses the initial tape indices. |
| `copyCfg` | In copy state, assign the first `i` input symbols to tape zero when that index exists; its head is at `i`, the native input head at `i+1`, other tapes blank, output empty. |
| `fullCfg` | Assign the full input to tape zero when present, with the specified control state, native input position, and tape-zero head; other tapes and output are empty. |

The positivity premises on the two clean-call tape counts prevent losing the state word through a zero-tape representation. For an empty native input, the startup contract still specifies four steps to reach the canonical anchor configuration; no positive-input-length assumption is hidden.

**Question 5 — output-prefix commutation.**

Blind restatement of `step_output_prefix` and `runFrom_output_prefix`: replacing initial output by `pre ++ c.output` prefixes the resulting output by the same `pre`, while every other resulting configuration field is unchanged. The latter holds for every natural duration. `runFrom_output_extends` separately states that final output is initial output followed by some suffix.

These are the appropriate contracts for an output-blind, append-only machine. They are strong enough for the assembly because the install-call contract ends in `Cfg.ofWords`, whose output is empty. Starting that call with an already-emitted chunk therefore ends with exactly that chunk and the newly installed state word. Prefix commutation alone would not establish absence of additional output; the empty-output endpoint is essential.

The stronger claim that the install call emits nothing at any intermediate time follows from append-only output and its empty-output endpoint: if a nonempty prefix had appeared, later steps could not erase it. No inspection of its transition proof is needed. This also handles a multi-bit previously emitted chunk.

**Remaining public FP/helper statement restatements.** These complete the new public statement inventory beyond the headliners and machine contracts above.

| Statements | Independent meaning |
|---|---|
| `polyTimeComputable_sliceTakeAt`, `polyTimeComputable_sliceDropAt` | Each displayed total slicing/re-encoding function is FP for fixed natural `a,k`. |
| `polyTimeComputable_tail`, `polyTimeComputable_take1` | Dropping or taking one symbol is FP; both return `[]` on empty input. |
| `polyTimeComputable_headD` | Returning the head as a singleton is FP, with `[false]` on empty input. |
| `polyTimeComputable_isNil` | The singleton emptiness bit is FP. |
| `polyTimeComputable_or`, `polyTimeComputable_not` | Pointwise OR of two FP singleton tests, and negation of one, remain FP singleton tests. |
| `pairFstD_nil` | The empty word has empty first default projection. |
| `length_pairSndD_le` | The second default projection has length at most the input length. |
| `eq_pairEncode_of_pairFstD_ne` | A nonempty first default projection certifies that re-encoding both projections recovers the original word. No converse is asserted. |
| `length_pair_components_le` | Twice the first projected length plus the second projected length is at most the original length, also on malformed words. |
| `length_sliceDropAt_le` | Reconstructing after dropping a slice has length at most `max z.length 2`, accounting for canonicalization of a short malformed word. |
| `flatMap_range_eq_single` | If `K<N` and all chunks in `range N` are empty except the prescribed chunk at `K`, their concatenation equals that chunk, of any length. |
| `polyTimeComputable_xorD`, `xorD_pairEncode` | The total truncating XOR function is FP; on genuine pair encodings it is precisely `List.zipWith xor`. |
| `polyTimeComputable_blockAnyTest`, `polyTimeComputable_blockXorAnyTest`, `polyTimeComputable_blockMajorityTest` | From an FP singleton indicator of `V`, obtain exactly one Boolean output encoding the specified aggregate on every input word. |

**Question 6 — additive extension and evidence.**

The baseline's 13 `PClosure` declarations remain an ordered prefix of the current 16. I compared the complete pre-existing declaration text, not just names: after removing comments/whitespace and the new import, it is unchanged. The additions are three ordinary theorems in `namespace Complexity`; there is no new definition, instance, notation, or attribute in that suffix. The new imported implementation modules use the `Complexity` and `Turing` namespaces; the private finite-type instance concerns only the new private body-state type. I found no mechanism that changes existing closure definitions through instance or namespace capture.

For the phase-1 surface, the repository comparison reports eight existing non-`PolyTimeModel` files with changes; each is unchanged after comment/whitespace removal. The other four phase-1 files are absent from the repository diff. `PolyTimeModel` retains the same 20 declaration names, their order and signatures, and exactly the same imports; only the three targeted declaration bodies differ. All nine Lean modules in this attachment match the pinned repository snapshot. These checks corroborate the statement-freeze claim without auditing proofs.

I also read the committed sweep, axiom, and lint logs. They report 19 successful module checks, one intentional admission in `walk_visits_concentration`, and 36 axiom prints of which 35 contain only `propext`, `Classical.choice`, and `Quot.sound`. The exceptional print contains `sorryAx` for that same documented stub. I did not independently run Lean, regenerate oleans, or reproduce those prints. The sweep log identifies `74af662` plus a worktree documentation sweep, so its execution-to-final-snapshot provenance remains a maintainer attestation rather than an independently reproduced build.

The lint log reports `Classes.lean` at **1,329 lines**, rather than the pack's 1,266; the plan's closure row gives the correct 1,329. This discrepancy does not alter the disclosed size finding or the audited semantics. A later split of the counting layer is reasonable provided names, statements, definitions, and required import access are preserved and the affected tree is rechecked. I would not require that refactor to establish fidelity of these fill additions, and this audit does not make a maintainer-reserved decision on it.

No formal-statement repair is proposed. Findings 1–2 should be resolved as documentation/API-inventory corrections. Findings 3–4 delimit the exact guarantees that subsequent work may use.

## ===== audits/ch7-fill-resolutions.md =====

# Chapter 7 fill gate — resolutions (OPEN: round 2 asks the duplication question)

## Round 1 (2026-10-10): 0 blockers, 0 majors, 2 minors, 2 notes

Findings verbatim in `audits/ch7-fill-findings.md`.

**Provenance.** The auditor hashed its input as `00be8b1d…`. That is
`0c22ae33:audits/ch7-fill-bundle.md`, the bundle from Aparna's fork, not the
merged-tree adaptation `audits/ch7-fill-bundle.md` (`39eacf62…`). Round 1
therefore audited questions 1–6 on the fork's sources, and **question 7
(duplication, `audits/TEMPLATE.md` failure mode 5) was never asked.**

**Transfer to the merged tree (verified, `audits/logs/ch7-fill-r2-transfer.log`).**
Of the nine Lean files round 1 audited, six are byte-identical at the round-2
commit to `0c22ae33`. The other three, `EmitIterEmbed`, `PolyTimeBlockLoop`
and `PClosure`, differ in comments only (comment- and whitespace-stripped
identical): the P0 finding-5 docstrings in `PClosure` and the round-1 sweep
below. The statement findings of questions 1–6 therefore carry over unchanged.

**User decisions (2026-10-10).** (1) A short follow-up round on the merged
tree asks question 7 only; questions 1–6 are not reopened. (2) The maintainer
sweeps the minors on the campaign branch, and Aparna pulls them on her side.
(3) Finding 2 is resolved by correcting the summary; any API change waits for
12.2c item 6 (EmitIter ↔ §12 unification).

| Finding | Disposition |
|---|---|
| 1 (minor): `PolyTimeBlockLoop`'s module summary credits XOR to the abandoned one-pass counter program | **Swept** (doc-only): the bullet now reads "polynomial-time, via the emit-iteration loop" |
| 2 (minor): `EmitIterEmbed`'s summary advertises `Turing.control_step`/`control_step'`, which are private in `EmitIterBody` | **Swept** (doc-only): both names are removed from *Main results*, and the "control steps" bullet now says these are private helpers of `EmitIterBody`, not exports of this module. No API change; 12.2c item 6 settles that layer |
| 3 (note): the three block headlines are total extensions through default decoding | **Carried as documentation**: one paragraph added to `PClosure`'s "Block-query closure" section docstring. Malformed words are classified by the same test on their default-decoded components, an invalid inner pair keeps only the outer mask, and `V` is consulted only on re-encoded queries. Statements unchanged |
| 4 (note): `exists_emitIterTM`'s all-iterations orbit bound is sufficient, not necessary | **Carried.** No change; a scheduled-orbit generalization is optional future work |

**Sweep verification.** The diff is
`audits/evidence/ch7/ch7-fill-r1-minor-sweep.diff`, comment-only in all three
files. The seven-module chain from `Build/EmitIterEmbed` to
`Randomized/PolyTimeModel` re-checks with 0 errors
(`audits/logs/ch7-fill-r2-docfix-sweep.log`). Lint reports 0 FAIL in
`ClassNP` and `TuringMachine/Build`.

## Round 2 (pending)

Pack: `audits/ch7-fill-r2-pack.md`, with bundle `audits/ch7-fill-r2-bundle.md`.
It asks question 7 on the merged tree and checks the round-1 sweep. Findings
go to `audits/ch7-fill-r2-findings.md`. The gate closes on zero blockers and
zero majors.

## ===== audits/evidence/ch7/ch7-fill-duplication-screen.md =====

# Chapter-7 fill surface — duplication screen (merged tree)

Maintainer pre-screen for the ch7 fill gate's duplication question (pack question 7),
run on the merged tree `complexity/arora-barak-ch3-4` at `49658bb6` under this
repository's duplication governance (`policy.md` **Duplication**, `workflow.md` §4,
`audits/TEMPLATE.md` failure mode 5). The auditor verifies these facts and judges the
classification; it is a starting point, not a substitute for the audit.

## Method

Script: `audits/evidence/ch7/ch7-fill-duplication-screen.py`. Every `.lean` file under
`TCSlib/` (561 files) is comment-stripped and split into declarations. Each of the
**112 declarations** of the six-file surface (`Build/EmitIterEmbed`,
`Build/EmitIterBody`, `ClassNP/PolyTimeBlockLoop`, `PolyTimeBlockTests`,
`PolyTimeBlockMajority`, and the three new `PClosure` headliners) is cut into token
shingles in two modes: **exact** (25-token runs) and **renamed** (50-token runs with
every identifier abstracted, so a consistently renamed copy still matches). A
declaration's overlap is the fraction of its shingles found in one other declaration
anywhere in the tree. Reported threshold: ≥ 50%.

**Coverage qualification.** The screen detects contiguous reproduction, exact or under
consistent renaming. It does not detect re-derivations whose proofs are restructured,
and it says nothing about design-level parallels. Whether `EmitIterEmbed` duplicates
the §12 `Build/Embed` layer is a non-mechanical question for the auditor.

## Results

**Class A: one per-loop lemma set re-proved under renaming (debt).** The OR, XOR and
strict-majority loops each carry their own copy of the same orbit, length and init
lemmas. The proofs are identical up to the step function's name; a single lemma
quantified over the step function would serve all three. The later instance of each
pair is counted as the copy (`PolyTimeBlockTests` predates the split that produced
`PolyTimeBlockMajority`; within `Tests` the OR loop predates the XOR loop).

| Copy | Original | Overlap (renamed / exact) | Lines |
|---|---|---|---:|
| `Majority::length_majStep_iterate` | `Tests::length_xorStep_iterate` | 100% / 39% | 15 |
| `Majority::majStep_orbit_done` | `Tests::anyStep_orbit_done` | 100% / 49% | 16 |
| `Majority::length_majStep_le` | `Tests::length_xorStep_le` | 72% / 63% | 46 |
| `Majority::polyTimeComputable_majInit` | `Tests::polyTimeComputable_anyInit` | 53% / 38% (reverse direction 83%) | 8 |
| `Tests::xorStep_orbit_done` | `Tests::anyStep_orbit_done` | 53% / 27% | 21 |
| `Tests::xorLoop_output` | `Tests::anyLoop_output` | 51% / 19% (reverse 59%) | 30 |

All six members are `private`. Per-file totals:

- **`PolyTimeBlockMajority`: 4 of 14 declarations (28.6%, 85 lines). This is above the
  one-fifth threshold** (`workflow.md` §4), so a `backlog.md` §1 human-review item is
  opened. **The human maintainer has acknowledged it** (2026-10-10): it is resolved in
  the 12.2c refactor, as one generic lemma set with statements unchanged.
- **`PolyTimeBlockTests`: 2 of 25 declarations (8.0%).**

**Class B: mirror pairs (dual statements; conventional, not counted).** These are
dual statements whose proofs coincide under the swap, the usual Lean
`_left`/`_right` pattern:

- `PolyTimeBlockLoop`: `polyTimeComputable_take1`/`_tail` and
  `polyTimeComputable_sliceTakeAt`/`_sliceDropAt` (100% renamed).
- `EmitIterBody`: `embed_ofWords_left`/`_right` (100% renamed).
- `PolyTimeBlockLoop::length_pairSndD_le` against
  `PolyTimePairing::length_pairFstD_le` (53% renamed, only 19 shingles — the Snd/Fst
  dual).

**Borderline (auditor to judge).**

- `PolyTimeBlockLoop::length_xorPairStep_le` against `length_sliceDropAt_le` in the
  same file: 87% renamed, 0% exact. They have the same proof shape over different step
  functions.
- `Majority::majStep` against `polyTimeComputable_majStep`: 55–63%. This is a
  definition overlapping its own poly-time proof, which restates its case structure;
  it is not believed to be duplication.

**Class C: copies of pre-existing repository material: none.** Matched against
everything outside the six files, the largest overlap is the 19-shingle Snd/Fst dual
above (53%). The rest:

| Surface declaration | Closest outside match | Overlap |
|---|---|---|
| `polyTimeComputable_or` | `PolyTimePairing::polyTimeComputable_and` (a dual) | 44% exact |
| `EmitIterEmbed::embedCfg` | `Oracle::Cfg.embedOracle` (a design parallel) | 42% renamed |
| `mem_P_of_blockMajority` | `PolyTimeModel::polyTimeModel_closedUnderMajority` (its consumer) | 25% |

None of the §12 material (`Build/Embed`, `Build/Seam`, `Build/Catalog`) or the loop
library (`Build/Loop`, `Build/Primitives`) appears among the matches.

## Design-level parallel (not mechanical; recorded in the ledger watch items)

`EmitIterEmbed.lean` exports a **public** tape-padding, state-injecting embedding layer
(`padAction`, `embedCfg`, `embed_step`, `embed_run`, `SafeRun`: 18 public
declarations, no private ones). It was written against `main`, which lacks the §12
`Build/Embed.lean` (attached to the bundle for comparison). The two layers are
independently written, and the screen finds no copies between them. Consolidating them
into one embedding API is on the **12.2c docket** (user decision, 2026-10-10).

## ===== audits/evidence/ch7/ch7-fill-duplication-screen.py =====

import os, re, sys, glob, collections
root = sys.argv[1]
def strip(src):
    out=[];i=0;depth=0;n=len(src)
    while i<n:
        if src.startswith('/-',i): depth+=1;i+=2;continue
        if depth and src.startswith('-/',i): depth-=1;i+=2;continue
        if depth: i+=1;continue
        if src.startswith('--',i):
            j=src.find('\n',i); i = n if j<0 else j; continue
        out.append(src[i]);i+=1
    return ''.join(out)
TOK = re.compile(r"[A-Za-z_Ͱ-Ͽ₀-ₜ][A-Za-z0-9_'.Ͱ-Ͽ₀-ₜ!?]*|\d+|\S")
KW = set("def theorem lemma abbrev instance structure private protected noncomputable by have show from fun at with calc exact apply intro intros rw simp simp_all omega cases rcases obtain refine constructor induction match if then else let in using only decide norm_num linarith nlinarith positivity aesop rfl ring field_simp unfold split contradiction exfalso subst congr ext funext specialize use exists left right trivial assumption dsimp change generalize gcongr push_neg by_contra by_cases".split())
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|private|protected)\s+)*(?:def|theorem|lemma|abbrev|instance|structure|inductive)\s+(\S+)", re.M)
def decls(text):
    ms = list(DECL.finditer(text))
    for i,m in enumerate(ms):
        end = ms[i+1].start() if i+1<len(ms) else len(text)
        yield m.group(1), text[m.start():end]
def toks(s, abstract):
    t = TOK.findall(s)
    return [('ID' if abstract and re.match(r"[A-Za-z_]",x) and x not in KW else x) for x in t]
def shingles(t, k): return {tuple(t[i:i+k]) for i in range(max(0,len(t)-k+1))}
surface = ['TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean','TCSlib/Complexity/TuringMachine/Build/EmitIterBody.lean',
           'TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean','TCSlib/Complexity/ClassNP/PolyTimeBlockTests.lean',
           'TCSlib/Complexity/ClassNP/PolyTimeBlockMajority.lean','TCSlib/Complexity/ClassNP/PClosure.lean']
pclosure_new = {'mem_P_of_blockAny','mem_P_of_blockMajority','mem_P_of_blockXorAny'}
allfiles = [os.path.relpath(p,root) for p in glob.glob(os.path.join(root,'TCSlib/**/*.lean'),recursive=True)]
EX_K, AB_K = 25, 50
hay_ex, hay_ab = collections.defaultdict(set), collections.defaultdict(set)
for f in allfiles:
    txt = strip(open(os.path.join(root,f),encoding='utf-8').read())
    for name, body in decls(txt):
        for s in shingles(toks(body,False),EX_K): hay_ex[s].add((f,name))
        for s in shingles(toks(body,True),AB_K): hay_ab[s].add((f,name))
print(f"haystack: {len(allfiles)} files")
rows=[]
for f in surface:
    txt = strip(open(os.path.join(root,f),encoding='utf-8').read())
    for name, body in decls(txt):
        if f.endswith('PClosure.lean') and name not in pclosure_new: continue
        for mode,k,hay in (('exact',EX_K,hay_ex),('renamed',AB_K,hay_ab)):
            sh = shingles(toks(body, mode=='renamed'), k)
            if not sh: continue
            hits = collections.Counter()
            for s in sh:
                for (g,n2) in hay.get(s,()):
                    if (g,n2) != (f,name): hits[(g,n2)] += 1
            if hits:
                (g,n2),c = hits.most_common(1)[0]
                rows.append((c/len(sh), mode, f.split('/')[-1], name, len(sh), g, n2))
rows.sort(reverse=True)
screened = sum(1 for f in surface for n,_ in decls(strip(open(os.path.join(root,f)).read())) if not (f.endswith('PClosure.lean') and n not in pclosure_new))
print(f"declarations screened: {screened}")
print("top overlaps (fraction of the declaration's shingles found in ONE other declaration elsewhere):")
for r in [r for r in rows if r[0]>=.5]: print(f"  {r[0]:.0%} [{r[1]}] {r[2]}::{r[3]} ({r[4]} sh) ~ {r[5]}::{r[6]}")
print(f"declarations with >=50% overlap: exact={sum(1 for r in rows if r[1]=='exact' and r[0]>=.5)}, renamed={sum(1 for r in rows if r[1]=='renamed' and r[0]>=.5)}")

## ===== audits/evidence/ch7/ch7-fill-duplication-screen-rerun.txt =====

haystack: 562 files
declarations screened: 112
top overlaps (fraction of the declaration's shingles found in ONE other declaration elsewhere):
  100% [renamed] PolyTimeBlockTests.lean::length_xorStep_iterate (139 sh) ~ TCSlib/Complexity/ClassNP/PolyTimeBlockMajority.lean::length_majStep_iterate
  100% [renamed] PolyTimeBlockTests.lean::anyStep_orbit_done (178 sh) ~ TCSlib/Complexity/ClassNP/PolyTimeBlockMajority.lean::majStep_orbit_done
  100% [renamed] PolyTimeBlockMajority.lean::majStep_orbit_done (178 sh) ~ TCSlib/Complexity/ClassNP/PolyTimeBlockTests.lean::anyStep_orbit_done
  100% [renamed] PolyTimeBlockMajority.lean::length_majStep_iterate (139 sh) ~ TCSlib/Complexity/ClassNP/PolyTimeBlockTests.lean::length_xorStep_iterate
  100% [renamed] PolyTimeBlockLoop.lean::polyTimeComputable_take1 (38 sh) ~ TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean::polyTimeComputable_tail
  100% [renamed] PolyTimeBlockLoop.lean::polyTimeComputable_tail (38 sh) ~ TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean::polyTimeComputable_take1
  100% [renamed] PolyTimeBlockLoop.lean::polyTimeComputable_sliceTakeAt (176 sh) ~ TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean::polyTimeComputable_sliceDropAt
  100% [renamed] PolyTimeBlockLoop.lean::polyTimeComputable_sliceDropAt (176 sh) ~ TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean::polyTimeComputable_sliceTakeAt
  100% [renamed] EmitIterBody.lean::embed_ofWords_right (73 sh) ~ TCSlib/Complexity/TuringMachine/Build/EmitIterBody.lean::embed_ofWords_left
  100% [renamed] EmitIterBody.lean::embed_ofWords_left (73 sh) ~ TCSlib/Complexity/TuringMachine/Build/EmitIterBody.lean::embed_ofWords_right
  87% [renamed] PolyTimeBlockLoop.lean::length_xorPairStep_le (87 sh) ~ TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean::length_sliceDropAt_le
  83% [renamed] PolyTimeBlockTests.lean::polyTimeComputable_anyInit (24 sh) ~ TCSlib/Complexity/ClassNP/PolyTimeBlockMajority.lean::polyTimeComputable_majInit
  81% [renamed] PolyTimeBlockLoop.lean::length_sliceDropAt_le (94 sh) ~ TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean::length_xorPairStep_le
  72% [renamed] PolyTimeBlockMajority.lean::length_majStep_le (419 sh) ~ TCSlib/Complexity/ClassNP/PolyTimeBlockTests.lean::length_xorStep_le
  63% [exact] PolyTimeBlockMajority.lean::majStep (143 sh) ~ TCSlib/Complexity/ClassNP/PolyTimeBlockMajority.lean::polyTimeComputable_majStep
  63% [exact] PolyTimeBlockMajority.lean::length_majStep_le (427 sh) ~ TCSlib/Complexity/ClassNP/PolyTimeBlockTests.lean::length_xorStep_le
  60% [renamed] PolyTimeBlockTests.lean::length_xorStep_le (500 sh) ~ TCSlib/Complexity/ClassNP/PolyTimeBlockMajority.lean::length_majStep_le
  59% [renamed] PolyTimeBlockTests.lean::anyLoop_output (323 sh) ~ TCSlib/Complexity/ClassNP/PolyTimeBlockTests.lean::xorLoop_output
  55% [exact] PolyTimeBlockTests.lean::length_xorStep_le (483 sh) ~ TCSlib/Complexity/ClassNP/PolyTimeBlockMajority.lean::length_majStep_le
  55% [renamed] PolyTimeBlockMajority.lean::majStep (118 sh) ~ TCSlib/Complexity/ClassNP/PolyTimeBlockMajority.lean::polyTimeComputable_majStep
  53% [renamed] PolyTimeBlockTests.lean::xorStep_orbit_done (184 sh) ~ TCSlib/Complexity/ClassNP/PolyTimeBlockTests.lean::anyStep_orbit_done
  53% [renamed] PolyTimeBlockMajority.lean::polyTimeComputable_majInit (38 sh) ~ TCSlib/Complexity/ClassNP/PolyTimeBlockTests.lean::polyTimeComputable_anyInit
  53% [renamed] PolyTimeBlockLoop.lean::length_pairSndD_le (19 sh) ~ TCSlib/Complexity/ClassNP/PolyTimePairing.lean::length_pairFstD_le
  51% [renamed] PolyTimeBlockTests.lean::xorLoop_output (374 sh) ~ TCSlib/Complexity/ClassNP/PolyTimeBlockTests.lean::anyLoop_output
declarations with >=50% overlap: exact=3, renamed=21

## ===== audits/evidence/ch7/ch7-fill-r1-minor-sweep.diff =====

diff --git a/TCSlib/Complexity/ClassNP/PClosure.lean b/TCSlib/Complexity/ClassNP/PClosure.lean
index 0370605d..f44d3024 100644
--- a/TCSlib/Complexity/ClassNP/PClosure.lean
+++ b/TCSlib/Complexity/ClassNP/PClosure.lean
@@ -203,7 +203,12 @@ the second component of a pair and aggregating the answers.  `blockAt a k z i` i
 count is `a'·(n+1)^k'`.  These are the folklore "repeat the machine polynomially many
 times" closures that [AB09] ch. 7 uses tacitly (§7.3, Theorem 7.8; §7.4.1;
 Theorems 7.17–7.18); the machine-level loop lives in
-`TCSlib.Complexity.ClassNP.PolyTimeBlockLoop`. -/
+`TCSlib.Complexity.ClassNP.PolyTimeBlockLoop`.
+
+Like the length comparisons above, all three languages are total extensions through
+the default projections: a malformed word is classified by the same test on its
+default-decoded components (for the nested pair, an invalid inner pair leaves only the
+outer mask), and `V` is consulted only on re-encoded queries (ch7 fill audit, note 3). -/
 
 /-- **`P` is closed under a polynomial block-OR**: if `V ∈ P` then so is the set of
 pairs some of whose `a'·(n+1)^k'` blocks of length `a·(n+1)^k` passes `V`'s test,
diff --git a/TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean b/TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean
index 611d5e11..b665bc25 100644
--- a/TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean
+++ b/TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean
@@ -45,7 +45,7 @@ stated in `TCSlib.Complexity.ClassNP.PClosure`, which imports this file.
   clean-call modules (`Turing.FinTM.exists_installCallTM` /
   `exists_emitCallTM`) as the per-round body.
 * `Complexity.polyTimeComputable_xorD` — truncating bitwise XOR is
-  polynomial-time (a one-pass counter program).
+  polynomial-time, via the emit-iteration loop.
 * The aggregated one-bit block tests live in
   `TCSlib.Complexity.ClassNP.PolyTimeBlockTests`.
 
diff --git a/TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean b/TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean
index 424ec64c..3ac16284 100644
--- a/TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean
+++ b/TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean
@@ -28,7 +28,10 @@ Generic machine-construction infrastructure shared by loop-body assemblies
   its states injected into the host's state type, step for step
   (`embed_step`/`embed_run`), while the padding tapes stay blank;
 * **control steps** — a transition that only changes control (and possibly
-  moves the input head) replaces just those configuration components.
+  moves the input head) replaces just those configuration components. These
+  two lemmas are private helpers of
+  `TCSlib.Complexity.TuringMachine.Build.EmitIterBody`, not exports of this
+  module.
 
 ## Main definitions
 
@@ -37,7 +40,7 @@ Generic machine-construction infrastructure shared by loop-body assemblies
 ## Main results
 
 * `Turing.runFrom_output_prefix`, `Turing.runFrom_output_extends`,
-  `Turing.embed_run`, `Turing.control_step`, `Turing.control_step'`.
+  `Turing.embed_run`.
 
 ## References
 

## ===== audits/logs/ch7-fill-r2-transfer.log =====

Transfer attestation: the nine Lean files of the round-1 bundle (a-gupte 0c22ae33) vs this working tree
Comment stripping: nested /- -/ blocks and -- line comments removed, then all whitespace removed.

COMMENT-ONLY DIFF  TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean  (de94b02751582f84 -> 1a7d25619fb88b51)
BYTE-IDENTICAL     TCSlib/Complexity/TuringMachine/Build/EmitIterBody.lean  (bc35c3485cad1755 -> bc35c3485cad1755)
COMMENT-ONLY DIFF  TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean  (5654f6f1b1b12025 -> 6ebb9c76ba771d77)
BYTE-IDENTICAL     TCSlib/Complexity/ClassNP/PolyTimeBlockTests.lean  (50f36052fcfe2359 -> 50f36052fcfe2359)
BYTE-IDENTICAL     TCSlib/Complexity/ClassNP/PolyTimeBlockMajority.lean  (3aafee9369808413 -> 3aafee9369808413)
COMMENT-ONLY DIFF  TCSlib/Complexity/ClassNP/PClosure.lean  (5481969b35302efd -> 304ef94faa5755f7)
BYTE-IDENTICAL     TCSlib/Complexity/Randomized/PolyTimeModel.lean  (8fdad754b3fd9040 -> 8fdad754b3fd9040)
BYTE-IDENTICAL     TCSlib/Complexity/Randomized/Classes.lean  (4cfa2b44e26bbedc -> 4cfa2b44e26bbedc)
BYTE-IDENTICAL     TCSlib/Complexity/Randomized/SipserGacs.lean  (b2971786332052f0 -> b2971786332052f0)

## ===== audits/logs/ch7-fill-r2-docfix-sweep.log =====

CHECK TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed
EXIT TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed 0
CHECK TCSlib/Complexity/TuringMachine/Build/EmitIterBody
EXIT TCSlib/Complexity/TuringMachine/Build/EmitIterBody 0
CHECK TCSlib/Complexity/ClassNP/PolyTimeBlockLoop
EXIT TCSlib/Complexity/ClassNP/PolyTimeBlockLoop 0
CHECK TCSlib/Complexity/ClassNP/PolyTimeBlockTests
EXIT TCSlib/Complexity/ClassNP/PolyTimeBlockTests 0
CHECK TCSlib/Complexity/ClassNP/PolyTimeBlockMajority
EXIT TCSlib/Complexity/ClassNP/PolyTimeBlockMajority 0
CHECK TCSlib/Complexity/ClassNP/PClosure
EXIT TCSlib/Complexity/ClassNP/PClosure 0
CHECK TCSlib/Complexity/Randomized/PolyTimeModel
EXIT TCSlib/Complexity/Randomized/PolyTimeModel 0

## ===== audits/logs/ch7-fill-merged-sweep.log =====

# ch7 fill sweep on the MERGED tree — 2026-10-10T04:15:27Z — complexity/arora-barak-ch3-4 at 6d555248 + merge of 0c22ae33 (index, pre-commit; committed as 49658bb6)
TCSlib/Complexity/Expanders/Basic rc=0 errors=0 sorry_decls=0
TCSlib/Complexity/Expanders/Mixing rc=0 errors=0 sorry_decls=0
TCSlib/Complexity/Expanders/Walks rc=0 errors=0 sorry_decls=0
TCSlib/Complexity/Expanders/Chernoff rc=0 errors=0 sorry_decls=1
TCSlib/Complexity/Randomized/SchwartzZippel rc=0 errors=0 sorry_decls=0
TCSlib/Complexity/Randomized/ErrorReduction rc=0 errors=0 sorry_decls=0
TCSlib/Complexity/Randomized/Classes rc=0 errors=0 sorry_decls=0
TCSlib/Complexity/Randomized/Adleman rc=0 errors=0 sorry_decls=0
TCSlib/Complexity/Randomized/SipserGacs rc=0 errors=0 sorry_decls=0
TCSlib/Complexity/TuringMachine/CounterProgInput rc=0 errors=0 sorry_decls=0
TCSlib/Complexity/CircuitComplexity/PairEncode rc=0 errors=0 sorry_decls=0
TCSlib/Complexity/ClassNP/PolyTimePrefix rc=0 errors=0 sorry_decls=0
TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed rc=0 errors=0 sorry_decls=0
TCSlib/Complexity/TuringMachine/Build/EmitIterBody rc=0 errors=0 sorry_decls=0
TCSlib/Complexity/ClassNP/PolyTimeBlockLoop rc=0 errors=0 sorry_decls=0
TCSlib/Complexity/ClassNP/PolyTimeBlockTests rc=0 errors=0 sorry_decls=0
TCSlib/Complexity/ClassNP/PolyTimeBlockMajority rc=0 errors=0 sorry_decls=0
TCSlib/Complexity/ClassNP/PClosure rc=0 errors=0 sorry_decls=0
TCSlib/Complexity/Randomized/PolyTimeModel rc=0 errors=0 sorry_decls=0
TCSlib/Complexity/Expanders rc=0 errors=0 sorry_decls=0
TCSlib/Complexity/Randomized rc=0 errors=0 sorry_decls=0
TCSlib/Complexity/ClassNP rc=0 errors=0 sorry_decls=0
TCSlib/Complexity/TuringMachine rc=0 errors=0 sorry_decls=0
TOTAL: failures=0 sorry_decls=1

## ===== audits/logs/ch7-fill-merged-axioms.log =====

# ch7 fill axiom prints on the MERGED tree (complexity/arora-barak-ch3-4 at 49658bb6) — the same 36 names as audits/logs/ch7-fill-axioms.log; the print lines below are byte-identical to that log
'Randomized.schwartz_zippel' depends on axioms: [propext, Classical.choice, Quot.sound]
'Randomized.iid_bernoulli_avg_concentration' depends on axioms: [propext, Classical.choice, Quot.sound]
'Randomized.majority_error_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Randomized.bpp_error_reduction' depends on axioms: [propext, Classical.choice, Quot.sound]
'Randomized.inBPPWeak_iff_inBPP' depends on axioms: [propext, Classical.choice, Quot.sound]
'Randomized.InBPP.compl' depends on axioms: [propext, Classical.choice, Quot.sound]
'Randomized.inZPP_iff_inRP_and_inCoRP' depends on axioms: [propext, Classical.choice, Quot.sound]
'Randomized.adleman' depends on axioms: [propext, Classical.choice, Quot.sound]
'Randomized.sipser_gacs' depends on axioms: [propext, Classical.choice, Quot.sound]
'Randomized.bpp_subset_sigma2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Expander.lambda_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Expander.norm_mulVec_le_lambda' depends on axioms: [propext, Classical.choice, Quot.sound]
'Expander.walk_all_mem_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Expander.walk_visits_concentration' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Randomized.polyTimeModel_closedUnderRace' depends on axioms: [propext, Classical.choice, Quot.sound]
'Randomized.polyTimeModel_closedUnderAnswerIs' depends on axioms: [propext, Classical.choice, Quot.sound]
'Randomized.polyTimeModel_closedUnderNot' depends on axioms: [propext, Classical.choice, Quot.sound]
'Randomized.polyTimeModel_closedUnderMajority' depends on axioms: [propext, Classical.choice, Quot.sound]
'Randomized.polyTimeModel_closedUnderAny' depends on axioms: [propext, Classical.choice, Quot.sound]
'Randomized.polyTimeModel_closedUnderShiftOr' depends on axioms: [propext, Classical.choice, Quot.sound]
'Randomized.polyTimeModel_verifierHasCircuits' depends on axioms: [propext, Classical.choice, Quot.sound]
'Randomized.inSigma2_polyTimeModel_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Randomized.adleman_polyTime' depends on axioms: [propext, Classical.choice, Quot.sound]
'Randomized.sipser_gacs_polyTime' depends on axioms: [propext, Classical.choice, Quot.sound]
'Randomized.zpp_eq_rp_inter_corp_polyTime' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.mem_P_of_blockAny' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.mem_P_of_blockMajority' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.mem_P_of_blockXorAny' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.polyTimeComputable_blockAnyTest' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.polyTimeComputable_blockMajorityTest' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.polyTimeComputable_blockXorAnyTest' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.polyTimeComputable_emitIter' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.polyTimeComputable_xorD' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.polyTimeComputable_sliceTakeAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.polyTimeComputable_sliceDropAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.exists_emitIterTM' depends on axioms: [propext, Classical.choice, Quot.sound]

## ===== TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean =====

```
/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.TuringMachine.Build.Loop
import TCSlib.Complexity.TuringMachine.Build.Primitives

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Run embedding for loop bodies

Generic machine-construction infrastructure shared by loop-body assemblies
(first customer: `TCSlib.Complexity.TuringMachine.Build.EmitIterBody`):

* **safe runs** — a run segment that never visits an avoided (anchor) state
  strictly before its endpoint, closed under prepending a step and under
  concatenation: the shape of the `Turing.FinTM.exists_emitLoopTM` startup
  and round obligations;
* **output-prefix commutation** — the transition table never reads the
  output tape and the output is append-only, so prepending a fixed output
  prefix commutes with running the machine, and outputs only ever extend;
* **the tape-padding, state-injecting embedding** — a clean-call module over
  `m ≤ k` tapes runs inside a `k`-tape host on its first `m` work tapes with
  its states injected into the host's state type, step for step
  (`embed_step`/`embed_run`), while the padding tapes stay blank;
* **control steps** — a transition that only changes control (and possibly
  moves the input head) replaces just those configuration components. These
  two lemmas are private helpers of
  `TCSlib.Complexity.TuringMachine.Build.EmitIterBody`, not exports of this
  module.

## Main definitions

* `Turing.SafeRun`, `Turing.padAction`, `Turing.embedCfg`.

## Main results

* `Turing.runFrom_output_prefix`, `Turing.runFrom_output_extends`,
  `Turing.embed_run`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2: the machine model these
  constructions assemble.)
-/

namespace Turing

open MultiTapeTM

variable {k m : ℕ} {B SS : Type} {x : List Bool}

/-! ### Safe runs

A run segment together with the promise that no strictly earlier
configuration sits at the avoided (anchor) state: the shape of the
`exists_emitLoopTM` startup and round obligations, closed under
single-step prepending and concatenation. -/

/-- A run from `c` to `c'` in exactly `t` steps that never visits the state
`avoid` strictly before `t`. -/
def SafeRun (H : MultiTapeTM k Bool B) (avoid : B)
    (c : Cfg k Bool B x) (t : ℕ) (c' : Cfg k Bool B x) : Prop :=
  H.runFrom c t = c' ∧ ∀ t' < t, (H.runFrom c t').state ≠ some avoid

/-- The empty run is safe. -/
theorem SafeRun.zero {H : MultiTapeTM k Bool B} {avoid : B}
    {c : Cfg k Bool B x} : SafeRun H avoid c 0 c :=
  ⟨rfl, fun t' ht' => absurd ht' (by omega)⟩

/-- Prepend one non-avoided step to a safe run. -/
theorem SafeRun.cons {H : MultiTapeTM k Bool B} {avoid : B}
    {c c₁ c' : Cfg k Bool B x} {t : ℕ} (hstep : H.step c = c₁)
    (hc : c.state ≠ some avoid) (h : SafeRun H avoid c₁ t c') :
    SafeRun H avoid c (t + 1) c' := by
  have hone : H.runFrom c 1 = c₁ := by
    simp [runFrom, hstep]
  refine ⟨?_, ?_⟩
  · rw [show t + 1 = 1 + t by omega, runFrom_add, hone]
    exact h.1
  · intro t' ht'
    cases t' with
    | zero => simpa using hc
    | succ u =>
      rw [show u + 1 = 1 + u by omega, runFrom_add, hone]
      exact h.2 u (by omega)

/-- Concatenate safe runs. -/
theorem SafeRun.trans {H : MultiTapeTM k Bool B} {avoid : B}
    {c c₁ c' : Cfg k Bool B x} {t₁ t₂ : ℕ} (h₁ : SafeRun H avoid c t₁ c₁)
    (h₂ : SafeRun H avoid c₁ t₂ c') : SafeRun H avoid c (t₁ + t₂) c' := by
  refine ⟨?_, ?_⟩
  · rw [runFrom_add, h₁.1]
    exact h₂.1
  · intro t' ht'
    by_cases hlt : t' < t₁
    · exact h₁.2 t' hlt
    · obtain ⟨u, rfl⟩ : ∃ u, t' = t₁ + u := ⟨t' - t₁, by omega⟩
      rw [runFrom_add, h₁.1]
      exact h₂.2 u (by omega)

/-! ### Output-prefix commutation

The transition table never reads the output tape and the output is
append-only, so prepending a fixed prefix to the output commutes with
running the machine. -/

/-- One step commutes with an output prefix. -/
theorem step_output_prefix (H : MultiTapeTM k Bool B)
    (c : Cfg k Bool B x) (pre : List Bool) :
    H.step { c with output := pre ++ c.output } =
      { H.step c with output := pre ++ (H.step c).output } := by
  obtain ⟨st, pos, tapes, tpos, out⟩ := c
  cases st with
  | none => rfl
  | some q =>
    have hws : (⟨some q, pos, tapes, tpos, pre ++ out⟩ : Cfg k Bool B x).workTapeSymbols =
        (⟨some q, pos, tapes, tpos, out⟩ : Cfg k Bool B x).workTapeSymbols := rfl
    simp [MultiTapeTM.step, Action.apply, Cfg.inputSymbol, hws, List.append_assoc]

/-- A run commutes with an output prefix. -/
theorem runFrom_output_prefix (H : MultiTapeTM k Bool B)
    (c : Cfg k Bool B x) (pre : List Bool) (t : ℕ) :
    H.runFrom { c with output := pre ++ c.output } t =
      { H.runFrom c t with output := pre ++ (H.runFrom c t).output } := by
  induction t generalizing c with
  | zero => simp
  | succ t ih =>
    rw [runFrom_succ_eq_step, runFrom_succ_eq_step, step_output_prefix]
    exact ih (H.step c)

/-- The output tape is append-only along a run. -/
theorem runFrom_output_extends (H : MultiTapeTM k Bool B)
    (c : Cfg k Bool B x) (t : ℕ) :
    ∃ o, (H.runFrom c t).output = c.output ++ o := by
  induction t generalizing c with
  | zero => exact ⟨[], by simp⟩
  | succ t ih =>
    rw [runFrom_succ_eq_step]
    obtain ⟨o, ho⟩ := ih (H.step c)
    unfold MultiTapeTM.step at ho ⊢
    cases hq : c.state with
    | none =>
      rw [hq] at ho
      exact ⟨o, ho⟩
    | some q =>
      rw [hq] at ho
      refine ⟨(H.tr q c.inputSymbol c.workTapeSymbols).output.toList ++ o, ?_⟩
      rw [ho]
      simp [Action.apply]

/-! ### Halted runs are stationary -/

/-- A halted configuration never changes. -/
theorem runFrom_of_halted (H : MultiTapeTM k Bool B)
    {c : Cfg k Bool B x} (h : c.state = none) (t : ℕ) : H.runFrom c t = c := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [runFrom_add, ih]
    simp [runFrom, step_of_halt h]

/-- Every configuration strictly before a live endpoint is live. -/
theorem state_isSome_of_runFrom (H : MultiTapeTM k Bool B)
    {c : Cfg k Bool B x} {t : ℕ} {qf : B}
    (hf : (H.runFrom c t).state = some qf) {j : ℕ} (hj : j ≤ t) :
    ∃ q, (H.runFrom c j).state = some q := by
  cases hq : (H.runFrom c j).state with
  | some q => exact ⟨q, rfl⟩
  | none =>
    exfalso
    have hstat : H.runFrom c t = H.runFrom c j := by
      obtain ⟨u, rfl⟩ : ∃ u, t = j + u := ⟨t - j, by omega⟩
      rw [runFrom_add, runFrom_of_halted H hq]
    rw [hstat, hq] at hf
    exact Option.noConfusion hf

/-! ### Tape-padding, state-injecting embedding

A clean-call module over `m ≤ k` tapes runs inside the `k`-tape body on its
first `m` work tapes, with its states injected into the body's state type;
the extra tapes stay blank and their heads stay at the origin. -/

/-- Pad a module action to the host: act on the first `m` tapes, leave the
rest alone, and map the successor state. -/
def padAction (hmk : m ≤ k) (f : Option SS → Option B)
    (a : Action m Bool SS) : Action k Bool B where
  inputTape := a.inputTape
  workTapes := fun i =>
    if h : (i : ℕ) < m then a.workTapes ⟨i, h⟩ else (none, 0)
  output := a.output
  state := f a.state

/-- Embed a module configuration into the host. -/
def embedCfg (hmk : m ≤ k) (inject : SS → B)
    (c : Cfg m Bool SS x) : Cfg k Bool B x where
  state := c.state.map inject
  inputPos := c.inputPos
  workTapes := fun i =>
    if h : (i : ℕ) < m then c.workTapes ⟨i, h⟩ else fun _ => none
  workTapePos := fun i =>
    if h : (i : ℕ) < m then c.workTapePos ⟨i, h⟩ else 0
  output := c.output

/-- Embedding a canonical seam gives a canonical seam with the padded word
assignment. -/
theorem embedCfg_ofWords (hmk : m ≤ k) (inject : SS → B) (q : SS)
    (w : Fin m → List Bool) :
    embedCfg hmk inject (Cfg.ofWords (input := x) q w) =
      Cfg.ofWords (inject q)
        (fun i => if h : (i : ℕ) < m then w ⟨i, h⟩ else []) := by
  unfold embedCfg Cfg.ofWords
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    by_cases h : (i : ℕ) < m <;> simp [h]
  · funext i
    by_cases h : (i : ℕ) < m <;> simp [h]

/-- Applying a padded action to an embedded configuration embeds the applied
module configuration. -/
theorem padAction_apply (hmk : m ≤ k) (inject : SS → B)
    (a : Action m Bool SS) (c : Cfg m Bool SS x) (b : B) :
    (padAction hmk (Option.map inject) a).apply
        { embedCfg hmk inject c with state := some b } =
      embedCfg hmk inject (a.apply c) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    by_cases h : (i : ℕ) < m
    · simp only [Action.apply, padAction, embedCfg, dif_pos h]
    · simp only [Action.apply, padAction, embedCfg, dif_neg h]
  · funext i
    by_cases h : (i : ℕ) < m
    · simp only [Action.apply, padAction, embedCfg, dif_pos h]
    · simp only [Action.apply, padAction, embedCfg, dif_neg h]
      rfl

/-- The embedded configuration reads the module's work symbols on the first
`m` tapes. -/
theorem embedCfg_workTapeSymbols (hmk : m ≤ k) (inject : SS → B)
    (c : Cfg m Bool SS x) (b : B) :
    (fun i => ({ embedCfg hmk inject c with state := some b } :
        Cfg k Bool B x).workTapeSymbols (Fin.castLE hmk i)) =
      c.workTapeSymbols := by
  funext i
  have h : ((Fin.castLE hmk i : Fin k) : ℕ) < m := i.isLt
  simp only [Cfg.workTapeSymbols, embedCfg, dif_pos h]
  congr 1 <;> exact congrArg _ (Fin.eta i i.isLt) <;> rfl

/-- Embedding commutes with replacing the output. -/
theorem embedCfg_output (hmk : m ≤ k) (inject : SS → B)
    (c : Cfg m Bool SS x) (o : List Bool) :
    embedCfg hmk inject { c with output := o } =
      { embedCfg hmk inject c with output := o } := rfl

/-- A one-step run is a step. -/
theorem runFrom_one (H : MultiTapeTM k Bool B) (c : Cfg k Bool B x) :
    H.runFrom c 1 = H.step c := by
  simp [MultiTapeTM.runFrom]

/-- One host step at a state behaving like the module's state `q` tracks one
module step.
**Proof sketch.** Both steps dispatch their transition tables on live states;
the embedded configuration reads the same input symbol and, through
`embedCfg_workTapeSymbols`, the same work symbols, so the host's action is
the padded module action, and `padAction_apply` pushes it through the
embedding. -/
theorem embed_step (hmk : m ≤ k) (M : MultiTapeTM m Bool SS)
    (H : MultiTapeTM k Bool B) (inject : SS → B)
    (c : Cfg m Bool SS x) (q : SS) (hq : c.state = some q) (b : B)
    (htr : ∀ inp work, H.tr b inp work =
      padAction hmk (Option.map inject)
        (M.tr q inp (fun i => work (Fin.castLE hmk i)))) :
    H.step { embedCfg hmk inject c with state := some b } =
      embedCfg hmk inject (M.step c) := by
  have hIS : ({ embedCfg hmk inject c with state := some b } :
      Cfg k Bool B x).inputSymbol = c.inputSymbol := rfl
  have hstepL : H.step { embedCfg hmk inject c with state := some b } =
      (H.tr b ({ embedCfg hmk inject c with state := some b } :
          Cfg k Bool B x).inputSymbol
        ({ embedCfg hmk inject c with state := some b } :
          Cfg k Bool B x).workTapeSymbols).apply
        { embedCfg hmk inject c with state := some b } := rfl
  have hstepR : M.step c = (M.tr q c.inputSymbol c.workTapeSymbols).apply c := by
    unfold MultiTapeTM.step
    rw [hq]
  rw [hstepL, hstepR, htr, hIS, embedCfg_workTapeSymbols]
  exact padAction_apply hmk inject _ c b

/-- A module run strictly inside the avoided exit embeds step-for-step into
the host, provided the host's transition at every injected live state is the
padded module transition.
**Proof sketch.** Induction on the run length: every strictly earlier
configuration is live and off the exit by hypothesis, so `embed_step`
transports each step. -/
theorem embed_run (hmk : m ≤ k) (M : MultiTapeTM m Bool SS)
    (H : MultiTapeTM k Bool B) (inject : SS → B) (ex : SS)
    (htr : ∀ q : SS, q ≠ ex → ∀ inp work,
      H.tr (inject q) inp work =
        padAction hmk (Option.map inject)
          (M.tr q inp (fun i => work (Fin.castLE hmk i))))
    (c : Cfg m Bool SS x) (t : ℕ)
    (hstate : ∀ j < t, ∃ q, (M.runFrom c j).state = some q ∧ q ≠ ex) :
    H.runFrom (embedCfg hmk inject c) t = embedCfg hmk inject (M.runFrom c t) := by
  induction t generalizing c with
  | zero => simp
  | succ t ih =>
    obtain ⟨q, hq, hqex⟩ := hstate 0 (by omega)
    simp only [runFrom_zero] at hq
    have hstep : H.step (embedCfg hmk inject c) = embedCfg hmk inject (M.step c) := by
      have hc : { embedCfg hmk inject c with state := some (inject q) } =
          embedCfg hmk inject c := by
        simp [embedCfg, hq]
      rw [← hc]
      exact embed_step hmk M H inject c q hq (inject q) (htr q hqex)
    rw [runFrom_succ_eq_step, runFrom_succ_eq_step, hstep]
    exact ih (M.step c) (fun j hj => by
      have := hstate (j + 1) (by omega)
      simpa [runFrom, Function.iterate_succ_apply] using this)


end Turing
```

## ===== TCSlib/Complexity/TuringMachine/Build/EmitIterBody.lean =====

```
/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.TuringMachine.Build.EmitIterEmbed

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The emit-iteration body

The host machine behind `Complexity.polyTimeComputable_emitIter` (in
`TCSlib.Complexity.ClassNP.PolyTimeBlockLoop`): one finite machine that, on
input `w`, concatenates the chunks `e (g^[i] w)` for `i = 0, …, R |w|`, in
polynomial time, given machines for the step `g` and the chunk `e` and a
polynomial length envelope for the orbit of `g`.

It is an instance of `Turing.FinTM.exists_emitLoopTM`.  The body machine's
startup copies the native input onto work tape zero (the loop's round state)
and rewinds both heads to the canonical seam; each round is two clean calls
on the tape-resident state word — an emit-mode call
(`Turing.FinTM.exists_emitCallTM`) forwarding the chunk `e s` to the physical
output, then an install-mode call (`Turing.FinTM.exists_installCallTM`)
replacing the word by `g s` — glued by two control states.  The clean-call
modules run on the body's first tapes through a tape-padding, state-injecting
embedding (`padAction`/`embedCfg` below); the round assembly commutes the
already-emitted chunk past the install call with an output-prefix lemma.

## Main definitions

None — the body machine, its embedding, and the phase configurations are
private to this file.

## Main results

* `Turing.FinTM.exists_emitIterTM` — the finite machine computing the
  concatenated chunks of a polynomially clocked iteration, within a
  polynomial budget in the `C·(n+1)^c` normal form.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2; §7.3–§7.4: the folklore
  "simulate the machine on each block" loop this host implements.)
-/


namespace Turing

open MultiTapeTM

variable {k m : ℕ} {B SS : Type} {x : List Bool}

/-! ### The body machine

Startup copies the native input onto work tape zero and rewinds both heads;
a round is the emit-mode call (whose first action the anchor itself performs,
so an entry state equal to the exit state still runs), a control handoff, the
install-mode call (likewise inlined into `gStart`), and a control return to
the anchor. -/

/-- Control states of the emit-iteration body. -/
private inductive BodyState (SE SG : Type) where
  | copy
  | rwTape
  | rwInput0
  | rwInput
  | anchor
  | callE (q : SE)
  | gStart
  | callG (q : SG)
  deriving DecidableEq

private instance {SE SG : Type} [Fintype SE] [Fintype SG] :
    Fintype (BodyState SE SG) := derive_fintype% _

/-- The emit-iteration body: copy the input onto tape zero, then alternate
the two clean-call modules under the anchored round discipline. -/
private def emitIterBody (Em Gm : FinTM Bool) (hek : 0 < Em.k)
    (ee ex : Em.State) (ge gx : Gm.State) : FinTM Bool where
  k := max Em.k Gm.k
  State := BodyState Em.State Gm.State
  tm := {
    q₀ := .copy
    tr := fun q inp work => match q with
      | .copy => match inp with
        | some s => ⟨.pos,
            fun i => if (i : ℕ) = 0 then (some (some s), 1) else (none, 0),
            none, some .copy⟩
        | none => ⟨0,
            fun i => if (i : ℕ) = 0 then (none, -1) else (none, 0),
            none, some .rwTape⟩
      | .rwTape =>
        match work ⟨0, Nat.lt_of_lt_of_le hek (Nat.le_max_left _ _)⟩ with
        | some _ => ⟨0,
            fun i => if (i : ℕ) = 0 then (none, -1) else (none, 0),
            none, some .rwTape⟩
        | none => ⟨0,
            fun i => if (i : ℕ) = 0 then (none, 1) else (none, 0),
            none, some .rwInput0⟩
      | .rwInput0 => FinTM.controlAction .neg (some .rwInput)
      | .rwInput => match inp with
        | some _ => FinTM.controlAction .neg (some .rwInput)
        | none => FinTM.controlAction .pos (some .anchor)
      | .anchor =>
        padAction (Nat.le_max_left _ _) (Option.map .callE)
          (Em.tm.tr ee inp (fun i => work (Fin.castLE (Nat.le_max_left _ _) i)))
      | .callE q =>
        if q = ex then FinTM.controlAction 0 (some .gStart)
        else
          padAction (Nat.le_max_left _ _) (Option.map .callE)
            (Em.tm.tr q inp (fun i => work (Fin.castLE (Nat.le_max_left _ _) i)))
      | .gStart =>
        padAction (Nat.le_max_right _ _) (Option.map .callG)
          (Gm.tm.tr ge inp (fun i => work (Fin.castLE (Nat.le_max_right _ _) i)))
      | .callG q =>
        if q = gx then FinTM.controlAction 0 (some .anchor)
        else
          padAction (Nat.le_max_right _ _) (Option.map .callG)
            (Gm.tm.tr q inp (fun i => work (Fin.castLE (Nat.le_max_right _ _) i))) }

/-- A pure control transition replaces only the state. -/
private theorem control_step {H : MultiTapeTM k Bool B} {q r : B}
    (h : ∀ inp work, H.tr q inp work = FinTM.controlAction 0 (some r))
    {c : Cfg k Bool B x} (hc : c.state = some q) :
    H.step c = { c with state := some r } := by
  have hs : H.step c = (H.tr q c.inputSymbol c.workTapeSymbols).apply c := by
    unfold MultiTapeTM.step
    rw [hc]
  rw [hs, h]
  refine Cfg.ext rfl ?_ ?_ ?_ ?_ <;>
    simp [FinTM.controlAction, Action.apply]

/-- A moving control transition replaces the state and moves the input head. -/
private theorem control_step' {H : MultiTapeTM k Bool B} {q r : B} {mv : SignType}
    (h : ∀ inp work, H.tr q inp work = FinTM.controlAction mv (some r))
    {c : Cfg k Bool B x} (hc : c.state = some q) :
    H.step c = { c with
      state := some r
      inputPos := moveInputPos c.inputPos mv } := by
  have hs : H.step c = (H.tr q c.inputSymbol c.workTapeSymbols).apply c := by
    unfold MultiTapeTM.step
    rw [hc]
  rw [hs, h]
  refine Cfg.ext rfl rfl ?_ ?_ ?_ <;>
    simp [FinTM.controlAction, Action.apply]

section Body

variable (Em Gm : FinTM Bool) (ee ex : Em.State) (ge gx : Gm.State)

/-- Embedding an `Em`-seam into the body gives a body seam: tape zero's word
survives and the padding tapes are blank on both sides. -/
private theorem embed_ofWords_left (hek : 0 < Em.k) (s : List Bool) :
    embedCfg (Nat.le_max_left Em.k Gm.k) (BodyState.callE (SG := Gm.State))
        (Cfg.ofWords (input := x) ee (stateWord Em.k s)) =
      Cfg.ofWords (BodyState.callE ee) (stateWord (max Em.k Gm.k) s) := by
  rw [embedCfg_ofWords]
  congr 1
  funext i
  by_cases h : (i : ℕ) < Em.k
  · simp [stateWord, h]
  · have h0 : ¬ (i : ℕ) = 0 := fun hz => h (hz ▸ hek)
    simp [stateWord, h, h0]

/-- Embedding a `Gm`-seam into the body gives a body seam, provided `Gm` has
a genuine tape (otherwise tape zero's word would be lost). -/
private theorem embed_ofWords_right (hgk : 0 < Gm.k) (s : List Bool) :
    embedCfg (Nat.le_max_right Em.k Gm.k) (BodyState.callG (SE := Em.State))
        (Cfg.ofWords (input := x) ge (stateWord Gm.k s)) =
      Cfg.ofWords (BodyState.callG ge) (stateWord (max Em.k Gm.k) s) := by
  rw [embedCfg_ofWords]
  congr 1
  funext i
  by_cases h : (i : ℕ) < Gm.k
  · simp [stateWord, h]
  · have h0 : ¬ (i : ℕ) = 0 := fun hz => h (hz ▸ hgk)
    simp [stateWord, h, h0]

/-- **The round segment.** From the anchor seam carrying `s`, the body runs
the emit-mode module (emitting `es`), hands control to the install-mode
module (installing `gs`), and returns to the anchor seam, in positive time,
without visiting the anchor strictly inside.
**Proof sketch.** The anchor itself fires the emit module's first action, so
an entry state equal to the exit state still runs; `embed_run` transports the
rest of the emit run, landing at the handoff state with the chunk emitted and
the word preserved.  One control step enters `gStart`, which fires the
install module's first action; the install run is transported likewise, with
the already-emitted chunk commuted past it by `runFrom_output_prefix` (the
install module's own output stays empty along the run, by the append-only
output).  One final control step re-enters the anchor carrying the stepped
word.  The anchor-exclusion clause reads the visited state off the
appropriate phase equality: an injected call state, or a control state,
never the anchor. -/
private theorem body_round (hek : 0 < Em.k) (hgk : 0 < Gm.k) (s es gs : List Bool)
    (tE : ℕ) (htE : 0 < tE)
    (hEfirst : ∀ t', 0 < t' → t' < tE →
      (Em.tm.runFrom (Cfg.ofWords (input := x) ee (stateWord Em.k s)) t').state ≠
        some ex)
    (hErun : Em.tm.runFrom (Cfg.ofWords (input := x) ee (stateWord Em.k s)) tE =
      { Cfg.ofWords ex (stateWord Em.k s) with output := es })
    (tG : ℕ) (htG : 0 < tG)
    (hGfirst : ∀ t', 0 < t' → t' < tG →
      (Gm.tm.runFrom (Cfg.ofWords (input := x) ge (stateWord Gm.k s)) t').state ≠
        some gx)
    (hGrun : Gm.tm.runFrom (Cfg.ofWords (input := x) ge (stateWord Gm.k s)) tG =
      Cfg.ofWords gx (stateWord Gm.k gs)) :
    (emitIterBody Em Gm hek ee ex ge gx).tm.runFrom
        (Cfg.ofWords (input := x) .anchor (stateWord (max Em.k Gm.k) s))
        (tE + 1 + tG + 1) =
      { Cfg.ofWords (input := x) .anchor (stateWord (max Em.k Gm.k) gs)
          with output := es } ∧
    ∀ t', 0 < t' → t' < tE + 1 + tG + 1 →
      ((emitIterBody Em Gm hek ee ex ge gx).tm.runFrom
        (Cfg.ofWords (input := x) .anchor (stateWord (max Em.k Gm.k) s))
          t').state ≠ some .anchor := by
  set H := (emitIterBody Em Gm hek ee ex ge gx).tm with hH
  set c₀ : Cfg (max Em.k Gm.k) Bool (BodyState Em.State Gm.State) x :=
    Cfg.ofWords .anchor (stateWord (max Em.k Gm.k) s) with hc₀
  set subc₀ : Cfg Em.k Bool Em.State x := Cfg.ofWords ee (stateWord Em.k s) with hsubc₀
  set subg₀ : Cfg Gm.k Bool Gm.State x := Cfg.ofWords ge (stateWord Gm.k s) with hsubg₀
  have htrE : ∀ q : Em.State, q ≠ ex → ∀ inp work,
      H.tr (.callE q) inp work =
        padAction (Nat.le_max_left Em.k Gm.k) (Option.map .callE)
          (Em.tm.tr q inp (fun i => work (Fin.castLE (Nat.le_max_left _ _) i))) := by
    intro q hq inp work
    simp [hH, emitIterBody, hq]
  have htrG : ∀ q : Gm.State, q ≠ gx → ∀ inp work,
      H.tr (.callG q) inp work =
        padAction (Nat.le_max_right Em.k Gm.k) (Option.map .callG)
          (Gm.tm.tr q inp (fun i => work (Fin.castLE (Nat.le_max_right _ _) i))) := by
    intro q hq inp work
    simp [hH, emitIterBody, hq]
  -- the first module step, fired from the anchor
  have hstep₁ : H.step c₀ =
      embedCfg (Nat.le_max_left Em.k Gm.k) (BodyState.callE (SG := Gm.State))
        (Em.tm.step subc₀) := by
    have h := embed_step (Nat.le_max_left Em.k Gm.k) Em.tm H
      (BodyState.callE (SG := Gm.State)) subc₀ ee rfl .anchor (fun inp work => rfl)
    have hcfg : ({ embedCfg (Nat.le_max_left Em.k Gm.k)
        (BodyState.callE (SG := Gm.State)) subc₀ with
        state := some .anchor } : Cfg (max Em.k Gm.k) Bool _ x) = c₀ := by
      rw [hsubc₀, embed_ofWords_left Em Gm ee hek]
      rfl
    rw [← hcfg]
    exact h
  -- the module chain after the first step
  have hEsome : ∀ j ≤ tE, ∃ q, (Em.tm.runFrom subc₀ j).state = some q := by
    intro j hj
    exact state_isSome_of_runFrom Em.tm (by rw [hErun]; rfl) hj
  have hone : Em.tm.runFrom subc₀ 1 = Em.tm.step subc₀ := by
    simp [MultiTapeTM.runFrom]
  have hEchain : ∀ u ≤ tE - 1,
      H.runFrom c₀ (1 + u) =
        embedCfg (Nat.le_max_left Em.k Gm.k) (BodyState.callE (SG := Gm.State))
          (Em.tm.runFrom subc₀ (1 + u)) := by
    intro u hu
    rw [runFrom_add, runFrom_one, hstep₁]
    rw [embed_run (Nat.le_max_left Em.k Gm.k) Em.tm H
      (BodyState.callE (SG := Gm.State)) ex htrE (Em.tm.step subc₀) u ?hstates]
    · rw [runFrom_add, hone]
    case hstates =>
      intro j hj
      have hj1 : 1 + j ≤ tE := by omega
      obtain ⟨q, hq⟩ := hEsome (1 + j) hj1
      rw [runFrom_add, hone] at hq
      refine ⟨q, hq, ?_⟩
      intro hqex
      subst hqex
      have := hEfirst (1 + j) (by omega) (by omega)
      rw [runFrom_add, hone] at this
      exact this hq
  -- checkpoint A: after tE steps, at the handoff state with the chunk emitted
  have hA : H.runFrom c₀ tE =
      { Cfg.ofWords (BodyState.callE ex) (stateWord (max Em.k Gm.k) s)
          with output := es } := by
    have h := hEchain (tE - 1) le_rfl
    rw [show 1 + (tE - 1) = tE from by omega] at h
    rw [h, hErun]
    rw [embedCfg_output, embed_ofWords_left Em Gm ex hek]
  -- checkpoint B: the control handoff
  have hB : H.runFrom c₀ (tE + 1) =
      { Cfg.ofWords BodyState.gStart (stateWord (max Em.k Gm.k) s)
          with output := es } := by
    rw [runFrom_add, hA, runFrom_one, control_step (q := BodyState.callE ex) ?_ rfl]
    · rfl
    · intro inp work
      simp [hH, emitIterBody]
  -- the install chain, lifted along the emitted prefix
  have hstep₂ : H.step (Cfg.ofWords (BodyState.gStart (SE := Em.State) (SG := Gm.State))
        (stateWord (max Em.k Gm.k) s)) =
      embedCfg (Nat.le_max_right Em.k Gm.k) (BodyState.callG (SE := Em.State))
        (Gm.tm.step subg₀) := by
    have h := embed_step (Nat.le_max_right Em.k Gm.k) Gm.tm H
      (BodyState.callG (SE := Em.State)) subg₀ ge rfl
      (BodyState.gStart (SE := Em.State) (SG := Gm.State)) (fun inp work => rfl)
    have hcfg : ({ embedCfg (Nat.le_max_right Em.k Gm.k)
        (BodyState.callG (SE := Em.State)) subg₀ with
        state := some (BodyState.gStart (SE := Em.State) (SG := Gm.State)) } :
          Cfg (max Em.k Gm.k) Bool (BodyState Em.State Gm.State) x) =
        Cfg.ofWords BodyState.gStart (stateWord (max Em.k Gm.k) s) := by
      rw [hsubg₀, embed_ofWords_right Em Gm ge hgk]
      rfl
    rw [← hcfg]
    exact h
  have hGsome : ∀ j ≤ tG, ∃ q, (Gm.tm.runFrom subg₀ j).state = some q := by
    intro j hj
    exact state_isSome_of_runFrom Gm.tm (by rw [hGrun]; rfl) hj
  have honeG : Gm.tm.runFrom subg₀ 1 = Gm.tm.step subg₀ := by
    simp [MultiTapeTM.runFrom]
  have hGchain : ∀ u ≤ tG - 1,
      H.runFrom (Cfg.ofWords (BodyState.gStart (SE := Em.State) (SG := Gm.State)) (stateWord (max Em.k Gm.k) s)) (1 + u) =
        embedCfg (Nat.le_max_right Em.k Gm.k) (BodyState.callG (SE := Em.State))
          (Gm.tm.runFrom subg₀ (1 + u)) := by
    intro u hu
    rw [runFrom_add, runFrom_one, hstep₂]
    rw [embed_run (Nat.le_max_right Em.k Gm.k) Gm.tm H
      (BodyState.callG (SE := Em.State)) gx htrG (Gm.tm.step subg₀) u ?hstatesG]
    · rw [runFrom_add, honeG]
    case hstatesG =>
      intro j hj
      have hj1 : 1 + j ≤ tG := by omega
      obtain ⟨q, hq⟩ := hGsome (1 + j) hj1
      rw [runFrom_add, honeG] at hq
      refine ⟨q, hq, ?_⟩
      intro hqex
      subst hqex
      have := hGfirst (1 + j) (by omega) (by omega)
      rw [runFrom_add, honeG] at this
      exact this hq
  have hGout : ∀ u ≤ tG, 1 ≤ u →
      H.runFrom c₀ (tE + 1 + u) =
        { embedCfg (Nat.le_max_right Em.k Gm.k) (BodyState.callG (SE := Em.State))
            (Gm.tm.runFrom subg₀ u) with output := es } := by
    intro u hu h1u
    rw [show tE + 1 + u = (tE + 1) + u from rfl, runFrom_add, hB]
    have hpre : ({ Cfg.ofWords BodyState.gStart (stateWord (max Em.k Gm.k) s)
        with output := es } : Cfg (max Em.k Gm.k) Bool (BodyState Em.State Gm.State) x) =
        { (Cfg.ofWords BodyState.gStart (stateWord (max Em.k Gm.k) s) :
            Cfg (max Em.k Gm.k) Bool (BodyState Em.State Gm.State) x) with
          output := es ++ (Cfg.ofWords (input := x)
            (BodyState.gStart (SE := Em.State) (SG := Gm.State))
            (stateWord (max Em.k Gm.k) s)).output } := by
      simp [Cfg.ofWords]
    have hsubout : (Gm.tm.runFrom subg₀ u).output = [] := by
      obtain ⟨o2, h2⟩ := runFrom_output_extends Gm.tm (Gm.tm.runFrom subg₀ u) (tG - u)
      rw [← runFrom_add, show u + (tG - u) = tG from by omega, hGrun] at h2
      have : ([] : List Bool) = (Gm.tm.runFrom subg₀ u).output ++ o2 := h2
      exact (List.append_eq_nil_iff.mp this.symm).1
    rw [hpre, runFrom_output_prefix]
    obtain ⟨u', rfl⟩ : ∃ u', u = 1 + u' := ⟨u - 1, by omega⟩
    rw [hGchain u' (by omega)]
    rw [show (embedCfg (Nat.le_max_right Em.k Gm.k) (BodyState.callG (SE := Em.State))
      (Gm.tm.runFrom subg₀ (1 + u'))).output = [] from hsubout, List.append_nil]
  -- checkpoint C and the final control return
  have hC : H.runFrom c₀ (tE + 1 + tG) =
      { Cfg.ofWords (BodyState.callG gx) (stateWord (max Em.k Gm.k) gs)
          with output := es } := by
    rw [hGout tG le_rfl (by omega), hGrun, embed_ofWords_right Em Gm gx hgk]
  constructor
  · rw [show tE + 1 + tG + 1 = (tE + 1 + tG) + 1 from rfl, runFrom_add, hC,
      runFrom_one, control_step (q := BodyState.callG gx) ?_ rfl]
    · rfl
    · intro inp work
      simp [hH, emitIterBody]
  · intro t' ht'0 ht'
    rcases lt_trichotomy t' (tE + 1) with hlt | heq | hgt
    · rcases Nat.lt_or_ge t' tE with hltE | hgeE
      · obtain ⟨u, rfl⟩ : ∃ u, t' = 1 + u := ⟨t' - 1, by omega⟩
        rw [hEchain u (by omega)]
        obtain ⟨q, hq⟩ := hEsome (1 + u) (by omega)
        simp [embedCfg, hq]
      · have he : t' = tE := by omega
        subst he
        rw [hA]
        simp [Cfg.ofWords]
    · subst heq
      rw [hB]
      simp [Cfg.ofWords]
    · obtain ⟨u, rfl⟩ : ∃ u, t' = tE + 1 + u := ⟨t' - (tE + 1), by omega⟩
      rw [hGout u (by omega) (by omega)]
      obtain ⟨q, hq⟩ := hGsome u (by omega)
      simp [embedCfg, hq]

/-! #### The startup copier -/

/-- The copy-phase configuration: the first `i` input symbols already written
on tape zero, both heads past them. -/
private def copyCfg (x : List Bool) (i : ℕ) (hi : i ≤ x.length) :
    Cfg (max Em.k Gm.k) Bool (BodyState Em.State Gm.State) x :=
  ⟨some .copy, ⟨i + 1, by omega⟩,
    fun j => if (j : ℕ) = 0 then FinTM.bufferTape (x.take i) else fun _ => none,
    fun j => if (j : ℕ) = 0 then (i : ℤ) else 0, []⟩

/-- A rewind-phase configuration: the whole input on tape zero, the input
head at `p`, the tape-zero head at `z`. -/
private def fullCfg (x : List Bool) (st : BodyState Em.State Gm.State)
    (p : ℕ) (hp : p < x.length + 2) (z : ℤ) :
    Cfg (max Em.k Gm.k) Bool (BodyState Em.State Gm.State) x :=
  ⟨some st, ⟨p, hp⟩,
    fun j => if (j : ℕ) = 0 then FinTM.bufferTape x else fun _ => none,
    fun j => if (j : ℕ) = 0 then z else 0, []⟩

/-- The body's initial configuration is the empty copy configuration. -/
private theorem initCfg_eq_copyCfg (hek : 0 < Em.k) (x : List Bool) :
    (emitIterBody Em Gm hek ee ex ge gx).tm.initCfg x =
      copyCfg Em Gm x 0 (Nat.zero_le _) := by
  refine Cfg.ext rfl (Fin.ext (by simp [copyCfg])) ?_ ?_ rfl
  · funext j
    by_cases hj : (j : ℕ) = 0 <;>
      simp [copyCfg, emitIterBody, hj, MultiTapeTM.initCfg, Cfg.init]
  · funext j
    by_cases hj : (j : ℕ) = 0 <;>
      simp [copyCfg, emitIterBody, hj, MultiTapeTM.initCfg, Cfg.init]

/-- One copy step: read the next input symbol, write it, advance both heads.
**Proof sketch.** The input symbol under the head is the `i`-th input bit;
the applied action writes it at tape-zero cell `i` (`bufferTape_append`
extends the copied prefix) and moves both heads right. -/
private theorem copy_step (hek : 0 < Em.k) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (emitIterBody Em Gm hek ee ex ge gx).tm.step (copyCfg Em Gm x i (le_of_lt hi)) =
      copyCfg Em Gm x (i + 1) hi := by
  have hinp : (copyCfg Em Gm x i (le_of_lt hi)).inputSymbol = some x[i] :=
    inputSymbolInner i (by simp only [copyCfg]; omega) hi
  have h1 : (emitIterBody Em Gm hek ee ex ge gx).tm.step (copyCfg Em Gm x i (le_of_lt hi)) =
      ((emitIterBody Em Gm hek ee ex ge gx).tm.tr .copy
        (copyCfg Em Gm x i (le_of_lt hi)).inputSymbol
        (copyCfg Em Gm x i (le_of_lt hi)).workTapeSymbols).apply
        (copyCfg Em Gm x i (le_of_lt hi)) := rfl
  rw [h1, hinp]
  have htake : x.take (i + 1) = x.take i ++ [x[i]] := by
    rw [List.take_succ, List.getElem?_eq_getElem hi]
    rfl
  have hlen : ((x.take i).length : ℤ) = (i : ℤ) := by
    simp [List.length_take, Nat.min_eq_left (le_of_lt hi)]
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · show moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) .pos = _
    rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]
    rfl
  · funext j
    by_cases hj : (j : ℕ) = 0
    · simp only [emitIterBody, Action.apply, copyCfg, hj, if_pos]
      rw [htake, FinTM.bufferTape_append, hlen]
    · simp [emitIterBody, Action.apply, copyCfg, hj]
  · funext j
    by_cases hj : (j : ℕ) = 0
    · simp only [emitIterBody, Action.apply, copyCfg, hj, if_pos]
      simp only [SignType.coe_one]
      omega
    · simp [emitIterBody, Action.apply, copyCfg, hj]

/-- The copy phase ends at the right input boundary and starts the tape
rewind.
**Proof sketch.** At the right boundary the input read is blank, so the
copy state's other branch fires: the input head stays, tape zero (now
holding the whole input, `List.take_length`) steps left. -/
private theorem copy_end (hek : 0 < Em.k) (x : List Bool) :
    (emitIterBody Em Gm hek ee ex ge gx).tm.step (copyCfg Em Gm x x.length le_rfl) =
      fullCfg Em Gm x .rwTape (x.length + 1) (by omega) ((x.length : ℤ) - 1) := by
  have hinp : (copyCfg Em Gm x x.length le_rfl).inputSymbol = none := by
    have h := FinTM.inputSymbol_at (copyCfg Em Gm x x.length le_rfl) x.length le_rfl
      (by simp [copyCfg])
    simpa using h
  have h1 : (emitIterBody Em Gm hek ee ex ge gx).tm.step (copyCfg Em Gm x x.length le_rfl) =
      ((emitIterBody Em Gm hek ee ex ge gx).tm.tr .copy
        (copyCfg Em Gm x x.length le_rfl).inputSymbol
        (copyCfg Em Gm x x.length le_rfl).workTapeSymbols).apply
        (copyCfg Em Gm x x.length le_rfl) := rfl
  rw [h1, hinp]
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · show moveInputPos (⟨x.length + 1, by omega⟩ : Fin (x.length + 2)) 0 = _
    rw [moveInputPos_zero]
    rfl
  · funext j
    by_cases hj : (j : ℕ) = 0
    · simp only [emitIterBody, Action.apply, copyCfg, fullCfg, hj, if_pos]
      rw [List.take_length]
    · simp [emitIterBody, Action.apply, copyCfg, fullCfg, hj]
  · funext j
    by_cases hj : (j : ℕ) = 0
    · simp only [emitIterBody, Action.apply, copyCfg, fullCfg, hj, if_pos,
        SignType.neg_eq_neg_one, SignType.coe_neg_one]
      omega
    · simp [emitIterBody, Action.apply, copyCfg, fullCfg, hj]

/-- One tape-rewind step over a written cell.
**Proof sketch.** The tape-zero read at cell `j` is the `j`-th copied bit,
so the rewind state keeps moving left; only the head position changes. -/
private theorem rwTape_some (hek : 0 < Em.k) (x : List Bool) (j : ℕ) (hj : j < x.length) :
    (emitIterBody Em Gm hek ee ex ge gx).tm.step
        (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (j : ℤ)) =
      fullCfg Em Gm x .rwTape (x.length + 1) (by omega) ((j : ℤ) - 1) := by
  have hw : (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (j : ℤ)).workTapeSymbols
      ⟨0, Nat.lt_of_lt_of_le hek (Nat.le_max_left Em.k Gm.k)⟩ = some x[j] := by
    simp only [fullCfg, Cfg.workTapeSymbols]
    simp [List.getElem?_eq_getElem hj]
  have h1 : (emitIterBody Em Gm hek ee ex ge gx).tm.step
      (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (j : ℤ)) =
      ((emitIterBody Em Gm hek ee ex ge gx).tm.tr .rwTape
        (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (j : ℤ)).inputSymbol
        (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (j : ℤ)).workTapeSymbols).apply
        (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (j : ℤ)) := rfl
  have htr : (emitIterBody Em Gm hek ee ex ge gx).tm.tr .rwTape
      (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (j : ℤ)).inputSymbol
      (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (j : ℤ)).workTapeSymbols =
      ⟨0, fun i => if (i : ℕ) = 0 then (none, -1) else (none, 0), none, some .rwTape⟩ := by
    simp only [emitIterBody]
    rw [hw]
  rw [h1, htr]
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · show moveInputPos (⟨x.length + 1, by omega⟩ : Fin (x.length + 2)) 0 = _
    rw [moveInputPos_zero]
    rfl
  · funext i
    by_cases hi : (i : ℕ) = 0 <;> simp [Action.apply, fullCfg, hi]
  · funext i
    by_cases hi : (i : ℕ) = 0
    · simp only [Action.apply, fullCfg, hi, if_pos, SignType.neg_eq_neg_one,
        SignType.coe_neg_one]
      omega
    · simp [Action.apply, fullCfg, hi]

/-- The tape rewind reaches the left blank and turns the head back to the
origin.
**Proof sketch.** Cell `-1` is blank (`bufferTape_left`), so the rewind
state's blank branch fires: the head steps right to the origin and control
moves to the input rewind. -/
private theorem rwTape_none (hek : 0 < Em.k) (x : List Bool) :
    (emitIterBody Em Gm hek ee ex ge gx).tm.step
        (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (-1)) =
      fullCfg Em Gm x .rwInput0 (x.length + 1) (by omega) 0 := by
  have hw : (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (-1)).workTapeSymbols
      ⟨0, Nat.lt_of_lt_of_le hek (Nat.le_max_left Em.k Gm.k)⟩ = none := by
    simp only [fullCfg, Cfg.workTapeSymbols]
    simp
  have h1 : (emitIterBody Em Gm hek ee ex ge gx).tm.step
      (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (-1)) =
      ((emitIterBody Em Gm hek ee ex ge gx).tm.tr .rwTape
        (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (-1)).inputSymbol
        (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (-1)).workTapeSymbols).apply
        (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (-1)) := rfl
  have htr : (emitIterBody Em Gm hek ee ex ge gx).tm.tr .rwTape
      (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (-1)).inputSymbol
      (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (-1)).workTapeSymbols =
      ⟨0, fun i => if (i : ℕ) = 0 then (none, 1) else (none, 0), none, some .rwInput0⟩ := by
    simp only [emitIterBody]
    rw [hw]
  rw [h1, htr]
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · show moveInputPos (⟨x.length + 1, by omega⟩ : Fin (x.length + 2)) 0 = _
    rw [moveInputPos_zero]
    rfl
  · funext i
    by_cases hi : (i : ℕ) = 0 <;> simp [Action.apply, fullCfg, hi]
  · funext i
    by_cases hi : (i : ℕ) = 0
    · simp only [Action.apply, fullCfg, hi, if_pos, SignType.coe_one]
      omega
    · simp [Action.apply, fullCfg, hi]

/-- The input rewind's unconditional first move. -/
private theorem rwIn0_step (hek : 0 < Em.k) (x : List Bool) :
    (emitIterBody Em Gm hek ee ex ge gx).tm.step
        (fullCfg Em Gm x .rwInput0 (x.length + 1) (by omega) 0) =
      fullCfg Em Gm x .rwInput x.length (by omega) 0 := by
  rw [control_step' (mv := .neg) (r := BodyState.rwInput) (fun _ _ => rfl) rfl]
  refine Cfg.ext rfl ?_ rfl rfl rfl
  show moveInputPos (⟨x.length + 1, by omega⟩ : Fin (x.length + 2)) .neg = _
  rw [moveInputPos_neg_of_ne_left _ (by
    intro h
    have := congrArg Fin.val h
    simp at this)]
  rfl

/-- One input-rewind step over an input symbol.
**Proof sketch.** At interior position `p ≥ 1` the input read is the
`(p-1)`-st bit, so the rewind keeps moving left
(`moveInputPos_neg_of_ne_left`); nothing else changes. -/
private theorem rwInput_some (hek : 0 < Em.k) (x : List Bool) (p : ℕ)
    (hp1 : 1 ≤ p) (hpn : p ≤ x.length) :
    (emitIterBody Em Gm hek ee ex ge gx).tm.step
        (fullCfg Em Gm x .rwInput p (by omega) 0) =
      fullCfg Em Gm x .rwInput (p - 1) (by omega) 0 := by
  have hinp : (fullCfg Em Gm x .rwInput p (by omega) 0).inputSymbol = some x[p - 1] :=
    inputSymbolInner (p - 1) (by simp only [fullCfg]; omega) (by omega)
  have h1 : (emitIterBody Em Gm hek ee ex ge gx).tm.step
      (fullCfg Em Gm x .rwInput p (by omega) 0) =
      ((emitIterBody Em Gm hek ee ex ge gx).tm.tr .rwInput
        (fullCfg Em Gm x .rwInput p (by omega) 0).inputSymbol
        (fullCfg Em Gm x .rwInput p (by omega) 0).workTapeSymbols).apply
        (fullCfg Em Gm x .rwInput p (by omega) 0) := rfl
  rw [h1, hinp]
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · show moveInputPos (⟨p, by omega⟩ : Fin (x.length + 2)) .neg = _
    rw [moveInputPos_neg_of_ne_left _ (by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega)]
    rfl
  · funext i
    by_cases hi : (i : ℕ) = 0 <;>
      simp [emitIterBody, FinTM.controlAction, Action.apply, fullCfg, hi]
  · funext i
    by_cases hi : (i : ℕ) = 0 <;>
      simp [emitIterBody, FinTM.controlAction, Action.apply, fullCfg, hi]

/-- The input rewind reaches the left boundary and enters the anchor seam.
**Proof sketch.** At position zero the input read is blank, so the final
branch fires: the head steps right to the canonical position one and control
enters the anchor; the resulting configuration is literally the
`Cfg.ofWords` seam carrying the copied input on tape zero. -/
private theorem rwInput_zero (hek : 0 < Em.k) (x : List Bool) :
    (emitIterBody Em Gm hek ee ex ge gx).tm.step
        (fullCfg Em Gm x .rwInput 0 (by omega) 0) =
      Cfg.ofWords .anchor (stateWord (max Em.k Gm.k) x) := by
  have hinp : (fullCfg Em Gm x .rwInput 0 (by omega) 0).inputSymbol = none := by
    simp only [fullCfg, Cfg.inputSymbol]
    rw [dif_pos (by apply Fin.ext; simp)]
  have h1 : (emitIterBody Em Gm hek ee ex ge gx).tm.step
      (fullCfg Em Gm x .rwInput 0 (by omega) 0) =
      ((emitIterBody Em Gm hek ee ex ge gx).tm.tr .rwInput
        (fullCfg Em Gm x .rwInput 0 (by omega) 0).inputSymbol
        (fullCfg Em Gm x .rwInput 0 (by omega) 0).workTapeSymbols).apply
        (fullCfg Em Gm x .rwInput 0 (by omega) 0) := rfl
  rw [h1, hinp]
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · show moveInputPos (⟨0, by omega⟩ : Fin (x.length + 2)) .pos = _
    rw [moveInputPos_pos_of_ne_right _ (by simp)]
    apply Fin.ext
    simp [Cfg.ofWords]
  · funext i
    by_cases hi : (i : ℕ) = 0
    · simp [emitIterBody, FinTM.controlAction, Action.apply, fullCfg, Cfg.ofWords,
        stateWord, hi]
    · simp [emitIterBody, FinTM.controlAction, Action.apply, fullCfg, Cfg.ofWords,
        stateWord, hi]
  · funext i
    by_cases hi : (i : ℕ) = 0 <;>
      simp [emitIterBody, FinTM.controlAction, Action.apply, fullCfg, Cfg.ofWords, hi]

/-- **The startup segment.** From its initial configuration the body copies
the input onto tape zero, rewinds both heads, and enters the anchor seam
carrying the input, within `3·|x| + 4` steps and without visiting the anchor
earlier.
**Proof sketch.** Chain the safe runs of the four phases: `|x|` copy steps,
the boundary turnaround, `|x| + 1` tape-rewind steps, the unconditional
input-rewind entry, and `|x| + 1` input-rewind steps, each phase by
induction on its counter; every visited state is a copier state, never the
anchor. -/
private theorem body_start (hek : 0 < Em.k) :
    SafeRun (emitIterBody Em Gm hek ee ex ge gx).tm .anchor
      ((emitIterBody Em Gm hek ee ex ge gx).tm.initCfg x) (3 * x.length + 4)
      (Cfg.ofWords .anchor (stateWord (max Em.k Gm.k) x)) := by
  have hcopy : ∀ i (hi : i ≤ x.length),
      SafeRun (emitIterBody Em Gm hek ee ex ge gx).tm .anchor
        (copyCfg Em Gm x 0 (Nat.zero_le _)) i (copyCfg Em Gm x i hi) := by
    intro i
    induction i with
    | zero => intro _; exact SafeRun.zero
    | succ i ih =>
      intro hi
      exact SafeRun.trans (ih (by omega))
        (SafeRun.cons (copy_step Em Gm ee ex ge gx hek x i (by omega))
          (by simp [copyCfg]) SafeRun.zero)
  have hrwt : ∀ j (hj : j ≤ x.length),
      SafeRun (emitIterBody Em Gm hek ee ex ge gx).tm .anchor
        (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) ((j : ℤ) - 1)) (j + 1)
        (fullCfg Em Gm x .rwInput0 (x.length + 1) (by omega) 0) := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [show ((0 : ℕ) : ℤ) - 1 = -1 from by omega]
      exact SafeRun.cons (rwTape_none Em Gm ee ex ge gx hek x) (by simp [fullCfg])
        SafeRun.zero
    | succ j ih =>
      intro hj
      rw [show ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) from by push_cast; ring]
      exact SafeRun.cons (rwTape_some Em Gm ee ex ge gx hek x j (by omega))
        (by simp [fullCfg]) (ih (by omega))
  have hrwi : ∀ p (hp : p ≤ x.length),
      SafeRun (emitIterBody Em Gm hek ee ex ge gx).tm .anchor
        (fullCfg Em Gm x .rwInput p (by omega) 0) (p + 1)
        (Cfg.ofWords .anchor (stateWord (max Em.k Gm.k) x)) := by
    intro p
    induction p with
    | zero =>
      intro _
      exact SafeRun.cons (rwInput_zero Em Gm ee ex ge gx hek x) (by simp [fullCfg])
        SafeRun.zero
    | succ p ih =>
      intro hp
      exact SafeRun.cons (rwInput_some Em Gm ee ex ge gx hek x (p + 1) (by omega) hp)
        (by simp [fullCfg]) (ih (by omega))
  have hchain := ((((hcopy x.length le_rfl).trans
    (SafeRun.cons (copy_end Em Gm ee ex ge gx hek x) (by simp [copyCfg]) SafeRun.zero)).trans
    (hrwt x.length le_rfl)).trans
    (SafeRun.cons (rwIn0_step Em Gm ee ex ge gx hek x) (by simp [fullCfg]) SafeRun.zero)).trans
    (hrwi x.length le_rfl)
  rw [initCfg_eq_copyCfg]
  rw [show 3 * x.length + 4 =
    x.length + (0 + 1) + (x.length + 1) + (0 + 1) + (x.length + 1) from by omega]
  exact hchain

end Body

/-- **The emit-iteration machine** ([AB09] §7.3–§7.4 folklore: simulate a
machine on polynomially many rounds and concatenate the outcomes).  Given
machines computing the step `g` and the chunk `e` within polynomial budgets,
and a polynomial length envelope for the orbit of `g`, one finite machine
computes the concatenation of the chunks `e (g^[i] w)` for
`i = 0, …, a'·(|w|+1)^k'`, within a polynomial budget in the `C·(n+1)^c`
normal form.

**Proof sketch.** Instantiate `Turing.FinTM.exists_emitLoopTM` at the body
machine `emitIterBody` built from the two clean-call modules
(`exists_emitCallTM` for `e`, `exists_installCallTM` for `g`), the
polynomial-bits fuel machine (`computesFunInTime_polyBits`), the orbit
invariant `∃ i, s = g^[i] w`, and the budget `T` summing the fuel, startup,
and round envelopes; `body_start` and `body_round` discharge the startup and
round obligations, with the call budgets bounded through the orbit envelope
and the one-symbol-per-step output bound.  The loop host's
`c·(T+1)·(R+2)` budget is then absorbed into the polynomial normal form. -/
theorem FinTM.exists_emitIterTM (G E : FinTM Bool) (g e : List Bool → List Bool)
    (CG cG CE cE : ℕ)
    (hG : G.ComputesFunInTime g (fun n => CG * (n + 1) ^ cG))
    (hE : E.ComputesFunInTime e (fun n => CE * (n + 1) ^ cE))
    (a' k' b l : ℕ)
    (horbit : ∀ (w : List Bool) (i : ℕ), (g^[i] w).length ≤ b * (w.length + 1) ^ l) :
    ∃ (M : FinTM Bool) (C c : ℕ),
      M.ComputesFunInTime
        (fun w => (List.range (a' * (w.length + 1) ^ k' + 1)).flatMap
          (fun i => e (g^[i] w)))
        (fun n => C * (n + 1) ^ c) := by
  classical
  obtain ⟨Ce, eentry, eexit, cEcall, hke, hEcall⟩ :=
    FinTM.exists_emitCallTM E e _ hE
  obtain ⟨Cg, gentry, gexit, cGcall, hkg, hGcall⟩ :=
    FinTM.exists_installCallTM G g _ hG
  obtain ⟨F, cF, hF⟩ := FinTM.computesFunInTime_polyBits a' k'
  -- output-length bounds from the one-symbol-per-step discipline
  have hElen : ∀ s : List Bool, (e s).length ≤ CE * (s.length + 1) ^ cE := by
    intro s
    have hout := ((FinTM.computesInTime_iff _ _ _ _).mp (hE s)).2
    simpa only [hout] using E.tm.output_length_le s (CE * (s.length + 1) ^ cE)
  have hGlen : ∀ s : List Bool, (g s).length ≤ CG * (s.length + 1) ^ cG := by
    intro s
    have hout := ((FinTM.computesInTime_iff _ _ _ _).mp (hG s)).2
    simpa only [hout] using G.tm.output_length_le s (CG * (s.length + 1) ^ cG)
  -- the budget
  set L : ℕ → ℕ := fun n => b * (n + 1) ^ l with hL
  set TEb : ℕ → ℕ := fun n => CE * (L n + 1) ^ cE with hTEb
  set TGb : ℕ → ℕ := fun n => CG * (L n + 1) ^ cG with hTGb
  set T : ℕ → ℕ := fun n => cF * (n + 1) ^ (k' + 1) + (3 * n + 4) +
    (cEcall * (2 * TEb n + L n + 1) + cGcall * (2 * TGb n + L n + 1) + 2) with hT
  set body := emitIterBody Ce Cg hke eentry eexit gentry gexit with hbody
  have hF' : F.ComputesFunInTime
      (fun x => Nat.bits (a' * (x.length + 1) ^ k')) T := by
    intro x
    refine (hF x).mono ?_
    simp only [hT]
    omega
  have hstart : ∀ x : List Bool, ∃ t ≤ T x.length,
      (∀ t' < t, (body.tm.runFrom (body.tm.initCfg x) t').state ≠
        some BodyState.anchor) ∧
      body.tm.runFrom (body.tm.initCfg x) t =
        Cfg.ofWords .anchor (stateWord body.k x) := by
    intro x
    obtain ⟨hrun, hsafe⟩ := body_start Ce Cg eentry eexit gentry gexit hke (x := x)
    exact ⟨3 * x.length + 4, by simp only [hT]; omega, hsafe, hrun⟩
  have hround : ∀ (x s : List Bool), (∃ i, s = g^[i] x) →
      ∃ t, 0 < t ∧ t ≤ T x.length ∧
        (∀ t', 0 < t' → t' < t →
          (body.tm.runFrom
            (Cfg.ofWords (input := x) .anchor (stateWord body.k s)) t').state ≠
              some BodyState.anchor) ∧
        body.tm.runFrom
          (Cfg.ofWords (input := x) .anchor (stateWord body.k s)) t =
            { Cfg.ofWords .anchor (stateWord body.k (g s)) with output := e s } := by
    rintro x s ⟨i, rfl⟩
    set s := g^[i] x with hs
    have hsL : s.length ≤ L x.length := horbit x i
    obtain ⟨tEc, htEb', htEpos, hEfirst, hErun⟩ := hEcall x s
    obtain ⟨tGc, htGb', htGpos, hGfirst, hGrun⟩ := hGcall x s
    obtain ⟨hrun, hsafe⟩ := body_round Ce Cg eentry eexit gentry gexit hke hkg
      (x := x) s (e s) (g s) tEc htEpos hEfirst hErun tGc htGpos hGfirst hGrun
    refine ⟨tEc + 1 + tGc + 1, by omega, ?_, hsafe, hrun⟩
    have hpow : s.length + 1 ≤ L x.length + 1 := by omega
    have hTEs : CE * (s.length + 1) ^ cE ≤ TEb x.length :=
      Nat.mul_le_mul_left CE (Nat.pow_le_pow_left hpow cE)
    have hTGs : CG * (s.length + 1) ^ cG ≤ TGb x.length :=
      Nat.mul_le_mul_left CG (Nat.pow_le_pow_left hpow cG)
    have hes := hElen s
    have hgs := hGlen s
    have htE2 : tEc ≤ cEcall * (2 * TEb x.length + L x.length + 1) :=
      le_trans htEb' (Nat.mul_le_mul_left cEcall (by omega))
    have htG2 : tGc ≤ cGcall * (2 * TGb x.length + L x.length + 1) :=
      le_trans htGb' (Nat.mul_le_mul_left cGcall (by omega))
    simp only [hT]
    omega
  obtain ⟨M, c, hM⟩ := FinTM.exists_emitLoopTM body F .anchor
    (fun w s => ∃ i, s = g^[i] w) (fun _ s => g s) (fun _ s => e s)
    (fun w => w) (fun n => a' * (n + 1) ^ k') T hF'
    (fun w => ⟨0, rfl⟩)
    (fun w s hs => by
      obtain ⟨i, rfl⟩ := hs
      exact ⟨i + 1, (Function.iterate_succ_apply' g i w).symm⟩)
    hstart hround
  -- polynomial normal form
  set D : ℕ := k' + 1 + l * cE + l * cG + l + 1 with hD
  have honeD : ∀ n : ℕ, 1 ≤ (n + 1) ^ D := fun n => Nat.one_le_pow _ _ (by omega)
  have hTle : ∀ n, T n ≤
      (cF + 4 + cEcall * (2 * CE * (b + 1) ^ cE + b + 2) +
        cGcall * (2 * CG * (b + 1) ^ cG + b + 2) + 2) * (n + 1) ^ D := by
    intro n
    have hone : 1 ≤ (n + 1) ^ l := Nat.one_le_pow _ _ (by omega)
    have hLb : L n + 1 ≤ (b + 1) * (n + 1) ^ l := by
      simp only [hL]
      calc b * (n + 1) ^ l + 1 ≤ b * (n + 1) ^ l + (n + 1) ^ l := by omega
        _ = (b + 1) * (n + 1) ^ l := by ring
    have hpowD : ∀ a : ℕ, a ≤ D → (n + 1) ^ a ≤ (n + 1) ^ D :=
      fun a ha => Nat.pow_le_pow_right (by omega) ha
    have hTEbn : TEb n ≤ CE * (b + 1) ^ cE * (n + 1) ^ (l * cE) := by
      simp only [hTEb]
      calc CE * (L n + 1) ^ cE ≤ CE * ((b + 1) * (n + 1) ^ l) ^ cE :=
            Nat.mul_le_mul_left CE (Nat.pow_le_pow_left hLb cE)
        _ = CE * (b + 1) ^ cE * (n + 1) ^ (l * cE) := by
            rw [mul_pow, ← pow_mul]
            ring
    have hTGbn : TGb n ≤ CG * (b + 1) ^ cG * (n + 1) ^ (l * cG) := by
      simp only [hTGb]
      calc CG * (L n + 1) ^ cG ≤ CG * ((b + 1) * (n + 1) ^ l) ^ cG :=
            Nat.mul_le_mul_left CG (Nat.pow_le_pow_left hLb cG)
        _ = CG * (b + 1) ^ cG * (n + 1) ^ (l * cG) := by
            rw [mul_pow, ← pow_mul]
            ring
    have h1 : cF * (n + 1) ^ (k' + 1) ≤ cF * (n + 1) ^ D :=
      Nat.mul_le_mul_left cF (hpowD _ (by omega))
    have h2 : 3 * n + 4 ≤ 4 * (n + 1) ^ D := by
      have : n + 1 ≤ (n + 1) ^ D := le_trans (by omega)
        (Nat.le_self_pow (by omega) (n + 1))
      omega
    have h3 : TEb n ≤ CE * (b + 1) ^ cE * (n + 1) ^ D :=
      le_trans hTEbn (Nat.mul_le_mul_left _ (hpowD _ (by omega)))
    have h4 : TGb n ≤ CG * (b + 1) ^ cG * (n + 1) ^ D :=
      le_trans hTGbn (Nat.mul_le_mul_left _ (hpowD _ (by omega)))
    have h5 : L n + 1 ≤ (b + 1) * (n + 1) ^ D :=
      le_trans hLb (Nat.mul_le_mul_left _ (hpowD _ (by omega)))
    have hE3 : cEcall * (2 * TEb n + L n + 1) ≤
        cEcall * (2 * CE * (b + 1) ^ cE + b + 2) * (n + 1) ^ D := by
      rw [Nat.mul_assoc]
      refine Nat.mul_le_mul_left cEcall ?_
      calc 2 * TEb n + L n + 1 ≤
            2 * (CE * (b + 1) ^ cE * (n + 1) ^ D) + (b + 1) * (n + 1) ^ D +
              (n + 1) ^ D := by
            have := honeD n
            omega
        _ = (2 * CE * (b + 1) ^ cE + b + 2) * (n + 1) ^ D := by ring
    have hG3 : cGcall * (2 * TGb n + L n + 1) ≤
        cGcall * (2 * CG * (b + 1) ^ cG + b + 2) * (n + 1) ^ D := by
      rw [Nat.mul_assoc]
      refine Nat.mul_le_mul_left cGcall ?_
      calc 2 * TGb n + L n + 1 ≤
            2 * (CG * (b + 1) ^ cG * (n + 1) ^ D) + (b + 1) * (n + 1) ^ D +
              (n + 1) ^ D := by
            have := honeD n
            omega
        _ = (2 * CG * (b + 1) ^ cG + b + 2) * (n + 1) ^ D := by ring
    have h6 : 2 ≤ 2 * (n + 1) ^ D := by
      have := honeD n
      omega
    simp only [hT]
    calc cF * (n + 1) ^ (k' + 1) + (3 * n + 4) +
          (cEcall * (2 * TEb n + L n + 1) + cGcall * (2 * TGb n + L n + 1) + 2) ≤
        cF * (n + 1) ^ D + 4 * (n + 1) ^ D +
          (cEcall * (2 * CE * (b + 1) ^ cE + b + 2) * (n + 1) ^ D +
            cGcall * (2 * CG * (b + 1) ^ cG + b + 2) * (n + 1) ^ D +
            2 * (n + 1) ^ D) :=
          Nat.add_le_add (Nat.add_le_add h1 h2)
            (Nat.add_le_add (Nat.add_le_add hE3 hG3) h6)
      _ = (cF + 4 + cEcall * (2 * CE * (b + 1) ^ cE + b + 2) +
            cGcall * (2 * CG * (b + 1) ^ cG + b + 2) + 2) * (n + 1) ^ D := by ring
  set K₀ : ℕ := cF + 4 + cEcall * (2 * CE * (b + 1) ^ cE + b + 2) +
    cGcall * (2 * CG * (b + 1) ^ cG + b + 2) + 2 with hK₀
  refine ⟨M, c * (K₀ + 1) * (a' + 2), D + k', fun w => ?_⟩
  have hMw := hM w
  refine hMw.mono ?_
  set n := w.length
  have hT1 : T n + 1 ≤ (K₀ + 1) * (n + 1) ^ D := by
    have h := hTle n
    have h1 := honeD n
    calc T n + 1 ≤ K₀ * (n + 1) ^ D + (n + 1) ^ D := by omega
      _ = (K₀ + 1) * (n + 1) ^ D := by ring
  have hR2 : a' * (n + 1) ^ k' + 2 ≤ (a' + 2) * (n + 1) ^ k' := by
    have h1 : 1 ≤ (n + 1) ^ k' := Nat.one_le_pow _ _ (by omega)
    calc a' * (n + 1) ^ k' + 2 ≤ a' * (n + 1) ^ k' + 2 * (n + 1) ^ k' := by omega
      _ = (a' + 2) * (n + 1) ^ k' := by ring
  calc c * (T n + 1) * (a' * (n + 1) ^ k' + 2) ≤
        c * ((K₀ + 1) * (n + 1) ^ D) * ((a' + 2) * (n + 1) ^ k') :=
      Nat.mul_le_mul (Nat.mul_le_mul_left c hT1) hR2
    _ = c * (K₀ + 1) * (a' + 2) * (n + 1) ^ (D + k') := by
      rw [pow_add]
      ring

end Turing
```

## ===== TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean =====

```
/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import Mathlib.Computability.Language
import TCSlib.Complexity.ClassNP.CounterProgPolyTime
import TCSlib.Complexity.ClassNP.PolyTimePairing
import TCSlib.Complexity.ClassNP.PolyTimePrefix
import TCSlib.Complexity.TuringMachine.CounterProgInput
import TCSlib.Complexity.TuringMachine.Build.Loop
import TCSlib.Complexity.TuringMachine.Build.Primitives
import TCSlib.Complexity.TuringMachine.Build.EmitIterBody

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The bounded block-query loop

The chapter-neutral composition primitive behind "run a `P`-decider on
polynomially many fixed-size blocks of the input and aggregate the answers":
the folklore closure of polynomial time under polynomial repetition, used
tacitly throughout [AB09] (§7.3, proof of Theorem 7.8; §7.4.1, repeated
trials; proofs of Theorems 7.17 and 7.18).

Everything here lives at the level of `Complexity.PolyTimeComputable`; the
`P`-closure corollaries (`Complexity.mem_P_of_blockAny` and friends) are
stated in `TCSlib.Complexity.ClassNP.PClosure`, which imports this file.

## Main definitions

* `Complexity.sliceTakeAt` / `Complexity.sliceDropAt` — keep the first
  component and take/drop a polynomial-length prefix of the second.
* `Complexity.xorD` — truncating bitwise XOR of the two components of a pair.

## Main results

* `Complexity.polyTimeComputable_emitIter` — the machine-level loop: iterating
  a polynomial-time step function a polynomial number of times, concatenating
  a polynomial-time chunk of each iterate, is polynomial-time, provided the
  iterates stay inside a polynomial length envelope.  This is the one genuinely
  new combinator; it is built on `Turing.FinTM.exists_emitLoopTM` with
  clean-call modules (`Turing.FinTM.exists_installCallTM` /
  `exists_emitCallTM`) as the per-round body.
* `Complexity.polyTimeComputable_xorD` — truncating bitwise XOR is
  polynomial-time, via the emit-iteration loop.
* The aggregated one-bit block tests live in
  `TCSlib.Complexity.ClassNP.PolyTimeBlockTests`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§7.3, Theorem 7.8; §7.4.1; Theorems
  7.17–7.18: the implicit "simulate the machine on each block" closures.)
-/

namespace Complexity

open Turing

/-! ### Slicing the second component at a polynomial schedule

The `Randomized`-layer `sliceTake`/`sliceDrop` of
`TCSlib.Complexity.Randomized.PolyTimeModel` are instances of the following
chapter-neutral forms (stated here, below the `Randomized` layer, so that the
block loop can be shared with the Chapter 3–4 development). -/

/-- Keep the first component of a pair and the first `a·(n+1)^k` symbols of its
second component, where `n` is the first component's length: on
`Turing.pairEncode x r` it returns `Turing.pairEncode x (r.take (a·(|x|+1)^k))`. -/
def sliceTakeAt (a k : ℕ) (z : List Bool) : List Bool :=
  pairEncode (pairFstD z) ((pairSndD z).take (a * ((pairFstD z).length + 1) ^ k))

/-- Keep the first component of a pair and drop the first `a·(n+1)^k` symbols of
its second component: on `Turing.pairEncode x r` it returns
`Turing.pairEncode x (r.drop (a·(|x|+1)^k))`. -/
def sliceDropAt (a k : ℕ) (z : List Bool) : List Bool :=
  pairEncode (pairFstD z) ((pairSndD z).drop (a * ((pairFstD z).length + 1) ^ k))

/-- `sliceTakeAt a k` is polynomial-time computable.
**Proof sketch.** `a·(n+1)^k` is available as a unary string via
`Complexity.polyTimeComputable_polyUnary`; pair it with the second component and
apply the length-gated prefix primitive
`Complexity.polyTimeComputable_takePrefixByLength`, so no in-machine
exponentiation is needed. -/
theorem polyTimeComputable_sliceTakeAt (a k : ℕ) :
    PolyTimeComputable (sliceTakeAt a k) := by
  have hu : PolyTimeComputable
      (fun z => List.replicate (a * ((pairFstD z).length + 1) ^ k) true) :=
    (polyTimeComputable_polyUnary a k).comp polyTimeComputable_pairFstD
  have henc : PolyTimeComputable (fun z => pairEncode
      (List.replicate (a * ((pairFstD z).length + 1) ^ k) true) (pairSndD z)) :=
    PolyTimeComputable.pairEncode hu polyTimeComputable_pairSndD
  have hg : PolyTimeComputable
      (fun z => (pairSndD z).take (a * ((pairFstD z).length + 1) ^ k)) := by
    have heq : (fun z => (pairSndD z).take (a * ((pairFstD z).length + 1) ^ k)) =
        PrefixByLength.take ∘ (fun z => pairEncode
          (List.replicate (a * ((pairFstD z).length + 1) ^ k) true) (pairSndD z)) := by
      funext z
      simp only [Function.comp, PrefixByLength.take, pairFstD_pairEncode,
        pairSndD_pairEncode, List.length_replicate]
    rw [heq]
    exact polyTimeComputable_takePrefixByLength.comp henc
  exact PolyTimeComputable.pairEncode polyTimeComputable_pairFstD hg

/-- `sliceDropAt a k` is polynomial-time computable.
**Proof sketch.** As `sliceTakeAt`, with
`Complexity.polyTimeComputable_dropPrefixByLength` in place of the take
primitive. -/
theorem polyTimeComputable_sliceDropAt (a k : ℕ) :
    PolyTimeComputable (sliceDropAt a k) := by
  have hu : PolyTimeComputable
      (fun z => List.replicate (a * ((pairFstD z).length + 1) ^ k) true) :=
    (polyTimeComputable_polyUnary a k).comp polyTimeComputable_pairFstD
  have henc : PolyTimeComputable (fun z => pairEncode
      (List.replicate (a * ((pairFstD z).length + 1) ^ k) true) (pairSndD z)) :=
    PolyTimeComputable.pairEncode hu polyTimeComputable_pairSndD
  have hg : PolyTimeComputable
      (fun z => (pairSndD z).drop (a * ((pairFstD z).length + 1) ^ k)) := by
    have heq : (fun z => (pairSndD z).drop (a * ((pairFstD z).length + 1) ^ k)) =
        PrefixByLength.drop ∘ (fun z => pairEncode
          (List.replicate (a * ((pairFstD z).length + 1) ^ k) true) (pairSndD z)) := by
      funext z
      simp only [Function.comp, PrefixByLength.drop, pairFstD_pairEncode,
        pairSndD_pairEncode, List.length_replicate]
    rw [heq]
    exact polyTimeComputable_dropPrefixByLength.comp henc
  exact PolyTimeComputable.pairEncode polyTimeComputable_pairFstD hg

/-! ### Small Boolean and list helpers -/

/-- Removing the head symbol is polynomial-time computable.
**Proof sketch.** `w.drop 1` is the length-gated drop
`Complexity.PrefixByLength.drop` applied to `Turing.pairEncode [true] w`. -/
theorem polyTimeComputable_tail : PolyTimeComputable (fun w => w.drop 1) := by
  have henc : PolyTimeComputable (fun w => pairEncode [true] w) :=
    (polyTimeComputable_const [true]).pairEncode polyTimeComputable_id
  have heq : (fun w : List Bool => w.drop 1) =
      PrefixByLength.drop ∘ (fun w => pairEncode [true] w) := by
    funext w
    simp [Function.comp, PrefixByLength.drop]
  rw [heq]
  exact polyTimeComputable_dropPrefixByLength.comp henc

/-- The emptiness test is polynomial-time computable (as a one-bit output).
**Proof sketch.** `w = []` iff `|w| ≤ |[]|`, the pair length test
`Complexity.polyTimeComputable_lenLe` at `Turing.pairEncode [] w`. -/
theorem polyTimeComputable_isNil :
    PolyTimeComputable (fun w => [decide (w = [])]) := by
  have henc : PolyTimeComputable (fun w => pairEncode [] w) :=
    (polyTimeComputable_const []).pairEncode polyTimeComputable_id
  have h := polyTimeComputable_lenLe.comp henc
  convert h using 1
  funext w
  simp only [Function.comp, pairFstD_pairEncode, pairSndD_pairEncode, List.length_nil,
    Nat.le_zero, List.length_eq_zero_iff]

/-- Polynomial-time Boolean disjunction of two one-bit tests. -/
theorem polyTimeComputable_or {p q : List Bool → Bool}
    (hp : PolyTimeComputable (fun x => [p x])) (hq : PolyTimeComputable (fun x => [q x])) :
    PolyTimeComputable (fun x => [p x || q x]) := by
  convert polyTimeComputable_ite hp (polyTimeComputable_const [true]) hq using 1
  funext x
  cases p x <;> rfl

/-- Polynomial-time Boolean negation of a one-bit test. -/
theorem polyTimeComputable_not {p : List Bool → Bool}
    (hp : PolyTimeComputable (fun x => [p x])) :
    PolyTimeComputable (fun x => [!p x]) := by
  convert polyTimeComputable_ite hp (polyTimeComputable_const [false])
    (polyTimeComputable_const [true]) using 1
  funext x
  cases p x <;> rfl

/-- The first projection of the empty word. -/
theorem pairFstD_nil : pairFstD ([] : List Bool) = [] := rfl

/-- The second component of a pair is shorter than the pair. -/
theorem length_pairSndD_le (z : List Bool) : (pairSndD z).length ≤ z.length := by
  cases h : pairDecode z with
  | none => simp [pairSndD, h]
  | some ab =>
    obtain ⟨p, u⟩ := ab
    have hz := eq_pairEncode_of_pairDecode z p u h
    rw [hz, pairSndD_pairEncode, length_pairEncode]
    omega

/-- A word with a nonempty first projection is a genuine pair. -/
theorem eq_pairEncode_of_pairFstD_ne {z : List Bool} (h : pairFstD z ≠ []) :
    z = pairEncode (pairFstD z) (pairSndD z) := by
  cases hd : pairDecode z with
  | none => exact absurd (by simp [pairFstD, hd]) h
  | some ab =>
    obtain ⟨p, u⟩ := ab
    have hz := eq_pairEncode_of_pairDecode z p u hd
    rw [hz, pairFstD_pairEncode, pairSndD_pairEncode]

/-- Both projections of a word fit inside it, jointly and doubled. -/
theorem length_pair_components_le (y : List Bool) :
    2 * (pairFstD y).length + (pairSndD y).length ≤ y.length := by
  cases hd : pairDecode y with
  | none =>
    have hf : pairFstD y = [] := by simp [pairFstD, hd]
    have hs : pairSndD y = [] := by simp [pairSndD, hd]
    simp [hf, hs]
  | some ab =>
    obtain ⟨p, u⟩ := ab
    have hz := eq_pairEncode_of_pairDecode y p u hd
    conv_rhs => rw [hz]
    rw [length_pairEncode, hz, pairFstD_pairEncode, pairSndD_pairEncode]
    omega

/-- Dropping a slice never grows a word beyond `max` with the constant pair. -/
theorem length_sliceDropAt_le (a k : ℕ) (z : List Bool) :
    (sliceDropAt a k z).length ≤ max z.length 2 := by
  cases h : pairDecode z with
  | none =>
    have h1 : pairFstD z = [] := by simp [pairFstD, h]
    have h2 : pairSndD z = [] := by simp [pairSndD, h]
    refine le_trans ?_ (le_max_right _ _)
    simp [sliceDropAt, h1, h2, length_pairEncode]
  | some ab =>
    obtain ⟨p, u⟩ := ab
    have hz := eq_pairEncode_of_pairDecode z p u h
    refine le_trans ?_ (le_max_left _ _)
    rw [hz]
    simp only [sliceDropAt, pairFstD_pairEncode, pairSndD_pairEncode, length_pairEncode,
      List.length_drop]
    omega

/-- A range-indexed concatenation with a single live chunk is that chunk. -/
theorem flatMap_range_eq_single {c : ℕ → List Bool} {N K : ℕ} {b : List Bool}
    (hKN : K < N) (hc : ∀ i < N, c i = if i = K then b else []) :
    (List.range N).flatMap c = b := by
  induction N with
  | zero => omega
  | succ N ih =>
    rw [List.range_succ, List.flatMap_append]
    by_cases hNK : N = K
    · subst hNK
      have hpre : (List.range N).flatMap c = [] := by
        refine List.flatMap_eq_nil_iff.mpr (fun i hi => ?_)
        have hiN := List.mem_range.mp hi
        rw [hc i (by omega), if_neg (by omega)]
      rw [hpre, List.nil_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        hc N (by omega), if_pos rfl]
    · have hKN' : K < N := by omega
      rw [ih hKN' (fun i hi => hc i (by omega))]
      rw [List.flatMap_cons, hc N (by omega), if_neg hNK]
      simp

/-- The absorbing end state of the block loops. -/
def blockDone : List Bool := pairEncode [] []

/-- The Boolean emptiness test, in the shape
`Complexity.polyTimeComputable_ite` consumes. -/
def isNilB (w : List Bool) : Bool := decide (w = [])

/-- Keeping only the head symbol is polynomial-time computable.
**Proof sketch.** `w.take 1` is the length-gated take
`Complexity.PrefixByLength.take` applied to `Turing.pairEncode [true] w`. -/
theorem polyTimeComputable_take1 : PolyTimeComputable (fun w => w.take 1) := by
  have henc : PolyTimeComputable (fun w => pairEncode [true] w) :=
    (polyTimeComputable_const [true]).pairEncode polyTimeComputable_id
  have heq : (fun w : List Bool => w.take 1) =
      PrefixByLength.take ∘ (fun w => pairEncode [true] w) := by
    funext w
    simp [Function.comp, PrefixByLength.take]
  rw [heq]
  exact polyTimeComputable_takePrefixByLength.comp henc

/-- The head bit (defaulting to `false`) is polynomial-time computable as a
one-bit output.
**Proof sketch.** `[w.headD false] = (w ++ [false]).take 1`. -/
theorem polyTimeComputable_headD :
    PolyTimeComputable (fun w => [w.headD false]) := by
  have happ : PolyTimeComputable (fun w : List Bool => w ++ [false]) :=
    PolyTimeComputable.append polyTimeComputable_id (polyTimeComputable_const [false])
  have heq : (fun w : List Bool => [w.headD false]) =
      (fun w : List Bool => w.take 1) ∘ (fun w : List Bool => w ++ [false]) := by
    funext w
    cases w <;> simp [Function.comp]
  rw [heq]
  exact polyTimeComputable_take1.comp happ

/-! ### The emit-iteration combinator -/

/-- **The bounded loop of polynomial-time rounds** — the machine-level engine
of every block-query closure: iterating a polynomial-time step function `g` a
polynomial number of times from the input, concatenating a polynomial-time
chunk `e` of each iterate, is again polynomial-time, provided every iterate
stays inside one polynomial length envelope `b·(n+1)^l` of the *original*
input length.

**Proof sketch.** Unpack the two machines and apply
`Turing.FinTM.exists_emitIterTM` (in
`TCSlib.Complexity.TuringMachine.Build.EmitIterBody`): an instance of
`Turing.FinTM.exists_emitLoopTM` whose body copies its input onto work tape
zero and runs each round as two clean calls on the tape-resident state word —
an emit-mode call (`Turing.FinTM.exists_emitCallTM`) forwarding the chunk
`e s`, then an install-mode call (`Turing.FinTM.exists_installCallTM`)
replacing the word by `g s`.  The host's admissibility invariant is "the
state word is an orbit point of `g` from the input", so the orbit-only
length envelope `horbit` bounds each call's budget by one polynomial in the
input length; the fuel machine is
`Turing.FinTM.computesFunInTime_polyBits`. -/
theorem polyTimeComputable_emitIter {g e : List Bool → List Bool}
    (hg : PolyTimeComputable g) (he : PolyTimeComputable e)
    (a' k' b l : ℕ)
    (horbit : ∀ (w : List Bool) (i : ℕ),
      (g^[i] w).length ≤ b * (w.length + 1) ^ l) :
    PolyTimeComputable (fun w =>
      (List.range (a' * (w.length + 1) ^ k' + 1)).flatMap (fun i => e (g^[i] w))) := by
  obtain ⟨G, CG, cG, hG⟩ := hg
  obtain ⟨E, CE, cE, hE⟩ := he
  obtain ⟨M, C, c, hM⟩ :=
    FinTM.exists_emitIterTM G E g e CG cG CE cE hG hE a' k' b l horbit
  exact ⟨M, C, c, hM⟩

/-! ### Truncating bitwise XOR -/

/-- Bitwise XOR of the two components of a pair, truncating to the shorter
component (`List.zipWith` semantics); malformed pairs give `[]`. -/
def xorD (z : List Bool) : List Bool :=
  List.zipWith xor (pairFstD z) (pairSndD z)

/-- One round of the XOR transducer: drop the head of both components. -/
private def xorPairStep (s : List Bool) : List Bool :=
  pairEncode ((pairFstD s).drop 1) ((pairSndD s).drop 1)

/-- The XOR transducer's chunk: one XOR bit while both components are
nonempty, nothing afterwards. -/
private def xorPairEmit (s : List Bool) : List Bool :=
  if isNilB (pairFstD s) || isNilB (pairSndD s) then []
  else if (pairFstD s).headD false then
    if (pairSndD s).headD false then [false] else [true]
  else
    if (pairSndD s).headD false then [true] else [false]

private theorem polyTimeComputable_xorPairStep : PolyTimeComputable xorPairStep :=
  (polyTimeComputable_tail.comp polyTimeComputable_pairFstD).pairEncode
    (polyTimeComputable_tail.comp polyTimeComputable_pairSndD)

private theorem polyTimeComputable_xorPairEmit : PolyTimeComputable xorPairEmit := by
  have hguard : PolyTimeComputable (fun s =>
      [isNilB (pairFstD s) || isNilB (pairSndD s)]) :=
    polyTimeComputable_or (polyTimeComputable_isNil.comp polyTimeComputable_pairFstD)
      (polyTimeComputable_isNil.comp polyTimeComputable_pairSndD)
  have hd1 : PolyTimeComputable (fun s => [(pairFstD s).headD false]) :=
    polyTimeComputable_headD.comp polyTimeComputable_pairFstD
  have hd2 : PolyTimeComputable (fun s => [(pairSndD s).headD false]) :=
    polyTimeComputable_headD.comp polyTimeComputable_pairSndD
  exact polyTimeComputable_ite hguard (polyTimeComputable_const [])
    (polyTimeComputable_ite hd1
      (polyTimeComputable_ite hd2 (polyTimeComputable_const [false])
        (polyTimeComputable_const [true]))
      (polyTimeComputable_ite hd2 (polyTimeComputable_const [true])
        (polyTimeComputable_const [false])))

/-- One XOR round never grows the state beyond `max` with the empty pair. -/
private theorem length_xorPairStep_le (s : List Bool) :
    (xorPairStep s).length ≤ max s.length 2 := by
  cases h : pairDecode s with
  | none =>
    have h1 : pairFstD s = [] := by simp [pairFstD, h]
    have h2 : pairSndD s = [] := by simp [pairSndD, h]
    refine le_trans ?_ (le_max_right _ _)
    simp [xorPairStep, h1, h2, length_pairEncode]
  | some ab =>
    obtain ⟨a, b⟩ := ab
    have hz := eq_pairEncode_of_pairDecode s a b h
    refine le_trans ?_ (le_max_left _ _)
    rw [hz]
    simp only [xorPairStep, pairFstD_pairEncode, pairSndD_pairEncode, length_pairEncode,
      List.length_drop]
    omega

/-- Orbit envelope for the XOR transducer. -/
private theorem length_xorPairStep_iterate (w : List Bool) (i : ℕ) :
    (xorPairStep^[i] w).length ≤ 2 * (w.length + 1) ^ 1 := by
  have hmax : (xorPairStep^[i] w).length ≤ max w.length 2 := by
    induction i with
    | zero => simpa using le_max_left _ _
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact le_trans (length_xorPairStep_le _) (max_le ih (le_max_right _ _))
  refine le_trans hmax ?_
  rw [pow_one]
  exact max_le (by omega) (by omega)

/-- The XOR transducer's orbit drops both components one symbol per round. -/
private theorem xorPairStep_orbit (p u : List Bool) (i : ℕ) :
    xorPairStep^[i] (pairEncode p u) = pairEncode (p.drop i) (u.drop i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [xorPairStep, pairFstD_pairEncode, pairSndD_pairEncode, List.drop_drop]

/-- On two nonempty components the chunk is the single XOR bit of the heads. -/
private theorem xorPairEmit_cons (b c : Bool) (p u : List Bool) :
    xorPairEmit (pairEncode (b :: p) (c :: u)) = [xor b c] := by
  cases b <;> cases c <;> simp [xorPairEmit, isNilB]

/-- Once a component is exhausted the chunk is empty. -/
private theorem xorPairEmit_nil {p u : List Bool} (h : p = [] ∨ u = []) :
    xorPairEmit (pairEncode p u) = [] := by
  rcases h with rfl | rfl <;> simp [xorPairEmit, isNilB]

/-- The concatenated chunks of the XOR transducer compute `List.zipWith xor`.
**Proof sketch.** Induction on the round budget, generalizing the two
components: each cons-cons round contributes its head XOR
(`xorPairEmit_cons`) and the orbit shifts both tails; an exhausted component
silences every later round. -/
private theorem xorPair_output : ∀ (N : ℕ) (p u : List Bool),
    min p.length u.length ≤ N →
    (List.range N).flatMap (fun i => xorPairEmit (pairEncode (p.drop i) (u.drop i))) =
      List.zipWith xor p u := by
  intro N
  induction N with
  | zero =>
    intro p u h
    have : p = [] ∨ u = [] := by
      rcases p with _ | ⟨b, p⟩
      · exact Or.inl rfl
      rcases u with _ | ⟨c, u⟩
      · exact Or.inr rfl
      simp at h
    rcases this with rfl | rfl <;> simp
  | succ N ih =>
    intro p u h
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    rcases p with _ | ⟨b, p⟩
    · simp only [List.zipWith_nil_left, List.drop_nil]
      rw [xorPairEmit_nil (Or.inl rfl), List.nil_append]
      refine List.flatMap_eq_nil_iff.mpr (fun i _ => ?_)
      exact xorPairEmit_nil (Or.inl rfl)
    rcases u with _ | ⟨c, u⟩
    · simp only [List.zipWith_nil_right, List.drop_nil]
      rw [xorPairEmit_nil (Or.inr rfl), List.nil_append]
      refine List.flatMap_eq_nil_iff.mpr (fun i _ => ?_)
      exact xorPairEmit_nil (Or.inr rfl)
    rw [List.drop_zero, List.drop_zero, xorPairEmit_cons, List.zipWith_cons_cons]
    have hrest : (List.range N).flatMap
        (fun i => xorPairEmit (pairEncode ((b :: p).drop (i + 1)) ((c :: u).drop (i + 1)))) =
        List.zipWith xor p u := by
      have heq : (fun i => xorPairEmit (pairEncode ((b :: p).drop (i + 1))
          ((c :: u).drop (i + 1)))) =
          (fun i => xorPairEmit (pairEncode (p.drop i) (u.drop i))) := by
        funext i
        rfl
      rw [heq]
      exact ih p u (by simp at h; omega)
    rw [hrest]
    rfl

/-- `xorD` is polynomial-time computable.
**Proof sketch.** An instance of `Complexity.polyTimeComputable_emitIter`:
the loop state is the pair of not-yet-consumed components; each round emits
the XOR of the two head bits (nothing once either component is exhausted) and
drops both heads, so the concatenated output is exactly the truncating
`List.zipWith xor`.  The round budget `|z|+1` dominates the shorter
component's length.  (The truncating semantics on unequal lengths is the
audited ch7-phase1 finding 1 convention.) -/
theorem polyTimeComputable_xorD : PolyTimeComputable xorD := by
  have hloop := polyTimeComputable_emitIter polyTimeComputable_xorPairStep
    polyTimeComputable_xorPairEmit 1 1 2 1 (fun w i => length_xorPairStep_iterate w i)
  have hinit : PolyTimeComputable (fun z => pairEncode (pairFstD z) (pairSndD z)) :=
    polyTimeComputable_pairFstD.pairEncode polyTimeComputable_pairSndD
  have heq : xorD = (fun w => (List.range (1 * (w.length + 1) ^ 1 + 1)).flatMap
      (fun i => xorPairEmit (xorPairStep^[i] w))) ∘
      (fun z => pairEncode (pairFstD z) (pairSndD z)) := by
    funext z
    rw [Function.comp_apply]
    have horb : ∀ i, xorPairStep^[i] (pairEncode (pairFstD z) (pairSndD z)) =
        pairEncode ((pairFstD z).drop i) ((pairSndD z).drop i) :=
      xorPairStep_orbit (pairFstD z) (pairSndD z)
    have hbudget : min (pairFstD z).length (pairSndD z).length ≤
        1 * ((pairEncode (pairFstD z) (pairSndD z)).length + 1) ^ 1 + 1 := by
      have h1 := length_pairFstD_le z
      rw [pow_one, length_pairEncode]
      omega
    calc xorD z = List.zipWith xor (pairFstD z) (pairSndD z) := rfl
      _ = (List.range (1 * ((pairEncode (pairFstD z) (pairSndD z)).length + 1) ^ 1 + 1)).flatMap
          (fun i => xorPairEmit (pairEncode ((pairFstD z).drop i) ((pairSndD z).drop i))) :=
        (xorPair_output _ (pairFstD z) (pairSndD z) hbudget).symm
      _ = _ := by
        simp only [horb]
  rw [heq]
  exact hloop.comp hinit

/-- `xorD` computes the truncating bitwise XOR on genuine pairs. -/
@[simp]
theorem xorD_pairEncode (a b : List Bool) :
    xorD (pairEncode a b) = List.zipWith xor a b := by
  simp [xorD]

end Complexity
```

## ===== TCSlib/Complexity/ClassNP/PolyTimeBlockTests.lean =====

```
/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.ClassNP.PolyTimeBlockLoop

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The aggregated block tests

The three customers of the bounded block-query loop
(`TCSlib.Complexity.ClassNP.PolyTimeBlockLoop`): the one-bit OR,
strict-majority, and XOR-then-OR aggregations of a polynomial-time one-bit
indicator over polynomially many polynomial-length blocks are polynomial-time.
Each is an instance of `Complexity.polyTimeComputable_emitIter` with the
aggregation state (flag, vote counters, XOR mask) carried inside the loop's
tape-resident state word; the per-round work is assembled from the existing
`FP` combinators, and the orbit is computed in closed form by induction.

These are the `PolyTimeComputable` engines of the `P`-closure lemmas
`Complexity.mem_P_of_blockAny` / `_blockMajority` / `_blockXorAny` in
`TCSlib.Complexity.ClassNP.PClosure`.

## Main definitions

* `Complexity.blockAt` — the `i`-th length-`a·(n+1)^k` block of the second
  component of a pair, where `n` is the first component's length.

## Main results

* `Complexity.polyTimeComputable_blockAnyTest` / `_blockXorAnyTest` — the
  aggregated one-bit OR and XOR-then-OR block tests of a polynomial-time
  one-bit indicator are polynomial-time.  The strict-majority test lives in
  `TCSlib.Complexity.ClassNP.PolyTimeBlockMajority`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§7.3, Theorem 7.8; §7.4.1; Theorems
  7.17–7.18: the implicit "simulate the machine on each block" closures.)
-/

namespace Complexity

open Turing

/-- The `i`-th length-`a·(n+1)^k` block of the second component of a pair,
where `n` is the first component's length. -/
def blockAt (a k : ℕ) (z : List Bool) (i : ℕ) : List Bool :=
  ((pairSndD z).drop (i * (a * ((pairFstD z).length + 1) ^ k))).take
    (a * ((pairFstD z).length + 1) ^ k)

/-! #### The OR-aggregating loop -/

/-- One round of the OR-aggregating block loop on state
`pairEncode [flag] (pairEncode countdown (pairEncode x rem))`: OR the
indicator of the current block into the flag, drop the block, decrement the
unary countdown.  A done or malformed state is sent to the absorbing
`blockDone`; an exhausted countdown is sent to `blockDone` one step after the
chunk function has emitted the flag. -/
private noncomputable def anyStep (V : Language Bool) (a k : ℕ) (s : List Bool) : List Bool :=
  if isNilB (pairFstD s) then blockDone
  else if isNilB (pairFstD (pairSndD s)) then blockDone
  else
    pairEncode
      (if MultiTapeTM.indicator V (sliceTakeAt a k (pairSndD (pairSndD s))) then [true]
        else pairFstD s)
      (pairEncode ((pairFstD (pairSndD s)).drop 1)
        (sliceDropAt a k (pairSndD (pairSndD s))))

/-- The chunk function: emit the flag exactly at countdown exhaustion. -/
private def anyEmit (s : List Bool) : List Bool :=
  if isNilB (pairFstD s) then []
  else if isNilB (pairFstD (pairSndD s)) then pairFstD s
  else []

/-- The initial state: clear flag, unary countdown `a'·(n+1)^k'`, and the
normalized input pair. -/
private def anyInit (a' k' : ℕ) (z : List Bool) : List Bool :=
  pairEncode [false]
    (pairEncode (List.replicate (a' * ((pairFstD z).length + 1) ^ k') true)
      (pairEncode (pairFstD z) (pairSndD z)))

/-- The OR round is polynomial-time.
**Proof sketch.** Assemble the two guards, the indicator of the sliced block,
the flag update, the countdown tail, and the dropped remainder from the `FP`
combinators (`polyTimeComputable_ite`/`pairEncode`/`comp` and the slice
primitives). -/
private theorem polyTimeComputable_anyStep {V : Language Bool}
    (hV : PolyTimeComputable (fun z => [MultiTapeTM.indicator V z])) (a k : ℕ) :
    PolyTimeComputable (anyStep V a k) := by
  have hcd : PolyTimeComputable (fun s => pairFstD (pairSndD s)) :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hzz : PolyTimeComputable (fun s => pairSndD (pairSndD s)) :=
    polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have ht1 : PolyTimeComputable (fun s => [isNilB (pairFstD s)]) :=
    polyTimeComputable_isNil.comp polyTimeComputable_pairFstD
  have ht2 : PolyTimeComputable (fun s => [isNilB (pairFstD (pairSndD s))]) :=
    polyTimeComputable_isNil.comp hcd
  have hind : PolyTimeComputable
      (fun s => [MultiTapeTM.indicator V (sliceTakeAt a k (pairSndD (pairSndD s)))]) :=
    hV.comp ((polyTimeComputable_sliceTakeAt a k).comp hzz)
  have hflag : PolyTimeComputable (fun s =>
      if MultiTapeTM.indicator V (sliceTakeAt a k (pairSndD (pairSndD s))) then [true]
      else pairFstD s) :=
    polyTimeComputable_ite hind (polyTimeComputable_const [true]) polyTimeComputable_pairFstD
  have hrest : PolyTimeComputable (fun s =>
      pairEncode ((pairFstD (pairSndD s)).drop 1)
        (sliceDropAt a k (pairSndD (pairSndD s)))) :=
    (polyTimeComputable_tail.comp hcd).pairEncode
      ((polyTimeComputable_sliceDropAt a k).comp hzz)
  have hinner := polyTimeComputable_ite ht2 (polyTimeComputable_const blockDone)
    (hflag.pairEncode hrest)
  exact polyTimeComputable_ite ht1 (polyTimeComputable_const blockDone) hinner

private theorem polyTimeComputable_anyEmit : PolyTimeComputable anyEmit := by
  have ht1 : PolyTimeComputable (fun s => [isNilB (pairFstD s)]) :=
    polyTimeComputable_isNil.comp polyTimeComputable_pairFstD
  have ht2 : PolyTimeComputable (fun s => [isNilB (pairFstD (pairSndD s))]) :=
    polyTimeComputable_isNil.comp
      (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
  exact polyTimeComputable_ite ht1 (polyTimeComputable_const [])
    (polyTimeComputable_ite ht2 polyTimeComputable_pairFstD (polyTimeComputable_const []))

private theorem polyTimeComputable_anyInit (a' k' : ℕ) :
    PolyTimeComputable (anyInit a' k') := by
  have hcnt : PolyTimeComputable
      (fun z => List.replicate (a' * ((pairFstD z).length + 1) ^ k') true) :=
    (polyTimeComputable_polyUnary a' k').comp polyTimeComputable_pairFstD
  exact (polyTimeComputable_const [false]).pairEncode
    (hcnt.pairEncode (polyTimeComputable_pairFstD.pairEncode polyTimeComputable_pairSndD))

/-- One loop round never grows the state beyond `max` with the done state's
length.
**Proof sketch.** The done branches have length two.  A live round keeps the
flag within the old flag's length, shortens the countdown, and replaces the
remainder by a dropped slice; summing the `Turing.length_pairEncode`
decompositions, the round shrinks the state by at least the two symbols the
countdown loses. -/
private theorem length_anyStep_le (V : Language Bool) (a k : ℕ) (s : List Bool) :
    (anyStep V a k s).length ≤ max s.length 2 := by
  unfold anyStep
  cases h1 : isNilB (pairFstD s) with
  | true =>
    simp only [if_pos rfl]
    refine le_trans ?_ (le_max_right _ _)
    simp [blockDone, length_pairEncode]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases h2 : isNilB (pairFstD (pairSndD s)) with
    | true =>
      simp only [if_pos rfl]
      refine le_trans ?_ (le_max_right _ _)
      simp [blockDone, length_pairEncode]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hf : pairFstD s ≠ [] := by simpa [isNilB] using h1
      have hcd : pairFstD (pairSndD s) ≠ [] := by simpa [isNilB] using h2
      have hs := eq_pairEncode_of_pairFstD_ne hf
      have ht := eq_pairEncode_of_pairFstD_ne hcd
      refine le_trans ?_ (le_max_left _ _)
      have hslice := length_sliceDropAt_le a k (pairSndD (pairSndD s))
      have hfl : (if MultiTapeTM.indicator V
          (sliceTakeAt a k (pairSndD (pairSndD s))) then [true]
          else pairFstD s).length ≤ (pairFstD s).length := by
        cases MultiTapeTM.indicator V (sliceTakeAt a k (pairSndD (pairSndD s)))
        · simp
        · simpa using Nat.one_le_iff_ne_zero.mpr
            (by simpa [List.length_eq_zero_iff] using hf)
      have hlens : s.length =
          2 * (pairFstD s).length + 2 +
            (2 * (pairFstD (pairSndD s)).length + 2 + (pairSndD (pairSndD s)).length) := by
        conv_lhs => rw [hs]
        rw [length_pairEncode]
        congr 2
        conv_lhs => rw [ht]
        rw [length_pairEncode]
      have hcd1 : 1 ≤ (pairFstD (pairSndD s)).length :=
        Nat.one_le_iff_ne_zero.mpr (by simpa [List.length_eq_zero_iff] using hcd)
      rw [length_pairEncode, length_pairEncode]
      simp only [List.length_drop]
      have hslice' : (sliceDropAt a k (pairSndD (pairSndD s))).length ≤
          (pairSndD (pairSndD s)).length + 2 :=
        le_trans hslice (by omega)
      omega

/-- Orbit envelope for the OR loop, in the shape
`Complexity.polyTimeComputable_emitIter` consumes. -/
private theorem length_anyStep_iterate (V : Language Bool) (a k : ℕ)
    (w : List Bool) (i : ℕ) :
    ((anyStep V a k)^[i] w).length ≤ 2 * (w.length + 1) ^ 1 := by
  have hmax : ((anyStep V a k)^[i] w).length ≤ max w.length 2 := by
    induction i with
    | zero => simpa using le_max_left _ _
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact le_trans (length_anyStep_le V a k _) (max_le ih (le_max_right _ _))
  refine le_trans hmax ?_
  rw [pow_one]
  exact max_le (by omega) (by omega)

/-- The done state is absorbing. -/
private theorem anyStep_done (V : Language Bool) (a k : ℕ) :
    anyStep V a k blockDone = blockDone := by
  unfold anyStep
  simp [blockDone, isNilB]

/-- Closed form of the OR loop's orbit up to countdown exhaustion.
**Proof sketch.** Induction on the round index: the guards see a one-bit flag
and a positive countdown, so the step fires; the slice primitives advance the
remainder by one block, `List.range_succ` extends the OR by the current
block's indicator, and the countdown loses one `true`. -/
private theorem anyStep_orbit (V : Language Bool) (a k a' k' : ℕ) (z : List Bool)
    {i : ℕ} (hi : i ≤ a' * ((pairFstD z).length + 1) ^ k') :
    (anyStep V a k)^[i] (anyInit a' k' z) =
      pairEncode
        [(List.range i).any (fun j => MultiTapeTM.indicator V
          (pairEncode (pairFstD z) (blockAt a k z j)))]
        (pairEncode
          (List.replicate (a' * ((pairFstD z).length + 1) ^ k' - i) true)
          (pairEncode (pairFstD z)
            ((pairSndD z).drop (i * (a * ((pairFstD z).length + 1) ^ k))))) := by
  induction i with
  | zero => simp [anyInit]
  | succ i ih =>
    have hii : i ≤ a' * ((pairFstD z).length + 1) ^ k' := Nat.le_of_succ_le hi
    rw [Function.iterate_succ_apply', ih hii]
    have hcd : a' * ((pairFstD z).length + 1) ^ k' - i =
        (a' * ((pairFstD z).length + 1) ^ k' - (i + 1)) + 1 := by omega
    rw [hcd, List.replicate_succ]
    unfold anyStep
    rw [if_neg (by simp [isNilB]), pairSndD_pairEncode, if_neg (by simp [isNilB])]
    rw [pairFstD_pairEncode, pairSndD_pairEncode]
    congr 1
    · rw [sliceTakeAt, pairFstD_pairEncode, pairSndD_pairEncode]
      rw [List.range_succ, List.any_append]
      cases hb : MultiTapeTM.indicator V (pairEncode (pairFstD z)
          (((pairSndD z).drop (i * (a * ((pairFstD z).length + 1) ^ k))).take
            (a * ((pairFstD z).length + 1) ^ k))) with
      | true =>
        have hb' : MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z i))
            = true := hb
        simp [hb']
      | false =>
        have hb' : MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z i))
            = false := hb
        simp [hb']
    · congr 1
      · rw [pairFstD_pairEncode]
        simp
      · rw [sliceDropAt, pairFstD_pairEncode, pairSndD_pairEncode, List.drop_drop]
        congr 2
        ring

/-- Beyond exhaustion the orbit sits at the done state. -/
private theorem anyStep_orbit_done (V : Language Bool) (a k a' k' : ℕ) (z : List Bool)
    {i : ℕ} (hi : a' * ((pairFstD z).length + 1) ^ k' < i) :
    (anyStep V a k)^[i] (anyInit a' k' z) = blockDone := by
  set K := a' * ((pairFstD z).length + 1) ^ k' with hK
  obtain ⟨j, rfl⟩ : ∃ j, i = j + (K + 1) := ⟨i - (K + 1), by omega⟩
  rw [Function.iterate_add_apply]
  have hend : (anyStep V a k)^[K + 1] (anyInit a' k' z) = blockDone := by
    rw [Function.iterate_succ_apply', anyStep_orbit V a k a' k' z (le_refl K)]
    unfold anyStep
    rw [if_neg (by simp [isNilB]), pairSndD_pairEncode, pairFstD_pairEncode]
    rw [if_pos (by simp [isNilB, hK])]
  rw [hend]
  clear hi
  induction j with
  | zero => simp
  | succ j ih => rw [Function.iterate_succ_apply', ih, anyStep_done]

/-- The OR loop's machine-level output is the single aggregated bit.
**Proof sketch.** The countdown exhausts within the machine's larger round
budget (the input embeds its own first component, and the schedule is
monotone).  Rounds before exhaustion emit nothing, the exhaustion round emits
the flag, and the absorbing done state emits nothing after it, so the
single-live-chunk concatenation lemma applies. -/
private theorem anyLoop_output (V : Language Bool) (a k a' k' : ℕ) (z : List Bool) :
    (List.range (a' * ((anyInit a' k' z).length + 1) ^ k' + 1)).flatMap
      (fun i => anyEmit ((anyStep V a k)^[i] (anyInit a' k' z))) =
      [(List.range (a' * ((pairFstD z).length + 1) ^ k')).any
        (fun j => MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j)))] := by
  set K := a' * ((pairFstD z).length + 1) ^ k' with hK
  have hlen : (pairFstD z).length ≤ (anyInit a' k' z).length := by
    rw [anyInit, length_pairEncode, length_pairEncode, length_pairEncode]
    omega
  have hKN : K < a' * ((anyInit a' k' z).length + 1) ^ k' + 1 := by
    have := Nat.mul_le_mul_left a'
      (Nat.pow_le_pow_left (Nat.add_le_add_right hlen 1) k')
    omega
  refine flatMap_range_eq_single hKN (fun i _ => ?_)
  rcases Nat.lt_trichotomy i K with hiK | rfl | hiK
  · rw [if_neg (by omega), anyStep_orbit V a k a' k' z (le_of_lt hiK)]
    unfold anyEmit
    rw [if_neg (by simp [isNilB]), pairSndD_pairEncode, pairFstD_pairEncode]
    rw [if_neg (by simp [isNilB]; omega)]
  · rw [if_pos rfl, anyStep_orbit V a k a' k' z (le_refl K)]
    unfold anyEmit
    rw [if_neg (by simp [isNilB]), pairSndD_pairEncode, pairFstD_pairEncode]
    rw [if_pos (by simp [isNilB]; omega), pairFstD_pairEncode]
  · rw [if_neg (by omega), anyStep_orbit_done V a k a' k' z hiK]
    unfold anyEmit
    rw [if_pos (by simp [blockDone, isNilB])]

/-- The OR-aggregated block test of a polynomial-time one-bit indicator is
polynomial-time: one bit saying whether some of the `a'·(n+1)^k'` blocks of
length `a·(n+1)^k` passes the test on `Turing.pairEncode`d (first component,
block).

**Proof sketch.** An instance of `Complexity.polyTimeComputable_emitIter`.
The loop state is `pairEncode [flag] (pairEncode countdown (pairEncode x rem))`
with a unary countdown initialized at `a'·(|x|+1)^k'`
(`Complexity.polyTimeComputable_polyUnary`); each round ORs the indicator of
`sliceTakeAt a k` into the flag, drops the block (`sliceDropAt a k`), and
decrements; the chunk function emits `[flag]` exactly at countdown exhaustion
(the step then moves to an absorbing done state), so the concatenated output
is the single aggregated bit.  The orbit is computed in closed form by
induction on the round index. -/
theorem polyTimeComputable_blockAnyTest {V : Language Bool}
    (hV : PolyTimeComputable (fun z => [MultiTapeTM.indicator V z]))
    (a k a' k' : ℕ) :
    PolyTimeComputable (fun z =>
      [(List.range (a' * ((pairFstD z).length + 1) ^ k')).any
        (fun i => MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z i)))]) := by
  have hloop := polyTimeComputable_emitIter (polyTimeComputable_anyStep hV a k)
    polyTimeComputable_anyEmit a' k' 2 1 (length_anyStep_iterate V a k)
  have heq : (fun z => [(List.range (a' * ((pairFstD z).length + 1) ^ k')).any
      (fun i => MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z i)))]) =
      ((fun w => (List.range (a' * (w.length + 1) ^ k' + 1)).flatMap
        (fun i => anyEmit ((anyStep V a k)^[i] w))) ∘ anyInit a' k') := by
    funext z
    rw [Function.comp_apply, anyLoop_output V a k a' k' z]
  rw [heq]
  exact hloop.comp (polyTimeComputable_anyInit a' k')

/-! #### The XOR-shifted OR loop -/

/-- One round of the XOR-shifted OR loop on state
`pairEncode [flag] (pairEncode countdown (pairEncode v (pairEncode x u)))`:
XOR the mask `v` with the current block of `u`, test paired with `x`, OR
into the flag, drop the block, decrement. -/
private noncomputable def xorStep (V : Language Bool) (a k : ℕ) (s : List Bool) : List Bool :=
  if isNilB (pairFstD s) then blockDone
  else if isNilB (pairFstD (pairSndD s)) then blockDone
  else
    pairEncode
      (if MultiTapeTM.indicator V
          (pairEncode (pairFstD (pairSndD (pairSndD (pairSndD s))))
            (xorD (pairEncode (pairFstD (pairSndD (pairSndD s)))
              (pairSndD (sliceTakeAt a k (pairSndD (pairSndD (pairSndD s)))))))) then [true]
        else pairFstD s)
      (pairEncode ((pairFstD (pairSndD s)).drop 1)
        (pairEncode (pairFstD (pairSndD (pairSndD s)))
          (sliceDropAt a k (pairSndD (pairSndD (pairSndD s))))))

/-- The initial state of the XOR-shifted loop on the nested pair
`⟨⟨x, u⟩, v⟩`: clear flag, unary countdown `a'·(|x|+1)^k'`, the mask `v`, and
the normalized `⟨x, u⟩`. -/
private def xorInit (a' k' : ℕ) (w : List Bool) : List Bool :=
  pairEncode [false]
    (pairEncode
      (List.replicate (a' * ((pairFstD (pairFstD w)).length + 1) ^ k') true)
      (pairEncode (pairSndD w)
        (pairEncode (pairFstD (pairFstD w)) (pairSndD (pairFstD w)))))

/-- The XOR-shifted round is polynomial-time.
**Proof sketch.** As the OR round, with the per-round test precomposed with
the truncating XOR of the carried mask and the sliced block
(`Complexity.polyTimeComputable_xorD`). -/
private theorem polyTimeComputable_xorStep {V : Language Bool}
    (hV : PolyTimeComputable (fun z => [MultiTapeTM.indicator V z])) (a k : ℕ) :
    PolyTimeComputable (xorStep V a k) := by
  have hcd : PolyTimeComputable (fun s => pairFstD (pairSndD s)) :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hmask : PolyTimeComputable (fun s => pairFstD (pairSndD (pairSndD s))) :=
    polyTimeComputable_pairFstD.comp
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have hzz : PolyTimeComputable (fun s => pairSndD (pairSndD (pairSndD s))) :=
    polyTimeComputable_pairSndD.comp
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have ht1 : PolyTimeComputable (fun s => [isNilB (pairFstD s)]) :=
    polyTimeComputable_isNil.comp polyTimeComputable_pairFstD
  have ht2 : PolyTimeComputable (fun s => [isNilB (pairFstD (pairSndD s))]) :=
    polyTimeComputable_isNil.comp hcd
  have hblk : PolyTimeComputable (fun s =>
      pairSndD (sliceTakeAt a k (pairSndD (pairSndD (pairSndD s))))) :=
    polyTimeComputable_pairSndD.comp ((polyTimeComputable_sliceTakeAt a k).comp hzz)
  have htest : PolyTimeComputable (fun s =>
      [MultiTapeTM.indicator V
        (pairEncode (pairFstD (pairSndD (pairSndD (pairSndD s))))
          (xorD (pairEncode (pairFstD (pairSndD (pairSndD s)))
            (pairSndD (sliceTakeAt a k (pairSndD (pairSndD (pairSndD s))))))))]) :=
    hV.comp ((polyTimeComputable_pairFstD.comp hzz).pairEncode
      (polyTimeComputable_xorD.comp (hmask.pairEncode hblk)))
  have hflag : PolyTimeComputable (fun s =>
      if MultiTapeTM.indicator V
          (pairEncode (pairFstD (pairSndD (pairSndD (pairSndD s))))
            (xorD (pairEncode (pairFstD (pairSndD (pairSndD s)))
              (pairSndD (sliceTakeAt a k (pairSndD (pairSndD (pairSndD s)))))))) then [true]
        else pairFstD s) :=
    polyTimeComputable_ite htest (polyTimeComputable_const [true])
      polyTimeComputable_pairFstD
  have hrest : PolyTimeComputable (fun s =>
      pairEncode ((pairFstD (pairSndD s)).drop 1)
        (pairEncode (pairFstD (pairSndD (pairSndD s)))
          (sliceDropAt a k (pairSndD (pairSndD (pairSndD s)))))) :=
    (polyTimeComputable_tail.comp hcd).pairEncode
      (hmask.pairEncode ((polyTimeComputable_sliceDropAt a k).comp hzz))
  have hinner := polyTimeComputable_ite ht2 (polyTimeComputable_const blockDone)
    (hflag.pairEncode hrest)
  exact polyTimeComputable_ite ht1 (polyTimeComputable_const blockDone) hinner

private theorem polyTimeComputable_xorInit (a' k' : ℕ) :
    PolyTimeComputable (xorInit a' k') := by
  have hx : PolyTimeComputable (fun w => pairFstD (pairFstD w)) :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD
  have hu : PolyTimeComputable (fun w => pairSndD (pairFstD w)) :=
    polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD
  have hcnt : PolyTimeComputable (fun w =>
      List.replicate (a' * ((pairFstD (pairFstD w)).length + 1) ^ k') true) :=
    (polyTimeComputable_polyUnary a' k').comp hx
  exact (polyTimeComputable_const [false]).pairEncode
    (hcnt.pairEncode (polyTimeComputable_pairSndD.pairEncode (hx.pairEncode hu)))

/-- One XOR-shifted round respects the slack measure `|s| + 16·|countdown s|`.
**Proof sketch.** As the majority round's bound; the mask is copied verbatim
and the joint-projection bound `length_pair_components_le` charges it against
the old state. -/
private theorem length_xorStep_le (V : Language Bool) (a k : ℕ) (s : List Bool) :
    (xorStep V a k s).length +
      16 * (pairFstD (pairSndD (xorStep V a k s))).length ≤
      max (s.length + 16 * (pairFstD (pairSndD s)).length) 2 := by
  unfold xorStep
  cases h1 : isNilB (pairFstD s) with
  | true =>
    simp only [if_pos rfl]
    refine le_trans ?_ (le_max_right _ _)
    simp [blockDone, length_pairEncode, pairFstD_nil]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases h2 : isNilB (pairFstD (pairSndD s)) with
    | true =>
      simp only [if_pos rfl]
      refine le_trans ?_ (le_max_right _ _)
      simp [blockDone, length_pairEncode, pairFstD_nil]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hf : pairFstD s ≠ [] := by simpa [isNilB] using h1
      have hcd : pairFstD (pairSndD s) ≠ [] := by simpa [isNilB] using h2
      have hs := eq_pairEncode_of_pairFstD_ne hf
      have ht := eq_pairEncode_of_pairFstD_ne hcd
      refine le_trans ?_ (le_max_left _ _)
      have hfl : (if MultiTapeTM.indicator V
          (pairEncode (pairFstD (pairSndD (pairSndD (pairSndD s))))
            (xorD (pairEncode (pairFstD (pairSndD (pairSndD s)))
              (pairSndD (sliceTakeAt a k (pairSndD (pairSndD (pairSndD s)))))))) then [true]
          else pairFstD s).length ≤ (pairFstD s).length := by
        cases MultiTapeTM.indicator V
          (pairEncode (pairFstD (pairSndD (pairSndD (pairSndD s))))
            (xorD (pairEncode (pairFstD (pairSndD (pairSndD s)))
              (pairSndD (sliceTakeAt a k (pairSndD (pairSndD (pairSndD s))))))))
        · simp
        · simpa using Nat.one_le_iff_ne_zero.mpr
            (by simpa [List.length_eq_zero_iff] using hf)
      have hslice := length_sliceDropAt_le a k (pairSndD (pairSndD (pairSndD s)))
      have hslice' : (sliceDropAt a k (pairSndD (pairSndD (pairSndD s)))).length ≤
          (pairSndD (pairSndD (pairSndD s))).length + 2 := le_trans hslice (by omega)
      have hY := length_pair_components_le (pairSndD (pairSndD s))
      have hlens : s.length =
          2 * (pairFstD s).length + 2 +
            (2 * (pairFstD (pairSndD s)).length + 2 + (pairSndD (pairSndD s)).length) := by
        conv_lhs => rw [hs]
        rw [length_pairEncode]
        congr 2
        conv_lhs => rw [ht]
        rw [length_pairEncode]
      have hcd1 : 1 ≤ (pairFstD (pairSndD s)).length :=
        Nat.one_le_iff_ne_zero.mpr (by simpa [List.length_eq_zero_iff] using hcd)
      simp only [pairSndD_pairEncode, pairFstD_pairEncode, length_pairEncode,
        List.length_drop]
      omega

/-- Orbit envelope for the XOR-shifted loop. -/
private theorem length_xorStep_iterate (V : Language Bool) (a k : ℕ)
    (w : List Bool) (i : ℕ) :
    ((xorStep V a k)^[i] w).length ≤ 17 * (w.length + 1) ^ 1 := by
  have hmax : ((xorStep V a k)^[i] w).length +
      16 * (pairFstD (pairSndD ((xorStep V a k)^[i] w))).length ≤
      max (w.length + 16 * (pairFstD (pairSndD w)).length) 2 := by
    induction i with
    | zero => simpa using le_max_left _ _
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact le_trans (length_xorStep_le V a k _) (max_le ih (le_max_right _ _))
  have h1 : (pairFstD (pairSndD w)).length ≤ w.length :=
    le_trans (length_pairFstD_le _) (length_pairSndD_le w)
  rw [pow_one]
  omega

/-- The done state is absorbing for the XOR-shifted loop. -/
private theorem xorStep_done (V : Language Bool) (a k : ℕ) :
    xorStep V a k blockDone = blockDone := by
  unfold xorStep
  simp [blockDone, isNilB]

/-- Closed form of the XOR-shifted loop's orbit up to countdown exhaustion.
**Proof sketch.** As the OR orbit, with the carried mask constant and the
per-round indicator applied to the mask XORed with the current block
(`xorD_pairEncode`). -/
private theorem xorStep_orbit (V : Language Bool) (a k a' k' : ℕ) (w : List Bool)
    {i : ℕ} (hi : i ≤ a' * ((pairFstD (pairFstD w)).length + 1) ^ k') :
    (xorStep V a k)^[i] (xorInit a' k' w) =
      pairEncode
        [(List.range i).any (fun j => MultiTapeTM.indicator V
          (pairEncode (pairFstD (pairFstD w))
            (List.zipWith xor (pairSndD w) (blockAt a k (pairFstD w) j))))]
        (pairEncode
          (List.replicate (a' * ((pairFstD (pairFstD w)).length + 1) ^ k' - i) true)
          (pairEncode (pairSndD w)
            (pairEncode (pairFstD (pairFstD w))
              ((pairSndD (pairFstD w)).drop
                (i * (a * ((pairFstD (pairFstD w)).length + 1) ^ k)))))) := by
  induction i with
  | zero => simp [xorInit]
  | succ i ih =>
    have hii : i ≤ a' * ((pairFstD (pairFstD w)).length + 1) ^ k' :=
      Nat.le_of_succ_le hi
    rw [Function.iterate_succ_apply', ih hii]
    have hcd : a' * ((pairFstD (pairFstD w)).length + 1) ^ k' - i =
        (a' * ((pairFstD (pairFstD w)).length + 1) ^ k' - (i + 1)) + 1 := by omega
    rw [hcd, List.replicate_succ]
    unfold xorStep
    rw [if_neg (by simp [isNilB]), pairSndD_pairEncode, if_neg (by simp [isNilB])]
    simp only [pairFstD_pairEncode, pairSndD_pairEncode]
    have hdrop1 : (true :: List.replicate
        (a' * ((pairFstD (pairFstD w)).length + 1) ^ k' - (i + 1)) true).drop 1 =
        List.replicate (a' * ((pairFstD (pairFstD w)).length + 1) ^ k' - (i + 1)) true :=
      rfl
    have hslice2 : sliceDropAt a k (pairEncode (pairFstD (pairFstD w))
        ((pairSndD (pairFstD w)).drop
          (i * (a * ((pairFstD (pairFstD w)).length + 1) ^ k)))) =
        pairEncode (pairFstD (pairFstD w))
          ((pairSndD (pairFstD w)).drop
            ((i + 1) * (a * ((pairFstD (pairFstD w)).length + 1) ^ k))) := by
      rw [sliceDropAt, pairFstD_pairEncode, pairSndD_pairEncode, List.drop_drop]
      congr 2
      ring
    rw [hdrop1, hslice2]
    congr 2
    simp only [sliceTakeAt, pairFstD_pairEncode, pairSndD_pairEncode, xorD_pairEncode]
    rw [List.range_succ, List.any_append]
    cases hb : MultiTapeTM.indicator V (pairEncode (pairFstD (pairFstD w))
        (List.zipWith xor (pairSndD w)
          (((pairSndD (pairFstD w)).drop
            (i * (a * ((pairFstD (pairFstD w)).length + 1) ^ k))).take
              (a * ((pairFstD (pairFstD w)).length + 1) ^ k)))) with
    | true =>
      have hb' : MultiTapeTM.indicator V (pairEncode (pairFstD (pairFstD w))
          (List.zipWith xor (pairSndD w) (blockAt a k (pairFstD w) i))) = true := hb
      simp [hb']
    | false =>
      have hb' : MultiTapeTM.indicator V (pairEncode (pairFstD (pairFstD w))
          (List.zipWith xor (pairSndD w) (blockAt a k (pairFstD w) i))) = false := hb
      simp [hb']

/-- Beyond exhaustion the XOR-shifted orbit sits at the done state. -/
private theorem xorStep_orbit_done (V : Language Bool) (a k a' k' : ℕ) (w : List Bool)
    {i : ℕ} (hi : a' * ((pairFstD (pairFstD w)).length + 1) ^ k' < i) :
    (xorStep V a k)^[i] (xorInit a' k' w) = blockDone := by
  set K := a' * ((pairFstD (pairFstD w)).length + 1) ^ k' with hK
  obtain ⟨j, rfl⟩ : ∃ j, i = j + (K + 1) := ⟨i - (K + 1), by omega⟩
  rw [Function.iterate_add_apply]
  have hend : (xorStep V a k)^[K + 1] (xorInit a' k' w) = blockDone := by
    rw [Function.iterate_succ_apply', xorStep_orbit V a k a' k' w (le_refl K)]
    unfold xorStep
    rw [if_neg (by simp [isNilB]), pairSndD_pairEncode, pairFstD_pairEncode]
    rw [if_pos (by simp [isNilB, hK])]
  rw [hend]
  clear hi
  induction j with
  | zero => simp
  | succ j ih => rw [Function.iterate_succ_apply', ih, xorStep_done]

/-- The XOR-shifted loop's machine-level output is the single aggregated bit.
**Proof sketch.** As the OR output lemma, over the nested pairing: the
countdown is scheduled at the inner first component's length, which the
initial state's length dominates. -/
private theorem xorLoop_output (V : Language Bool) (a k a' k' : ℕ) (w : List Bool) :
    (List.range (a' * ((xorInit a' k' w).length + 1) ^ k' + 1)).flatMap
      (fun i => anyEmit ((xorStep V a k)^[i] (xorInit a' k' w))) =
      [(List.range (a' * ((pairFstD (pairFstD w)).length + 1) ^ k')).any
        (fun j => MultiTapeTM.indicator V (pairEncode (pairFstD (pairFstD w))
          (List.zipWith xor (pairSndD w) (blockAt a k (pairFstD w) j))))] := by
  set K := a' * ((pairFstD (pairFstD w)).length + 1) ^ k' with hK
  have hlen : (pairFstD (pairFstD w)).length ≤ (xorInit a' k' w).length := by
    have h1 : (pairFstD (pairFstD w)).length ≤ w.length :=
      le_trans (length_pairFstD_le _) (length_pairFstD_le w)
    simp only [xorInit, length_pairEncode, List.length_replicate, List.length_cons,
      List.length_nil]
    omega
  have hKN : K < a' * ((xorInit a' k' w).length + 1) ^ k' + 1 := by
    have := Nat.mul_le_mul_left a'
      (Nat.pow_le_pow_left (Nat.add_le_add_right hlen 1) k')
    omega
  refine flatMap_range_eq_single hKN (fun i _ => ?_)
  rcases Nat.lt_trichotomy i K with hiK | rfl | hiK
  · rw [if_neg (by omega), xorStep_orbit V a k a' k' w (le_of_lt hiK)]
    unfold anyEmit
    rw [if_neg (by simp [isNilB]), pairSndD_pairEncode, pairFstD_pairEncode]
    rw [if_neg (by simp [isNilB]; omega)]
  · rw [if_pos rfl, xorStep_orbit V a k a' k' w (le_refl K)]
    unfold anyEmit
    rw [if_neg (by simp [isNilB]), pairSndD_pairEncode, pairFstD_pairEncode]
    rw [if_pos (by simp [isNilB]; omega), pairFstD_pairEncode]
  · rw [if_neg (by omega), xorStep_orbit_done V a k a' k' w hiK]
    unfold anyEmit
    rw [if_pos (by simp [blockDone, isNilB])]

/-- The XOR-then-OR aggregated block test of a polynomial-time one-bit
indicator is polynomial-time: the input is a nested pair
`⟨⟨x, u⟩, v⟩`; block `i` is drawn from `u`, XORed bitwise with `v`
(truncating, `Complexity.xorD`), and tested paired with `x`.

**Proof sketch.** As `Complexity.polyTimeComputable_blockAnyTest`, with the
per-round test precomposed with the XOR mask: the loop state additionally
carries `v`, and the round's test input is
`pairEncode x (xorD (pairEncode v block))`
(`Complexity.polyTimeComputable_xorD`). -/
theorem polyTimeComputable_blockXorAnyTest {V : Language Bool}
    (hV : PolyTimeComputable (fun z => [MultiTapeTM.indicator V z]))
    (a k a' k' : ℕ) :
    PolyTimeComputable (fun w =>
      [(List.range (a' * ((pairFstD (pairFstD w)).length + 1) ^ k')).any
        (fun i => MultiTapeTM.indicator V (pairEncode (pairFstD (pairFstD w))
          (List.zipWith xor (pairSndD w) (blockAt a k (pairFstD w) i))))]) := by
  have hloop := polyTimeComputable_emitIter (polyTimeComputable_xorStep hV a k)
    polyTimeComputable_anyEmit a' k' 17 1 (length_xorStep_iterate V a k)
  have heq : (fun w => [(List.range (a' * ((pairFstD (pairFstD w)).length + 1) ^ k')).any
      (fun i => MultiTapeTM.indicator V (pairEncode (pairFstD (pairFstD w))
        (List.zipWith xor (pairSndD w) (blockAt a k (pairFstD w) i))))]) =
      ((fun v => (List.range (a' * (v.length + 1) ^ k' + 1)).flatMap
        (fun i => anyEmit ((xorStep V a k)^[i] v))) ∘ xorInit a' k') := by
    funext w
    rw [Function.comp_apply, xorLoop_output V a k a' k' w]
  rw [heq]
  exact hloop.comp (polyTimeComputable_xorInit a' k')

end Complexity
```

## ===== TCSlib/Complexity/ClassNP/PolyTimeBlockMajority.lean =====

```
/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.ClassNP.PolyTimeBlockTests

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The majority-aggregated block test

The strict-majority customer of the bounded block-query loop
(`TCSlib.Complexity.ClassNP.PolyTimeBlockLoop`), split from
`TCSlib.Complexity.ClassNP.PolyTimeBlockTests` for size: the loop state
carries two unary vote counters, and at countdown exhaustion the emitted bit
is their strict comparison.

## Main definitions

None — the loop state, step, and chunk functions are private to this file.

## Main results

* `Complexity.polyTimeComputable_blockMajorityTest` — the strict-majority
  aggregated one-bit block test of a polynomial-time one-bit indicator is
  polynomial-time.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§7.4.1, repeated trials with a majority
  vote; Theorem 7.17.)
-/

namespace Complexity

open Turing

/-! #### The majority-aggregating loop -/

/-- One round of the majority-aggregating block loop on state
`pairEncode [true] (pairEncode countdown (pairEncode (pairEncode uT uF)
(pairEncode x rem)))`: push one vote onto the passed (`uT`) or failed (`uF`)
unary counter according to the indicator of the current block, drop the
block, decrement the countdown. -/
private noncomputable def majStep (V : Language Bool) (a k : ℕ) (s : List Bool) : List Bool :=
  if isNilB (pairFstD s) then blockDone
  else if isNilB (pairFstD (pairSndD s)) then blockDone
  else
    pairEncode [true]
      (pairEncode ((pairFstD (pairSndD s)).drop 1)
        (pairEncode
          (if MultiTapeTM.indicator V
              (sliceTakeAt a k (pairSndD (pairSndD (pairSndD s)))) then
            pairEncode (true :: pairFstD (pairFstD (pairSndD (pairSndD s))))
              (pairSndD (pairFstD (pairSndD (pairSndD s))))
          else
            pairEncode (pairFstD (pairFstD (pairSndD (pairSndD s))))
              (true :: pairSndD (pairFstD (pairSndD (pairSndD s)))))
          (sliceDropAt a k (pairSndD (pairSndD (pairSndD s))))))

/-- The chunk function: at countdown exhaustion, emit one bit comparing the
two unary vote counters strictly (`uF < uT`). -/
private def majEmit (s : List Bool) : List Bool :=
  if isNilB (pairFstD s) then []
  else if isNilB (pairFstD (pairSndD s)) then
    [!decide ((pairFstD (pairFstD (pairSndD (pairSndD s)))).length ≤
      (pairSndD (pairFstD (pairSndD (pairSndD s)))).length)]
  else []

/-- The initial state: live marker, unary countdown `a'·(n+1)^k'`, empty vote
counters, and the normalized input pair. -/
private def majInit (a' k' : ℕ) (z : List Bool) : List Bool :=
  pairEncode [true]
    (pairEncode (List.replicate (a' * ((pairFstD z).length + 1) ^ k') true)
      (pairEncode (pairEncode [] [])
        (pairEncode (pairFstD z) (pairSndD z))))

/-- The majority round is polynomial-time.
**Proof sketch.** As the OR round, with the flag update replaced by the
two-counter vote push, assembled from the same `FP` combinators. -/
private theorem polyTimeComputable_majStep {V : Language Bool}
    (hV : PolyTimeComputable (fun z => [MultiTapeTM.indicator V z])) (a k : ℕ) :
    PolyTimeComputable (majStep V a k) := by
  have hcd : PolyTimeComputable (fun s => pairFstD (pairSndD s)) :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hzz : PolyTimeComputable (fun s => pairSndD (pairSndD (pairSndD s))) :=
    polyTimeComputable_pairSndD.comp
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have hacc : PolyTimeComputable (fun s => pairFstD (pairSndD (pairSndD s))) :=
    polyTimeComputable_pairFstD.comp
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have ht1 : PolyTimeComputable (fun s => [isNilB (pairFstD s)]) :=
    polyTimeComputable_isNil.comp polyTimeComputable_pairFstD
  have ht2 : PolyTimeComputable (fun s => [isNilB (pairFstD (pairSndD s))]) :=
    polyTimeComputable_isNil.comp hcd
  have hind : PolyTimeComputable (fun s =>
      [MultiTapeTM.indicator V (sliceTakeAt a k (pairSndD (pairSndD (pairSndD s))))]) :=
    hV.comp ((polyTimeComputable_sliceTakeAt a k).comp hzz)
  have huT : PolyTimeComputable (fun s =>
      pairFstD (pairFstD (pairSndD (pairSndD s)))) :=
    polyTimeComputable_pairFstD.comp hacc
  have huF : PolyTimeComputable (fun s =>
      pairSndD (pairFstD (pairSndD (pairSndD s)))) :=
    polyTimeComputable_pairSndD.comp hacc
  have hconsT : PolyTimeComputable (fun s =>
      true :: pairFstD (pairFstD (pairSndD (pairSndD s)))) :=
    (polyTimeComputable_prepend [true]).comp huT
  have hconsF : PolyTimeComputable (fun s =>
      true :: pairSndD (pairFstD (pairSndD (pairSndD s)))) :=
    (polyTimeComputable_prepend [true]).comp huF
  have hvote : PolyTimeComputable (fun s =>
      if MultiTapeTM.indicator V
          (sliceTakeAt a k (pairSndD (pairSndD (pairSndD s)))) then
        pairEncode (true :: pairFstD (pairFstD (pairSndD (pairSndD s))))
          (pairSndD (pairFstD (pairSndD (pairSndD s))))
      else
        pairEncode (pairFstD (pairFstD (pairSndD (pairSndD s))))
          (true :: pairSndD (pairFstD (pairSndD (pairSndD s))))) :=
    polyTimeComputable_ite hind (hconsT.pairEncode huF) (huT.pairEncode hconsF)
  have hrest : PolyTimeComputable (fun s =>
      pairEncode ((pairFstD (pairSndD s)).drop 1)
        (pairEncode
          (if MultiTapeTM.indicator V
              (sliceTakeAt a k (pairSndD (pairSndD (pairSndD s)))) then
            pairEncode (true :: pairFstD (pairFstD (pairSndD (pairSndD s))))
              (pairSndD (pairFstD (pairSndD (pairSndD s))))
          else
            pairEncode (pairFstD (pairFstD (pairSndD (pairSndD s))))
              (true :: pairSndD (pairFstD (pairSndD (pairSndD s)))))
          (sliceDropAt a k (pairSndD (pairSndD (pairSndD s)))))) :=
    (polyTimeComputable_tail.comp hcd).pairEncode
      (hvote.pairEncode ((polyTimeComputable_sliceDropAt a k).comp hzz))
  have hinner := polyTimeComputable_ite ht2 (polyTimeComputable_const blockDone)
    ((polyTimeComputable_const [true]).pairEncode hrest)
  exact polyTimeComputable_ite ht1 (polyTimeComputable_const blockDone) hinner

/-- The majority chunk function is polynomial-time.
**Proof sketch.** The emitted bit is the negated pair length test
`Complexity.polyTimeComputable_lenLe` on the swapped vote counters, guarded
by the two emptiness tests. -/
private theorem polyTimeComputable_majEmit : PolyTimeComputable majEmit := by
  have hacc : PolyTimeComputable (fun s => pairFstD (pairSndD (pairSndD s))) :=
    polyTimeComputable_pairFstD.comp
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have ht1 : PolyTimeComputable (fun s => [isNilB (pairFstD s)]) :=
    polyTimeComputable_isNil.comp polyTimeComputable_pairFstD
  have ht2 : PolyTimeComputable (fun s => [isNilB (pairFstD (pairSndD s))]) :=
    polyTimeComputable_isNil.comp
      (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
  have hswap : PolyTimeComputable (fun s =>
      pairEncode (pairSndD (pairFstD (pairSndD (pairSndD s))))
        (pairFstD (pairFstD (pairSndD (pairSndD s))))) :=
    (polyTimeComputable_pairSndD.comp hacc).pairEncode
      (polyTimeComputable_pairFstD.comp hacc)
  have hle : PolyTimeComputable (fun s =>
      [decide ((pairFstD (pairFstD (pairSndD (pairSndD s)))).length ≤
        (pairSndD (pairFstD (pairSndD (pairSndD s)))).length)]) := by
    have h := polyTimeComputable_lenLe.comp hswap
    have heq : (fun s =>
        [decide ((pairFstD (pairFstD (pairSndD (pairSndD s)))).length ≤
          (pairSndD (pairFstD (pairSndD (pairSndD s)))).length)]) =
        ((fun z => [decide ((pairSndD z).length ≤ (pairFstD z).length)]) ∘
          (fun s => pairEncode (pairSndD (pairFstD (pairSndD (pairSndD s))))
            (pairFstD (pairFstD (pairSndD (pairSndD s)))))) := by
      funext s
      simp [Function.comp]
    rw [heq]
    exact h
  exact polyTimeComputable_ite ht1 (polyTimeComputable_const [])
    (polyTimeComputable_ite ht2 (polyTimeComputable_not hle)
      (polyTimeComputable_const []))

private theorem polyTimeComputable_majInit (a' k' : ℕ) :
    PolyTimeComputable (majInit a' k') := by
  have hcnt : PolyTimeComputable
      (fun z => List.replicate (a' * ((pairFstD z).length + 1) ^ k') true) :=
    (polyTimeComputable_polyUnary a' k').comp polyTimeComputable_pairFstD
  exact (polyTimeComputable_const [true]).pairEncode
    (hcnt.pairEncode ((polyTimeComputable_const (pairEncode [] [])).pairEncode
      (polyTimeComputable_pairFstD.pairEncode polyTimeComputable_pairSndD)))

/-- The vote push grows the accumulator by at most four symbols. -/
private theorem length_majVote_le (b : Bool) (acc : List Bool) :
    (if b then pairEncode (true :: pairFstD acc) (pairSndD acc)
      else pairEncode (pairFstD acc) (true :: pairSndD acc)).length ≤ acc.length + 4 := by
  have hb := length_pair_components_le acc
  cases b with
  | true =>
    rw [if_pos rfl, length_pairEncode, List.length_cons]
    omega
  | false =>
    rw [if_neg (by simp), length_pairEncode, List.length_cons]
    omega

/-- One majority round respects the slack measure `|s| + 16·|countdown s|`.
**Proof sketch.** As the OR round's length bound, except that the vote push
can grow the state by a bounded constant (`length_majVote_le`); the countdown
loses one symbol per round, so sixteen units of slack per remaining round
absorb the growth. -/
private theorem length_majStep_le (V : Language Bool) (a k : ℕ) (s : List Bool) :
    (majStep V a k s).length +
      16 * (pairFstD (pairSndD (majStep V a k s))).length ≤
      max (s.length + 16 * (pairFstD (pairSndD s)).length) 2 := by
  unfold majStep
  cases h1 : isNilB (pairFstD s) with
  | true =>
    simp only [if_pos rfl]
    refine le_trans ?_ (le_max_right _ _)
    simp [blockDone, length_pairEncode, pairFstD_nil]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases h2 : isNilB (pairFstD (pairSndD s)) with
    | true =>
      simp only [if_pos rfl]
      refine le_trans ?_ (le_max_right _ _)
      simp [blockDone, length_pairEncode, pairFstD_nil]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hf : pairFstD s ≠ [] := by simpa [isNilB] using h1
      have hcd : pairFstD (pairSndD s) ≠ [] := by simpa [isNilB] using h2
      have hs := eq_pairEncode_of_pairFstD_ne hf
      have ht := eq_pairEncode_of_pairFstD_ne hcd
      refine le_trans ?_ (le_max_left _ _)
      have hvote := length_majVote_le
        (MultiTapeTM.indicator V (sliceTakeAt a k (pairSndD (pairSndD (pairSndD s)))))
        (pairFstD (pairSndD (pairSndD s)))
      have hslice := length_sliceDropAt_le a k (pairSndD (pairSndD (pairSndD s)))
      have hslice' : (sliceDropAt a k (pairSndD (pairSndD (pairSndD s)))).length ≤
          (pairSndD (pairSndD (pairSndD s))).length + 2 := le_trans hslice (by omega)
      have hY := length_pair_components_le (pairSndD (pairSndD s))
      have hlens : s.length =
          2 * (pairFstD s).length + 2 +
            (2 * (pairFstD (pairSndD s)).length + 2 + (pairSndD (pairSndD s)).length) := by
        conv_lhs => rw [hs]
        rw [length_pairEncode]
        congr 2
        conv_lhs => rw [ht]
        rw [length_pairEncode]
      have hcd1 : 1 ≤ (pairFstD (pairSndD s)).length :=
        Nat.one_le_iff_ne_zero.mpr (by simpa [List.length_eq_zero_iff] using hcd)
      have hf1 : 1 ≤ (pairFstD s).length :=
        Nat.one_le_iff_ne_zero.mpr (by simpa [List.length_eq_zero_iff] using hf)
      simp only [pairSndD_pairEncode, pairFstD_pairEncode, length_pairEncode,
        List.length_drop, List.length_cons, List.length_nil]
      omega

/-- Orbit envelope for the majority loop. -/
private theorem length_majStep_iterate (V : Language Bool) (a k : ℕ)
    (w : List Bool) (i : ℕ) :
    ((majStep V a k)^[i] w).length ≤ 17 * (w.length + 1) ^ 1 := by
  have hmax : ((majStep V a k)^[i] w).length +
      16 * (pairFstD (pairSndD ((majStep V a k)^[i] w))).length ≤
      max (w.length + 16 * (pairFstD (pairSndD w)).length) 2 := by
    induction i with
    | zero => simpa using le_max_left _ _
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact le_trans (length_majStep_le V a k _) (max_le ih (le_max_right _ _))
  have h1 : (pairFstD (pairSndD w)).length ≤ w.length :=
    le_trans (length_pairFstD_le _) (length_pairSndD_le w)
  rw [pow_one]
  omega

/-- The done state is absorbing for the majority loop. -/
private theorem majStep_done (V : Language Bool) (a k : ℕ) :
    majStep V a k blockDone = blockDone := by
  unfold majStep
  simp [blockDone, isNilB]

/-- Closed form of the majority loop's orbit up to countdown exhaustion.
**Proof sketch.** As the OR orbit, with `List.countP` over `List.range`
replacing the OR: the vote push turns the passed counter `cT i` into
`cT i + 1` exactly when the current block's indicator holds
(`List.countP_append` at `List.range_succ`), and the failed counter is
`i - cT i` throughout. -/
private theorem majStep_orbit (V : Language Bool) (a k a' k' : ℕ) (z : List Bool)
    {i : ℕ} (hi : i ≤ a' * ((pairFstD z).length + 1) ^ k') :
    (majStep V a k)^[i] (majInit a' k' z) =
      pairEncode [true]
        (pairEncode
          (List.replicate (a' * ((pairFstD z).length + 1) ^ k' - i) true)
          (pairEncode
            (pairEncode
              (List.replicate ((List.range i).countP (fun j =>
                MultiTapeTM.indicator V
                  (pairEncode (pairFstD z) (blockAt a k z j)))) true)
              (List.replicate (i - (List.range i).countP (fun j =>
                MultiTapeTM.indicator V
                  (pairEncode (pairFstD z) (blockAt a k z j)))) true))
            (pairEncode (pairFstD z)
              ((pairSndD z).drop (i * (a * ((pairFstD z).length + 1) ^ k)))))) := by
  induction i with
  | zero => simp [majInit]
  | succ i ih =>
    have hii : i ≤ a' * ((pairFstD z).length + 1) ^ k' := Nat.le_of_succ_le hi
    rw [Function.iterate_succ_apply', ih hii]
    have hcd : a' * ((pairFstD z).length + 1) ^ k' - i =
        (a' * ((pairFstD z).length + 1) ^ k' - (i + 1)) + 1 := by omega
    rw [hcd, List.replicate_succ]
    unfold majStep
    rw [if_neg (by simp [isNilB]), pairSndD_pairEncode, if_neg (by simp [isNilB])]
    simp only [pairFstD_pairEncode, pairSndD_pairEncode]
    have hle : (List.range i).countP (fun j =>
        MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j))) ≤ i :=
      le_trans List.countP_le_length (by simp)
    have hcnt : (List.range (i + 1)).countP (fun j =>
        MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j))) =
        (List.range i).countP (fun j =>
          MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j))) +
        (if MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z i))
          then 1 else 0) := by
      rw [List.range_succ, List.countP_append]
      simp [List.countP_cons]
    have hdrop1 : (true :: List.replicate
        (a' * ((pairFstD z).length + 1) ^ k' - (i + 1)) true).drop 1 =
        List.replicate (a' * ((pairFstD z).length + 1) ^ k' - (i + 1)) true := rfl
    have hslice2 : sliceDropAt a k (pairEncode (pairFstD z)
        ((pairSndD z).drop (i * (a * ((pairFstD z).length + 1) ^ k)))) =
        pairEncode (pairFstD z)
          ((pairSndD z).drop ((i + 1) * (a * ((pairFstD z).length + 1) ^ k))) := by
      rw [sliceDropAt, pairFstD_pairEncode, pairSndD_pairEncode, List.drop_drop]
      congr 2
      ring
    have hvoteq : (if MultiTapeTM.indicator V (sliceTakeAt a k (pairEncode (pairFstD z)
        ((pairSndD z).drop (i * (a * ((pairFstD z).length + 1) ^ k))))) then
          pairEncode (true :: List.replicate ((List.range i).countP (fun j =>
            MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j)))) true)
            (List.replicate (i - (List.range i).countP (fun j =>
              MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j)))) true)
        else
          pairEncode (List.replicate ((List.range i).countP (fun j =>
            MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j)))) true)
            (true :: List.replicate (i - (List.range i).countP (fun j =>
              MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j)))) true)) =
        pairEncode
          (List.replicate ((List.range (i + 1)).countP (fun j =>
            MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j)))) true)
          (List.replicate (i + 1 - (List.range (i + 1)).countP (fun j =>
            MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j)))) true) := by
      rw [sliceTakeAt, pairFstD_pairEncode, pairSndD_pairEncode]
      cases hb : MultiTapeTM.indicator V (pairEncode (pairFstD z)
          (((pairSndD z).drop (i * (a * ((pairFstD z).length + 1) ^ k))).take
            (a * ((pairFstD z).length + 1) ^ k))) with
      | true =>
        have hb' : MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z i))
            = true := hb
        have hcT1 : (List.range (i + 1)).countP (fun j =>
            MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j))) =
            (List.range i).countP (fun j =>
              MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j))) + 1 := by
          rw [hcnt, hb']
          simp
        rw [if_pos rfl, hcT1, List.replicate_succ,
          show i + 1 - ((List.range i).countP (fun j =>
            MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j))) + 1) =
            i - (List.range i).countP (fun j =>
              MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j)))
          from by omega]
      | false =>
        have hb' : MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z i))
            = false := hb
        have hcT0 : (List.range (i + 1)).countP (fun j =>
            MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j))) =
            (List.range i).countP (fun j =>
              MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j))) := by
          rw [hcnt, hb']
          simp
        rw [if_neg (by simp), hcT0,
          show i + 1 - (List.range i).countP (fun j =>
            MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j))) =
            (i - (List.range i).countP (fun j =>
              MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j)))) + 1
          from by omega, List.replicate_succ]
    rw [hdrop1, hslice2, hvoteq]

/-- Beyond exhaustion the majority orbit sits at the done state. -/
private theorem majStep_orbit_done (V : Language Bool) (a k a' k' : ℕ) (z : List Bool)
    {i : ℕ} (hi : a' * ((pairFstD z).length + 1) ^ k' < i) :
    (majStep V a k)^[i] (majInit a' k' z) = blockDone := by
  set K := a' * ((pairFstD z).length + 1) ^ k' with hK
  obtain ⟨j, rfl⟩ : ∃ j, i = j + (K + 1) := ⟨i - (K + 1), by omega⟩
  rw [Function.iterate_add_apply]
  have hend : (majStep V a k)^[K + 1] (majInit a' k' z) = blockDone := by
    rw [Function.iterate_succ_apply', majStep_orbit V a k a' k' z (le_refl K)]
    unfold majStep
    rw [if_neg (by simp [isNilB]), pairSndD_pairEncode, pairFstD_pairEncode]
    rw [if_pos (by simp [isNilB, hK])]
  rw [hend]
  clear hi
  induction j with
  | zero => simp
  | succ j ih => rw [Function.iterate_succ_apply', ih, majStep_done]

/-- The majority loop's machine-level output is the single aggregated bit.
**Proof sketch.** As the OR output lemma; at exhaustion the emitted
comparison of the unary counters `¬(cT ≤ K - cT)` is the strict majority
`K < 2·cT`, by `decide_not` and arithmetic. -/
private theorem majLoop_output (V : Language Bool) (a k a' k' : ℕ) (z : List Bool) :
    (List.range (a' * ((majInit a' k' z).length + 1) ^ k' + 1)).flatMap
      (fun i => majEmit ((majStep V a k)^[i] (majInit a' k' z))) =
      [decide (a' * ((pairFstD z).length + 1) ^ k' <
        2 * (List.range (a' * ((pairFstD z).length + 1) ^ k')).countP
          (fun j => MultiTapeTM.indicator V
            (pairEncode (pairFstD z) (blockAt a k z j))))] := by
  set K := a' * ((pairFstD z).length + 1) ^ k' with hK
  have hlen : (pairFstD z).length ≤ (majInit a' k' z).length := by
    simp only [majInit, length_pairEncode, List.length_replicate, List.length_cons,
      List.length_nil]
    omega
  have hKN : K < a' * ((majInit a' k' z).length + 1) ^ k' + 1 := by
    have := Nat.mul_le_mul_left a'
      (Nat.pow_le_pow_left (Nat.add_le_add_right hlen 1) k')
    omega
  have hcT : (List.range K).countP (fun j =>
      MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j))) ≤ K :=
    le_trans List.countP_le_length (by simp)
  refine flatMap_range_eq_single hKN (fun i _ => ?_)
  rcases Nat.lt_trichotomy i K with hiK | rfl | hiK
  · rw [if_neg (by omega), majStep_orbit V a k a' k' z (le_of_lt hiK)]
    unfold majEmit
    rw [if_neg (by simp [isNilB]), pairSndD_pairEncode, pairFstD_pairEncode]
    rw [if_neg (by simp [isNilB]; omega)]
  · rw [if_pos rfl, majStep_orbit V a k a' k' z (le_refl K)]
    unfold majEmit
    rw [if_neg (by simp [isNilB]), pairSndD_pairEncode, pairFstD_pairEncode]
    rw [if_pos (by simp [isNilB]; omega)]
    simp only [pairSndD_pairEncode, pairFstD_pairEncode, List.length_replicate]
    congr 1
    rw [← decide_not]
    exact decide_eq_decide.mpr (by omega)
  · rw [if_neg (by omega), majStep_orbit_done V a k a' k' z hiK]
    unfold majEmit
    rw [if_pos (by simp [blockDone, isNilB])]

/-- The strict-majority-aggregated block test of a polynomial-time one-bit
indicator is polynomial-time.

**Proof sketch.** As `Complexity.polyTimeComputable_blockAnyTest`, with the
flag replaced by two unary vote counters (passed and failed blocks); at
countdown exhaustion the emitted bit is the strict comparison of their
lengths (`Complexity.polyTimeComputable_lenLe` after a `pairSwap`), which
equals `a'·(n+1)^k' < 2·(passed votes)` since the counts sum to the round
total. -/
theorem polyTimeComputable_blockMajorityTest {V : Language Bool}
    (hV : PolyTimeComputable (fun z => [MultiTapeTM.indicator V z]))
    (a k a' k' : ℕ) :
    PolyTimeComputable (fun z =>
      [decide (a' * ((pairFstD z).length + 1) ^ k' <
        2 * (List.range (a' * ((pairFstD z).length + 1) ^ k')).countP
          (fun i => MultiTapeTM.indicator V
            (pairEncode (pairFstD z) (blockAt a k z i))))]) := by
  have hloop := polyTimeComputable_emitIter (polyTimeComputable_majStep hV a k)
    polyTimeComputable_majEmit a' k' 17 1 (length_majStep_iterate V a k)
  have heq : (fun z => [decide (a' * ((pairFstD z).length + 1) ^ k' <
      2 * (List.range (a' * ((pairFstD z).length + 1) ^ k')).countP
        (fun i => MultiTapeTM.indicator V
          (pairEncode (pairFstD z) (blockAt a k z i))))]) =
      ((fun w => (List.range (a' * (w.length + 1) ^ k' + 1)).flatMap
        (fun i => majEmit ((majStep V a k)^[i] w))) ∘ majInit a' k') := by
    funext z
    rw [Function.comp_apply, majLoop_output V a k a' k' z]
  rw [heq]
  exact hloop.comp (polyTimeComputable_majInit a' k')

end Complexity
```

## ===== TCSlib/Complexity/ClassNP/PClosure.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.ClassNP.CoNP
import TCSlib.Complexity.ClassNP.PolyTimePairing
import TCSlib.Complexity.ClassNP.PolyTimeBlockMajority

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Closure properties of `P`

The class `P` [AB09, Def 1.13] is closed under polynomial-time preimages (many-one
reductions), under the Boolean operations, and hence under Boolean functions of finitely
many tests. These facts are used tacitly throughout [AB09] (e.g. ch. 2, ch. 5, ch. 6); here
they are derived from the function class FP (`TCSlib.Complexity.ClassNP.PolyTimePairing`)
and the closure under complement (`Complexity.compl_mem_P`, `ClassNP/CoNP.lean`).

## Main definitions

None — this module only proves theorems about existing definitions.

## Main results

* `Complexity.mem_P_iff_polyTimeComputable` — `V ∈ P` iff its one-bit indicator is in FP;
  `Complexity.mem_P_of_test`, `Complexity.test_of_mem_P` — the same for Boolean tests.
* `Complexity.preimage_mem_P` — `P` is closed under polynomial-time preimages.
* `Complexity.inter_mem_P`, `Complexity.union_mem_P`, `Complexity.empty_mem_P`,
  `Complexity.univ_mem_P` — Boolean closure.
* `Complexity.mem_P_of_atoms` — `P` is closed under Boolean functions of finitely many
  tests.
* `Complexity.lenEq_mem_P`, `lenLe_mem_P`, `lenEq_preimage_mem_P`, `lenLe_preimage_mem_P`
  — length comparisons are in `P`.
* `Complexity.mem_P_of_blockAny`, `Complexity.mem_P_of_blockMajority`,
  `Complexity.mem_P_of_blockXorAny` — `P` is closed under running a `P`-decider on
  polynomially many polynomial-length blocks of the input and aggregating the answers
  (OR / strict majority / XOR-then-OR), the folklore repetition closures used tacitly
  by [AB09] ch. 7 (Theorems 7.8, 7.10, 7.17, 7.18); the machine engine is
  `TCSlib.Complexity.ClassNP.PolyTimeBlockLoop`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.6, Definition 1.13; §2.2.)
-/

namespace Complexity

open Turing

/-! ### `P` and polynomial-time functions -/

/-- `V ∈ P` iff its singleton indicator `x ↦ [1_V(x)]` is polynomial-time computable. -/
theorem mem_P_iff_polyTimeComputable {V : Language Bool} :
    V ∈ P ↔ PolyTimeComputable (fun x => [MultiTapeTM.indicator V x]) := by
  constructor
  · intro h
    obtain ⟨C, c, M, hM⟩ := mem_P_iff.mp h
    exact ⟨M, C, c, hM⟩
  · rintro ⟨M, C, c, hM⟩
    exact mem_P_iff.mpr ⟨C, c, M, hM⟩

/-- **`P` is closed under polynomial-time preimages**: if `V ∈ P` and `g` is
polynomial-time computable then `g⁻¹(V) ∈ P` (the decider of `V` run on `g x`). -/
theorem preimage_mem_P {V : Language Bool} {g : List Bool → List Bool} (hV : V ∈ P)
    (hg : PolyTimeComputable g) : g ⁻¹' V ∈ P :=
  mem_P_iff_polyTimeComputable.mpr ((mem_P_iff_polyTimeComputable.mp hV).comp hg)

/-- A language whose Boolean test is polynomial-time computable (as a one-bit output) is
in `P`. -/
theorem mem_P_of_test {b : List Bool → Bool} (h : PolyTimeComputable (fun z => [b z])) :
    {z | b z = true} ∈ P := by
  rw [mem_P_iff_polyTimeComputable]
  convert h using 2 with z
  by_cases hz : b z = true <;> simp [MultiTapeTM.indicator, hz]

/-- The Boolean test of a language in `P` is polynomial-time computable. -/
theorem test_of_mem_P {L : Language Bool} (h : L ∈ P) :
    PolyTimeComputable (fun z => [MultiTapeTM.indicator L z]) :=
  mem_P_iff_polyTimeComputable.mp h

/-! ### Boolean closure -/

/-- **`P` is closed under intersection.** -/
theorem inter_mem_P {L₁ L₂ : Language Bool} (h₁ : L₁ ∈ P) (h₂ : L₂ ∈ P) :
    {z | z ∈ L₁ ∧ z ∈ L₂} ∈ P := by
  have h := mem_P_of_test (polyTimeComputable_and (test_of_mem_P h₁) (test_of_mem_P h₂))
  convert h using 1
  ext z
  by_cases a : z ∈ L₁ <;> by_cases b : z ∈ L₂ <;> simp [MultiTapeTM.indicator, a, b]

/-- **`P` is closed under union** (branching on the first test). -/
theorem union_mem_P {L₁ L₂ : Language Bool} (h₁ : L₁ ∈ P) (h₂ : L₂ ∈ P) :
    {z | z ∈ L₁ ∨ z ∈ L₂} ∈ P := by
  have ht : PolyTimeComputable
      (fun z => [MultiTapeTM.indicator L₁ z || MultiTapeTM.indicator L₂ z]) := by
    convert polyTimeComputable_ite (test_of_mem_P h₁) (polyTimeComputable_const [true])
      (test_of_mem_P h₂) using 1
    funext z
    cases MultiTapeTM.indicator L₁ z <;> rfl
  convert mem_P_of_test ht using 1
  ext z
  by_cases a : z ∈ L₁ <;> by_cases b : z ∈ L₂ <;> simp [MultiTapeTM.indicator, a, b]

/-- The empty language is in `P`. -/
theorem empty_mem_P : ({_z | false = true} : Language Bool) ∈ P :=
  mem_P_of_test (polyTimeComputable_const [false])

/-- The full language is in `P`. -/
theorem univ_mem_P : ({_z | true = true} : Language Bool) ∈ P :=
  mem_P_of_test (polyTimeComputable_const [true])

/-- **`P` is closed under Boolean functions of finitely many tests**: if each test
`b i` decides a language in `P`, so does `z ↦ F (b · z)` for any `F`.

**Proof sketch.** The language is the finite union, over the valuations `β` with
`F β = true`, of the finite intersections `⋂ᵢ {z | b i z = β i}`; each set in the
intersection is a test language or its complement. -/
theorem mem_P_of_atoms {ι : Type} [Fintype ι] [DecidableEq ι] (b : ι → List Bool → Bool)
    (hb : ∀ i, ({z | b i z = true} : Language Bool) ∈ P) (F : (ι → Bool) → Bool) :
    ({z | F (fun i => b i z) = true} : Language Bool) ∈ P := by
  classical
  -- one valuation
  have hval : ∀ β : ι → Bool, ∀ s : Finset ι,
      ({z | ∀ i ∈ s, b i z = β i} : Language Bool) ∈ P := by
    intro β s
    induction s using Finset.induction_on with
    | empty => simpa using univ_mem_P
    | insert i s hi ih =>
      have hi' : ({z | b i z = β i} : Language Bool) ∈ P := by
        cases hβ : β i
        · have := compl_mem_P (hb i)
          convert this using 1
          ext z
          change b i z = false ↔ ¬ (b i z = true)
          simp
        · exact hb i
      have := inter_mem_P hi' ih
      convert this using 1
      ext z
      simp
  have hunion : ∀ s : Finset (ι → Bool),
      ({z | ∃ β ∈ s, ∀ i, b i z = β i} : Language Bool) ∈ P := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using empty_mem_P
    | insert β s hβ ih =>
      have h1 := hval β Finset.univ
      have := union_mem_P h1 ih
      convert this using 1
      ext z
      change (∃ β' ∈ insert β s, ∀ i, b i z = β' i) ↔
        (∀ i ∈ Finset.univ, b i z = β i) ∨ (∃ β' ∈ s, ∀ i, b i z = β' i)
      simp
  have h := hunion (Finset.univ.filter fun β => F β = true)
  convert h using 1
  ext z
  simp only [Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hz; exact ⟨_, hz, fun i => rfl⟩
  · rintro ⟨β, hβ, hb'⟩
    have : (fun i => b i z) = β := funext hb'
    rw [this]; exact hβ

/-! ### Length comparisons -/

/-- The words whose two components under the total default projections
(`pairFstD`/`pairSndD`, both `[]` on malformed input) have equal length form a language
in `P`. Malformed words project to `([], [])` and are therefore members — e.g. `[]`
itself; the well-formed-pair corollaries below are unaffected (P0 round 1, finding 5). -/
theorem lenEq_mem_P : {z : List Bool | (pairFstD z).length = (pairSndD z).length} ∈ P := by
  have h := mem_P_of_test polyTimeComputable_lenEq
  simpa using h

/-- The words whose second default-projected component is at most as long as the first
form a language in `P` — with the same totalization as `Complexity.lenEq_mem_P`:
malformed words project to `([], [])` and are members. -/
theorem lenLe_mem_P : {z : List Bool | (pairSndD z).length ≤ (pairFstD z).length} ∈ P := by
  have h := mem_P_of_test polyTimeComputable_lenLe
  simpa using h

/-- Comparing the lengths of two polynomial-time computable strings is in `P`. -/
theorem lenEq_preimage_mem_P {f g : List Bool → List Bool} (hf : PolyTimeComputable f)
    (hg : PolyTimeComputable g) : {z | (f z).length = (g z).length} ∈ P := by
  have h := preimage_mem_P lenEq_mem_P (hf.pairEncode hg)
  simpa using h

/-- `|g z| ≤ |f z|` for polynomial-time `f`, `g` is decidable in `P`. -/
theorem lenLe_preimage_mem_P {f g : List Bool → List Bool} (hf : PolyTimeComputable f)
    (hg : PolyTimeComputable g) : {z | (g z).length ≤ (f z).length} ∈ P := by
  have h := preimage_mem_P lenLe_mem_P (hf.pairEncode hg)
  simpa using h

/-! ### Block-query closure

`P` is closed under running a `P`-decider on polynomially many fixed-size blocks of
the second component of a pair and aggregating the answers.  `blockAt a k z i` is the
`i`-th length-`a·(n+1)^k` block of `pairSndD z`, with `n = |pairFstD z|`; the block
count is `a'·(n+1)^k'`.  These are the folklore "repeat the machine polynomially many
times" closures that [AB09] ch. 7 uses tacitly (§7.3, Theorem 7.8; §7.4.1;
Theorems 7.17–7.18); the machine-level loop lives in
`TCSlib.Complexity.ClassNP.PolyTimeBlockLoop`.

Like the length comparisons above, all three languages are total extensions through
the default projections: a malformed word is classified by the same test on its
default-decoded components (for the nested pair, an invalid inner pair leaves only the
outer mask), and `V` is consulted only on re-encoded queries (ch7 fill audit, note 3). -/

/-- **`P` is closed under a polynomial block-OR**: if `V ∈ P` then so is the set of
pairs some of whose `a'·(n+1)^k'` blocks of length `a·(n+1)^k` passes `V`'s test,
paired with the first component. -/
theorem mem_P_of_blockAny {V : Language Bool} (hV : V ∈ P) (a k a' k' : ℕ) :
    {z : List Bool | ∃ i < a' * ((pairFstD z).length + 1) ^ k',
      pairEncode (pairFstD z) (blockAt a k z i) ∈ V} ∈ P := by
  have h := mem_P_of_test (polyTimeComputable_blockAnyTest (test_of_mem_P hV) a k a' k')
  convert h using 1
  ext z
  simp only [Set.mem_setOf_eq, List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨i, hi, hmem⟩
    exact ⟨i, hi, by simp [MultiTapeTM.indicator, hmem]⟩
  · rintro ⟨i, hi, hbit⟩
    refine ⟨i, hi, ?_⟩
    by_contra hmem
    simp [MultiTapeTM.indicator, hmem] at hbit

/-- **`P` is closed under a polynomial block-majority**: if `V ∈ P` then so is the
set of pairs a strict majority of whose `a'·(n+1)^k'` blocks of length `a·(n+1)^k`
passes `V`'s test, paired with the first component. -/
theorem mem_P_of_blockMajority {V : Language Bool} (hV : V ∈ P) (a k a' k' : ℕ) :
    {z : List Bool | a' * ((pairFstD z).length + 1) ^ k' <
      2 * (List.range (a' * ((pairFstD z).length + 1) ^ k')).countP
        (fun i => MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z i)))} ∈ P := by
  have h := mem_P_of_test (polyTimeComputable_blockMajorityTest (test_of_mem_P hV) a k a' k')
  convert h using 1
  ext z
  simp only [Set.mem_setOf_eq, decide_eq_true_eq]

/-- **`P` is closed under a polynomial XOR-shifted block-OR**: on a nested pair
`⟨⟨x, u⟩, v⟩`, if `V ∈ P` then so is the set of nested pairs some of whose
`a'·(|x|+1)^k'` blocks of `u` of length `a·(|x|+1)^k`, XORed bitwise with `v`
(truncating to the shorter word), passes `V`'s test paired with `x`. -/
theorem mem_P_of_blockXorAny {V : Language Bool} (hV : V ∈ P) (a k a' k' : ℕ) :
    {w : List Bool | ∃ i < a' * ((pairFstD (pairFstD w)).length + 1) ^ k',
      pairEncode (pairFstD (pairFstD w))
        (List.zipWith xor (pairSndD w) (blockAt a k (pairFstD w) i)) ∈ V} ∈ P := by
  have h := mem_P_of_test (polyTimeComputable_blockXorAnyTest (test_of_mem_P hV) a k a' k')
  convert h using 1
  ext w
  simp only [Set.mem_setOf_eq, List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨i, hi, hmem⟩
    exact ⟨i, hi, by simp [MultiTapeTM.indicator, hmem]⟩
  · rintro ⟨i, hi, hbit⟩
    refine ⟨i, hi, ?_⟩
    by_contra hmem
    simp [MultiTapeTM.indicator, hmem] at hbit

end Complexity
```

## ===== TCSlib/Complexity/ClassNP/PolyTimePairing.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.ClassNP.PolyTime
import TCSlib.Complexity.TuringMachine.Build.Primitives

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial-time pairing, projections and branching

Closure facts for the function class FP (`Complexity.PolyTimeComputable`, implicit
throughout [AB09, ch. 2]) needed when a reduction must keep its input while computing
from it: constant functions, the threaded payload map, pairing of two polynomial-time
functions through `Turing.pairEncode`, the total pair projections, concatenation,
Boolean branching and length tests, and the unary length maps `x ↦ 1^|x|` and
`x ↦ 1^{C(|x|+1)^d}` (the input of a uniformity machine, [AB09, Def 6.12]). All are
assembled from the proved machine catalog of
`TCSlib.Complexity.TuringMachine.Build.Primitives`. The closure facts for the class `P`
built on them are in `TCSlib.Complexity.ClassNP.PClosure`.

## Main definitions

* `Complexity.pairMapSnd` — on `pairEncode a b`, output `pairEncode a (g b)`; malformed
  words go to `[]`.
* `Complexity.pairFstD`, `Complexity.pairSndD` — total pair projections (`[]` on
  malformed words).

## Main results

* `Complexity.polyTimeComputable_of_linear` — a linear-time machine contract gives a
  polynomial-time computable function.
* `Complexity.polyTimeComputable_const` — constant functions are polynomial-time.
* `Complexity.PolyTimeComputable.pairMapSnd` — the threaded payload map preserves
  polynomial time.
* `Complexity.PolyTimeComputable.pairEncode` — `x ↦ pairEncode (f x) (g x)` is
  polynomial-time when `f` and `g` are.
* `Complexity.polyTimeComputable_unary` — `x ↦ 1^|x|` is polynomial-time;
  `Complexity.polyTimeComputable_polyUnary` — so is `x ↦ 1^{C(|x|+1)^d}`.
* `Complexity.PolyTimeComputable.append` — FP is closed under concatenation.
* `Complexity.polyTimeComputable_pairFstD`, `polyTimeComputable_pairSndD`,
  `polyTimeComputable_pairSwap`, `polyTimeComputable_pairConcat`,
  `polyTimeComputable_prepend` — projections and rearrangements of pairs.
* `Complexity.polyTimeComputable_ite`, `polyTimeComputable_and` — Boolean branching.
* `Complexity.polyTimeComputable_lenLe`, `polyTimeComputable_lenEq` — length tests on
  pairs.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Ch. 2; §6.2, Definition 6.12.)
-/

namespace Complexity

open Turing

/-- A function computed by a finite binary machine within a linear bound `a · (n + 1)`
is polynomial-time computable. -/
theorem polyTimeComputable_of_linear {f : List Bool → List Bool}
    (h : ∃ (M : FinTM Bool) (a : ℕ), M.ComputesFunInTime f (fun n => a * (n + 1))) :
    PolyTimeComputable f := by
  obtain ⟨M, a, hM⟩ := h
  exact ⟨M, a, 1, by simpa only [Nat.pow_one] using hM⟩

/-- Every constant function `fun _ => w` is polynomial-time computable. -/
theorem polyTimeComputable_const (w : List Bool) : PolyTimeComputable (fun _ => w) :=
  polyTimeComputable_of_linear (FinTM.computesFunInTime_const w)

/-- The threaded payload map of `g`: on a pair `pairEncode a b` it outputs
`pairEncode a (g b)` (the first component is carried unchanged), and on a word that is
not a pair it outputs `[]`. -/
def pairMapSnd (g : List Bool → List Bool) (z : List Bool) : List Bool :=
  match pairDecode z with
  | some (a, b) => pairEncode a (g b)
  | none => []

/-- On a pair, the threaded payload map transforms the second component. -/
@[simp]
theorem pairMapSnd_pairEncode (g : List Bool → List Bool) (a b : List Bool) :
    pairMapSnd g (pairEncode a b) = pairEncode a (g b) := by
  simp [pairMapSnd, pairDecode_pairEncode]

/-- If `g` is polynomial-time computable, so is its threaded payload map
`Complexity.pairMapSnd g`.

**Proof sketch.** `Turing.FinTM.computesFunInTime_pairMapSnd` with the monotone
majorant `C (n+1)^c` of `g`'s bound gives a budget `K (n + 1 + C (n+1)^c)`, which is at
most `K (C + 1) (n+1)^(c+1)`. -/
theorem PolyTimeComputable.pairMapSnd {g : List Bool → List Bool}
    (hg : PolyTimeComputable g) : PolyTimeComputable (Complexity.pairMapSnd g) := by
  obtain ⟨G, C, c, hG⟩ := hg
  obtain ⟨M, K, hM⟩ := FinTM.computesFunInTime_pairMapSnd hG
    (by
      intro m n h
      exact Nat.mul_le_mul_left C (Nat.pow_le_pow_left (Nat.add_le_add_right h 1) c))
  refine ⟨M, K * (C + 1), c + 1, fun x => (hM x).mono ?_⟩
  have hn : x.length + 1 ≤ (x.length + 1) ^ (c + 1) := by
    simpa only [Nat.pow_one] using
      Nat.pow_le_pow_right (Nat.succ_pos x.length) (show 1 ≤ c + 1 by omega)
  have hc := Nat.mul_le_mul_left C
    (Nat.pow_le_pow_right (Nat.succ_pos x.length) (Nat.le_succ c))
  calc
    _ ≤ K * ((x.length + 1) ^ (c + 1) + C * (x.length + 1) ^ (c + 1)) :=
      Nat.mul_le_mul_left K (Nat.add_le_add hn hc)
    _ = _ := by ring

/-- Appending to a pair appends to its second component. -/
private lemma pairEncode_append (a b c : List Bool) :
    pairEncode a b ++ c = pairEncode a (b ++ c) := by
  simp [pairEncode, List.append_assoc]

/-- **Pairing two polynomial-time functions is polynomial-time**: if `f` and `g` are
polynomial-time computable, so is `x ↦ pairEncode (f x) (g x)`.

**Proof sketch.** Only the second component of a pair can be transformed in place
(`Complexity.pairMapSnd`), so the first component is built with an empty payload and
then retained. Duplicating `x` (`Turing.FinTM.computesFunInTime_pairDup`) and mapping
the payload gives `H x = pairEncode (f x) []`; duplicating `x` and mapping `H` gives
`s x = pairEncode x (H x)`; duplicating `s x` and mapping `g ∘ fst` gives
`t x = pairEncode (s x) (g x)`. Concatenating the components of `t x`
(`Turing.FinTM.computesFunInTime_pairConcat`) yields
`pairEncode x (pairEncode (f x) (g x))`, whose second component is the result. -/
theorem PolyTimeComputable.pairEncode {f g : List Bool → List Bool}
    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
    PolyTimeComputable (fun x => Turing.pairEncode (f x) (g x)) := by
  have hd := polyTimeComputable_of_linear FinTM.computesFunInTime_pairDup
  have hp := polyTimeComputable_of_linear FinTM.computesFunInTime_pairFst
  have hs := polyTimeComputable_of_linear FinTM.computesFunInTime_pairSnd
  have hc := polyTimeComputable_of_linear FinTM.computesFunInTime_pairConcat
  -- `H x = pairEncode (f x) []`, `s x = pairEncode x (H x)`, `t x = pairEncode (s x) (g x)`
  have hH := (((polyTimeComputable_const []).pairMapSnd).comp hd).comp hf
  have hS := hH.pairMapSnd.comp hd
  have hT := ((hg.comp hp).pairMapSnd.comp hd).comp hS
  -- concatenate, then project the second component
  have h := hs.comp (hc.comp hT)
  convert h using 1
  funext x
  simp only [Function.comp_apply, pairMapSnd_pairEncode, pairDecode_pairEncode,
    Option.map_some, Option.getD_some]
  rw [pairEncode_append, pairEncode_append]
  simp [pairDecode_pairEncode]

/-- The last `true` of `1^(n+1)` is its last letter: stripping it leaves `1ⁿ`. -/
private lemma splitAtLastTrue_replicate_succ (n : ℕ) :
    splitAtLastTrue (List.replicate (n + 1) true) = some (List.replicate n true) := by
  rw [splitAtLastTrue, List.reverse_replicate, List.replicate_succ]
  simp [List.reverse_replicate]

/-- **The unary length map is polynomial-time**: `x ↦ 1^|x|` is polynomial-time
computable. (This is how the input `1ⁿ` of a uniformity machine [AB09, Def 6.12] is
produced from an input of length `n`.)

**Proof sketch.** Pair `x` with `1^(|x|+1)` (the unary polynomial generator at
`1 · (n + 1)¹`, `Turing.FinTM.computesFunInTime_polyUnary`), strip the last `true` of the
second component (`Turing.FinTM.computesFunInTime_stripLast`), and project the second
component (`Turing.FinTM.computesFunInTime_pairSnd`). -/
theorem polyTimeComputable_unary :
    PolyTimeComputable (fun x => List.replicate x.length true) := by
  have hu : PolyTimeComputable (fun x => List.replicate (1 * (x.length + 1) ^ 1) true) := by
    obtain ⟨M, c, hM⟩ := FinTM.computesFunInTime_polyUnary 1 1
    exact ⟨M, c, 2, hM⟩
  have hpair := polyTimeComputable_id.pairEncode hu
  have hstrip : PolyTimeComputable (fun x => match pairDecode x with
      | some (a, v) =>
        match splitAtLastTrue v with
        | some u => Turing.pairEncode a u
        | none => []
      | none => []) := by
    obtain ⟨M, c, hM⟩ := FinTM.computesFunInTime_stripLast
    exact ⟨M, c, 2, hM⟩
  have hs := polyTimeComputable_of_linear FinTM.computesFunInTime_pairSnd
  convert hs.comp (hstrip.comp hpair) using 1
  funext x
  simp only [Function.comp_apply, id, pairDecode_pairEncode, Nat.pow_one, Nat.one_mul,
    splitAtLastTrue_replicate_succ, Option.map_some, Option.getD_some]

/-- **FP is closed under concatenation**: if `f` and `g` are polynomial-time computable,
so is `x ↦ f x ++ g x`. (Pair the two results, `PolyTimeComputable.pairEncode`, then
concatenate the components, `Turing.FinTM.computesFunInTime_pairConcat`.) -/
theorem PolyTimeComputable.append {f g : List Bool → List Bool}
    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
    PolyTimeComputable (fun x => f x ++ g x) := by
  have hc := polyTimeComputable_of_linear FinTM.computesFunInTime_pairConcat
  convert hc.comp (hf.pairEncode hg) using 1
  funext x
  simp [pairDecode_pairEncode]

/-- `x ↦ 1^{C (|x| + 1)^d}` is polynomial-time computable. -/
theorem polyTimeComputable_polyUnary (C d : ℕ) :
    PolyTimeComputable fun x => List.replicate (C * (x.length + 1) ^ d) true := by
  obtain ⟨M, a, hM⟩ := FinTM.computesFunInTime_polyUnary C d
  exact ⟨M, a, d + 1, hM⟩

/-- Prepending a fixed word is polynomial-time. -/
theorem polyTimeComputable_prepend (w : List Bool) : PolyTimeComputable (fun x => w ++ x) :=
  polyTimeComputable_of_linear (FinTM.computesFunInTime_prepend w)

/-! ### Total pair projections -/

/-- The total first projection of a `Turing.pairEncode` pair (`[]` on malformed words). -/
def pairFstD (z : List Bool) : List Bool := ((pairDecode z).map Prod.fst).getD []

/-- The total second projection of a `Turing.pairEncode` pair (`[]` on malformed words). -/
def pairSndD (z : List Bool) : List Bool := ((pairDecode z).map Prod.snd).getD []

/-- The first projection of a pair is its first component. -/
@[simp] theorem pairFstD_pairEncode (a b : List Bool) : pairFstD (pairEncode a b) = a := by
  simp [pairFstD, pairDecode_pairEncode]

/-- The second projection of a pair is its second component. -/
@[simp] theorem pairSndD_pairEncode (a b : List Bool) : pairSndD (pairEncode a b) = b := by
  simp [pairSndD, pairDecode_pairEncode]

/-- The first projection of a word is no longer than the word. -/
theorem length_pairFstD_le (z : List Bool) : (pairFstD z).length ≤ z.length := by
  cases h : pairDecode z with
  | none => simp [pairFstD, h]
  | some ab =>
    obtain ⟨a, b⟩ := ab
    have hz := Turing.eq_pairEncode_of_pairDecode z a b h
    subst hz
    simp [length_pairEncode]
    omega

/-- The first projection is polynomial-time computable. -/
theorem polyTimeComputable_pairFstD : PolyTimeComputable pairFstD :=
  polyTimeComputable_of_linear FinTM.computesFunInTime_pairFst

/-- The second projection is polynomial-time computable. -/
theorem polyTimeComputable_pairSndD : PolyTimeComputable pairSndD :=
  polyTimeComputable_of_linear FinTM.computesFunInTime_pairSnd

/-- Iterated first projections (the root of a nested tuple) are polynomial-time. -/
theorem polyTimeComputable_iterate_pairFstD (n : ℕ) : PolyTimeComputable (pairFstD^[n]) := by
  induction n with
  | zero => simp only [Function.iterate_zero]; exact polyTimeComputable_id
  | succ n ih =>
    rw [Function.iterate_succ']
    exact polyTimeComputable_pairFstD.comp ih

/-- Concatenating the two components of a pair is polynomial-time. -/
theorem polyTimeComputable_pairConcat :
    PolyTimeComputable (fun z => pairFstD z ++ pairSndD z) := by
  have h := polyTimeComputable_of_linear FinTM.computesFunInTime_pairConcat
  convert h using 1
  funext z
  cases hz : pairDecode z with
  | none => simp [pairFstD, pairSndD, hz]
  | some p => cases p; simp [pairFstD, pairSndD, hz]

/-- Swapping the components of a pair is polynomial-time. -/
theorem polyTimeComputable_pairSwap :
    PolyTimeComputable (fun z => pairEncode (pairSndD z) (pairFstD z)) :=
  polyTimeComputable_pairSndD.pairEncode polyTimeComputable_pairFstD

/-! ### Branching and length tests -/

/-- **Polynomial-time branching**: if the test `p` (as a one-bit output) and both branches
are polynomial-time computable, so is `x ↦ if p x then f x else g x`.

**Proof sketch.** The timed branch contract `Turing.FinTM.computesFunInTime_cond` runs
the test, then the selected branch; enlarge the three degrees to their maximum and
absorb the constants. -/
theorem polyTimeComputable_ite {p : List Bool → Bool} {f g : List Bool → List Bool}
    (hp : PolyTimeComputable (fun x => [p x]))
    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
    PolyTimeComputable (fun x => if p x then f x else g x) := by
  obtain ⟨D, A, a, hD⟩ := hp
  obtain ⟨F, B, b, hF⟩ := hf
  obtain ⟨G, C, c, hG⟩ := hg
  obtain ⟨M, K, hM⟩ := FinTM.computesFunInTime_cond hD hF hG
  let e := max a (max b c)
  refine ⟨M, K * (A + B + C + 1), e, fun x => (hM x).mono ?_⟩
  have hpow (d : ℕ) (hd : d ≤ e) : (x.length + 1) ^ d ≤ (x.length + 1) ^ e :=
    Nat.pow_le_pow_right (Nat.succ_pos _) hd
  have ha := Nat.mul_le_mul_left A (hpow a (Nat.le_max_left _ _))
  have hb := Nat.mul_le_mul_left B (hpow b
    ((Nat.le_max_left b c).trans (Nat.le_max_right a (max b c))))
  have hc := Nat.mul_le_mul_left C (hpow c
    ((Nat.le_max_right b c).trans (Nat.le_max_right a (max b c))))
  have hbc : max (B * (x.length + 1) ^ b) (C * (x.length + 1) ^ c) ≤
      B * (x.length + 1) ^ e + C * (x.length + 1) ^ e :=
    max_le (by omega) (by omega)
  have hone := Nat.one_le_pow e (x.length + 1) (Nat.succ_pos _)
  calc
    _ ≤ K * (A * (x.length + 1) ^ e +
        (B * (x.length + 1) ^ e + C * (x.length + 1) ^ e) +
        (x.length + 1) ^ e) :=
      Nat.mul_le_mul_left K (Nat.add_le_add (Nat.add_le_add ha hbc) hone)
    _ = _ := by ring

/-- Polynomial-time Boolean conjunction of two one-bit tests. -/
theorem polyTimeComputable_and {p q : List Bool → Bool}
    (hp : PolyTimeComputable (fun x => [p x])) (hq : PolyTimeComputable (fun x => [q x])) :
    PolyTimeComputable (fun x => [p x && q x]) := by
  convert polyTimeComputable_ite hp hq (polyTimeComputable_const [false]) using 1
  funext x
  cases p x <;> rfl

/-- The length test `|snd z| ≤ |fst z|` on pairs is polynomial-time.

**Proof sketch.** The catalog's threaded length check at `(C, e) = (1, 1)` decides
`|b| ≤ |a| + 1` on `⟨a, b⟩`; apply it to `⟨fst z, 1 :: snd z⟩`. -/
theorem polyTimeComputable_lenLe :
    PolyTimeComputable (fun z => [decide ((pairSndD z).length ≤ (pairFstD z).length)]) := by
  have hchk : PolyTimeComputable (fun x => [match pairDecode x with
      | some (a, b) => decide (b.length ≤ 1 * (a.length + 1) ^ 1)
      | none => false]) := by
    obtain ⟨M, a, hM⟩ := FinTM.computesFunInTime_pairLenCheck 1 1
    exact ⟨M, a, 2, hM⟩
  have hpair : PolyTimeComputable (fun z => pairEncode (pairFstD z) (true :: pairSndD z)) :=
    polyTimeComputable_pairFstD.pairEncode
      ((polyTimeComputable_prepend [true]).comp polyTimeComputable_pairSndD)
  convert hchk.comp hpair using 1
  funext z
  simp [pairDecode_pairEncode]

/-- The length-equality test `|fst z| = |snd z|` on pairs is polynomial-time. -/
theorem polyTimeComputable_lenEq :
    PolyTimeComputable (fun z => [decide ((pairFstD z).length = (pairSndD z).length)]) := by
  have h := polyTimeComputable_and polyTimeComputable_lenLe
    (polyTimeComputable_lenLe.comp polyTimeComputable_pairSwap)
  convert h using 1
  funext z
  simp only [pairFstD_pairEncode, pairSndD_pairEncode]
  congr 1
  by_cases h1 : (pairFstD z).length = (pairSndD z).length
  · simp [h1]
  · rcases Nat.lt_or_gt_of_ne h1 with h2 | h2
    · simp [h1, Nat.not_le_of_lt h2]
    · simp [h1, Nat.not_le_of_lt h2]

end Complexity
```

## ===== TCSlib/Complexity/TuringMachine/Build/Embed.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.List.FinRange
import TCSlib.Complexity.TuringMachine.Simulation
import TCSlib.Complexity.TuringMachine.StateRenaming

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: bank embedding (R1)

The general tape-embedding layer of the machine-construction library
(`machine-library-design.md` §12, R1): a verified routine on its own
`m`-tape set runs on any injectively selected subset of a `k`-tape host's
work tapes, cost unchanged, everything else framed. This is the §5
deferral promoted — the design deferred the general form "until a third
site needs it", and the third, fourth, and fifth sites have arrived (the
chapter-1/2 retrofit families, the Hennie–Stearns conversion, the
two-work-tape universal machine). **Scope, stated precisely** (round-1
note R9): `ι` selects whole distinct physical tapes with coordinates
intact — it does not multiplex several virtual tapes onto zones of one
physical tape, shrink the tape count, or alter the source input word; the
Hennie–Stearns and universal-machine consumers get their zone/virtual-input
representation layers separately, with this module supplying only the
fixed-physical-bank routine relocation. It is the generic form of the private
`emitterBank*`/`emitterP2*` relocation families of
`TCSlib.Complexity.TuringMachine.Build.Primitives`, of the 4A chain's
`clBank*`/`clSlot*` families, and of the retained-tape disciplines that
`Build/Loop.lean` and `Build/Wrappers.lean` carry internally.

**Status: statement skeleton (§12 statement phase).** The transformers and
configuration transports below are real definitions; every contract is
sorried, each with a proof sketch naming its fill obligations.

## Design

Per frozen decision 12.4 there are **two named transformers over one
shared private core** (`embedActionCore`), so each spec stays crisp and a
consumer cites whichever fits:

* `Turing.embedSilentTM` — the W1/capture flavor: the embedded routine's
  emissions are recorded on a designated host work tape `cap` outside the
  selected bank, and the host's physical output stays silent.
* `Turing.embedEmitTM` — the E2/forwarding flavor: emissions pass to the
  host's physical output verbatim.

The two **closed** transformers preserve the source state type and map
the source halt to the host halt; their lockstep is unguarded, holding at
every time with the step count preserved exactly. The round-1 audit
(finding R1) refuted the earlier claim that live-return dispatch could be
left to the seam combinator: a source whose final transition emits and
halts loses that emission either way — the closed embedding is halted
after it, and a seam exit at the sole live state dispatches *before* it.
The **returning** flavors below repair this with an explicit halt-to-live
adapter built into the action core: `Turing.embedSilentRetTM` and
`Turing.embedEmitRetTM` run the source on states `S ⊕ Unit`, execute every
source action **through the halting transition** — the final emission
included — and land in the live return anchor `Sum.inr ()`, which a seam
then consumes as its left exit (`Turing.captureAction`'s and
`Turing.emitterRightTM`'s halt-to-live discipline, now exported).
`Turing.captureAction`/`Turing.capture_run` and
`Turing.emitAction`/`Turing.emit_run` are the fixed-shape precursors
(last-tape capture, identity selection); their statements are untouched.

## Main definitions

* `Turing.embedSilentCfg`, `Turing.embedEmitCfg` — a source configuration
  transported along `ι : Fin m ↪ Fin k`, with the unselected host tapes
  carried as frame parameters.
* `Turing.embedSilentTM`, `Turing.embedEmitTM` — the two closed machine
  transformers.
* `Turing.embedSilentRetTM`, `Turing.embedEmitRetTM` — the two returning
  transformers (round-1 repair R1): source halts land in the live return
  anchor `Sum.inr ()`, with the halting transition executed in full.

## Main results

All sorried (statement phase):

* `Turing.embedSilentTM_runFrom`, `Turing.embedEmitTM_runFrom` — lockstep:
  the transported run is the transport of the source run, same step count.
* `Turing.embedSilentTM_frame`, `Turing.embedEmitTM_frame` — tapes outside
  `Set.range ι` byte-identical with heads unmoved, input position tracking
  the source, output per flavor.
* `Turing.embedSilentTM_visitedByTapeHead`,
  `Turing.embedEmitTM_visitedByTapeHead` (and `_frame` companions),
  `Turing.embedSilentTM_spaceUsedByTape_cap` — per-tape space: host tape
  `ι i` visits exactly the source's tape-`i` cells, unselected tapes visit
  nothing new, and the capture tape is bounded by the recorded output.
* `Turing.embedSilentRetTM_run`, `Turing.embedEmitRetTM_run` — the
  through-halt contracts: live lockstep, then the handover at the source's
  first halt, final emission and source residue preserved, with the return
  anchor reached first exactly there.
* `Turing.embedSilentRetTM_visitedByTapeHead`,
  `Turing.embedEmitRetTM_visitedByTapeHead` — the returning flavors visit
  exactly what the closed flavors visit, at every time.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2; tape-subset simulations are the
  folklore of the §1.3/§1.7 robustness and simulation arguments.)
* [Bon26] É. Bonnet, *classical-complexity*, Lax Archive entry lax-434930,
  module `proofs/Lax434930Proofs/InclusionAux/TimeCompiler/`, commit
  `0c0840319318215fd7b36a9a822b81ce55cf6941`, Apache-2.0, examined
  2026-10-05. Design adaptation with nothing transcribed (different
  toolchain and machine model — TM2-style keyed stacks there, `FinTM`
  tapes with heads here): the bank-embedding shape is `StackRename`'s
  `rename_executes`.
-/

namespace Turing

variable {m k : ℕ} {S : Type*} {x : List Bool}

/-- The partial inverse of the tape selection: the source index that `ι`
sends to host tape `j`, or `none` when `j` is unselected. Injectivity of
`ι` makes the first `List.find?` hit the unique preimage. -/
private def embedSlot (ι : Fin m ↪ Fin k) (j : Fin k) : Option (Fin m) :=
  (List.finRange m).find? fun i => decide (ι i = j)

/-- Searching at a selected tape returns its unique source index. -/
private lemma embedSlot_selected (ι : Fin m ↪ Fin k) (i : Fin m) :
    embedSlot ι (ι i) = some i := by
  unfold embedSlot
  cases hs : (List.finRange m).find? (fun j => decide (ι j = ι i)) with
  | none =>
    have hn := List.find?_eq_none.mp hs i (by simp)
    simp at hn
  | some j =>
    have hj := List.find?_some hs
    have hji : j = i := ι.injective (of_decide_eq_true hj)
    subst j
    rfl

/-- Searching outside the selected bank returns no source index. -/
private lemma embedSlot_unselected (ι : Fin m ↪ Fin k) (j : Fin k)
    (hj : j ∉ Set.range ι) : embedSlot ι j = none := by
  unfold embedSlot
  rw [List.find?_eq_none]
  intro i _
  simp only [decide_eq_true_eq]
  exact fun hij => hj ⟨i, hij⟩

/-- The shared private core of the two embedding transformers (frozen
decision 12.4): transport one source action along `ι`, keeping the input
move and the successor state, performing the source's tape-`i` action on
host tape `ι i`, and leaving every unselected tape stationary and
unwritten — except that an emission is handled per the mode `sink`:
`sink = some cap` records it on host tape `cap` with a right move (the
capture discipline of `Turing.captureAction`) and keeps the host output
silent, while `sink = none` forwards it as the host's physical emission
(the discipline of `Turing.emitAction`). -/
private def embedActionCore (ι : Fin m ↪ Fin k) (sink : Option (Fin k))
    (a : Action m Bool S) : Action k Bool S where
  inputTape := a.inputTape
  workTapes := fun j =>
    match embedSlot ι j with
    | some i => a.workTapes i
    | none =>
      match sink with
      | some cap =>
        if j = cap then
          match a.output with
          | some b => (some (some b), SignType.pos)
          | none => (none, 0)
        else (none, 0)
      | none => (none, 0)
  output :=
    match sink with
    | some _ => none
    | none => a.output
  state := a.state

/-- A source configuration viewed inside a `k`-tape host along the
selection `ι`, suppressing flavor: same control state and input position,
source tape `i` sitting on host tape `ι i` (content and head), the
designated capture tape `cap` holding `pre ++ c.output` — the emissions
recorded so far after a pre-existing prefix — with its head one past that
word, every other unselected tape holding the ambient frame `tapes j` with
its head at `heads j`, and the host's physical output the untouched
`out₀`. Generic form of the `emitterBank*`/`clBank*` configuration
correspondences; for a source of `m` tapes in a host of `m + 1` with the
last tape selected as capture, it degenerates to `Turing.captureCfg` up to
the state embedding (round-1 restatement note: the specialization enlarges
the tape count by one — it is not `m = k`). [Bon26] -/
def embedSilentCfg (ι : Fin m ↪ Fin k) (cap : Fin k)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre out₀ : List Bool) (c : Cfg m Bool S x) : Cfg k Bool S x where
  state := c.state
  inputPos := c.inputPos
  workTapes := fun j =>
    match embedSlot ι j with
    | some i => c.workTapes i
    | none =>
      if j = cap then FinTM.bufferTape (pre ++ c.output) else tapes j
  workTapePos := fun j =>
    match embedSlot ι j with
    | some i => c.workTapePos i
    | none =>
      if j = cap then ((pre ++ c.output).length : ℤ) else heads j
  output := out₀

/-- A source configuration viewed inside a `k`-tape host along the
selection `ι`, forwarding flavor: same control state and input position,
source tape `i` on host tape `ι i`, every unselected tape holding the
ambient frame, and the host's physical output equal to the host's prior
output `pre` followed by everything the source has emitted. Generic form
of the `emitterP2*` relocation correspondences; at `ι = id` it is
`Turing.emitCfg` up to the state embedding. [Bon26] -/
def embedEmitCfg (ι : Fin m ↪ Fin k)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre : List Bool) (c : Cfg m Bool S x) : Cfg k Bool S x where
  state := c.state
  inputPos := c.inputPos
  workTapes := fun j =>
    match embedSlot ι j with
    | some i => c.workTapes i
    | none => tapes j
  workTapePos := fun j =>
    match embedSlot ι j with
    | some i => c.workTapePos i
    | none => heads j
  output := pre ++ c.output

/-- **R1, the suppressing embedding transformer** (design §12, decision
12.4; [Bon26]). Run the `m`-tape machine `M` on the host tapes selected by
`ι`, recording every emission on the designated host work tape `cap`
(intended outside `Set.range ι`) and emitting nothing physically — the
W1/capture flavor. States are preserved and the source halt is the host
halt; live return dispatch is the seam combinator's job. -/
def embedSilentTM (ι : Fin m ↪ Fin k) (cap : Fin k)
    (M : MultiTapeTM m Bool S) : MultiTapeTM k Bool S where
  q₀ := M.q₀
  tr := fun q inp w =>
    embedActionCore ι (some cap) (M.tr q inp fun i => w (ι i))

/-- **R1, the forwarding embedding transformer** (design §12, decision
12.4; [Bon26]). Run the `m`-tape machine `M` on the host tapes selected by
`ι`, with every emission passed to the host's physical output verbatim —
the E2 flavor. States are preserved and the source halt is the host
halt. -/
def embedEmitTM (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Bool S) :
    MultiTapeTM k Bool S where
  q₀ := M.q₀
  tr := fun q inp w =>
    embedActionCore ι none (M.tr q inp fun i => w (ι i))

/-- Applying the silent core commutes with configuration transport.
**Proof sketch.** Selected tapes perform the source action. Off-bank tapes
are stationary, except that capture appends the emitted bit at the old
word length. Input movement and successor control are copied verbatim. -/
private lemma embedSilent_apply (ι : Fin m ↪ Fin k) (cap : Fin k)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre out₀ : List Bool) (c : Cfg m Bool S x) (a : Action m Bool S) :
    (embedActionCore ι (some cap) a).apply
        (embedSilentCfg ι cap tapes heads pre out₀ c) =
      embedSilentCfg ι cap tapes heads pre out₀ (a.apply c) := by
  refine Cfg.ext rfl rfl ?_ ?_ ?_
  · funext j
    cases hs : embedSlot ι j with
    | some i => simp [embedActionCore, embedSilentCfg, Action.apply, hs]
    | none =>
      by_cases hj : j = cap
      · subst j
        cases ho : a.output <;>
          simp [embedActionCore, embedSilentCfg, Action.apply, hs, ho,
            ← List.append_assoc, FinTM.bufferTape_append]
      · simp [embedActionCore, embedSilentCfg, Action.apply, hs, hj]
  · funext j
    cases hs : embedSlot ι j with
    | some i => simp [embedActionCore, embedSilentCfg, Action.apply, hs]
    | none =>
      by_cases hj : j = cap
      · subst j
        cases ho : a.output <;>
          simp [embedActionCore, embedSilentCfg, Action.apply, hs, ho,
            Nat.cast_add, add_assoc]
      · simp [embedActionCore, embedSilentCfg, Action.apply, hs, hj]
  · simp [embedActionCore, embedSilentCfg, Action.apply]

/-- The silent host reads the source action and executes all its effects
in one step; halted configurations remain fixed on both sides. -/
private lemma embedSilent_step (ι : Fin m ↪ Fin k) (cap : Fin k)
    (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre out₀ : List Bool) (c : Cfg m Bool S x) :
    (embedSilentTM ι cap M).step (embedSilentCfg ι cap tapes heads pre out₀ c) =
      embedSilentCfg ι cap tapes heads pre out₀ (M.step c) := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => simp [embedSilentCfg, hs]
  | some q =>
    rw [show (embedSilentCfg ι cap tapes heads pre out₀ c).state = some q from hs]
    dsimp only
    have hr : (fun i => (embedSilentCfg ι cap tapes heads pre out₀ c).workTapeSymbols
        (ι i)) = c.workTapeSymbols := by
      funext i
      simp [Cfg.workTapeSymbols, embedSilentCfg, embedSlot_selected]
    change (embedActionCore ι (some cap) (M.tr q c.inputSymbol _)).apply _ = _
    rw [hr]
    exact embedSilent_apply ι cap tapes heads pre out₀ c _

/-- **R1 lockstep, suppressing flavor** (spec, fill pending — design §12;
[Bon26], `rename_executes`). The transported run *is* the transport of the
source run, at every time and with the step count preserved exactly: `t`
host steps simulate `t` source steps. No liveness guard is needed — the
transformer preserves states, so a halted source transports to a halted
host and both runs stall together.

**Proof sketch.** One-step commutation plus
`Turing.MultiTapeTM.runFrom_comm_of_step`. For the step: a halted source
makes both sides the identity. For a live source state, the host reads the
source symbols through `ι` (the transport puts source tape `i` at `ι i`),
so the host applies `embedActionCore` of the very action the source
applies; componentwise, selected tapes update as the source's
(`Turing.Action.apply` through the `embedSlot` inverse, whose two
equations `embedSlot ι (ι i) = some i` and `embedSlot ι j = none` off the
range are the `List.find?` glue obligations), unselected tapes receive the
stationary no-write action, the capture tape appends the optional emission
at head `|pre ++ c.output|` (`Turing.FinTM.bufferTape_append`, exactly as
in `capture_apply`), silence keeps the output at `out₀`, and the states
agree. -/
theorem embedSilentTM_runFrom (ι : Fin m ↪ Fin k) (cap : Fin k)
    (hcap : cap ∉ Set.range ι) (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre out₀ : List Bool) (c : Cfg m Bool S x) (t : ℕ) :
    (embedSilentTM ι cap M).runFrom
        (embedSilentCfg ι cap tapes heads pre out₀ c) t =
      embedSilentCfg ι cap tapes heads pre out₀ (M.runFrom c t) := by
  exact MultiTapeTM.runFrom_comm_of_step
    (embedSilentCfg ι cap tapes heads pre out₀)
    (embedSilent_step ι cap M tapes heads pre out₀) c t

/-- **R1 frame, suppressing flavor** (spec, fill pending — design §12).
Along the whole transported run, every host tape outside the selected bank
and distinct from the capture tape is byte-identical to its ambient frame
with its head unmoved; the input position tracks the source's; and the
host's physical output stays `out₀` (output silence).

**Proof sketch.** Project the lockstep equation
`embedSilentTM_runFrom` componentwise: the transport's `workTapes`/
`workTapePos` at an unselected `j ≠ cap` are the frame parameters by the
`embedSlot` off-range equation, its `inputPos` is the source's, and its
`output` is `out₀` by definition. -/
theorem embedSilentTM_frame (ι : Fin m ↪ Fin k) (cap : Fin k)
    (hcap : cap ∉ Set.range ι) (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre out₀ : List Bool) (c : Cfg m Bool S x) (t : ℕ) :
    (∀ j : Fin k, j ∉ Set.range ι → j ≠ cap →
      ((embedSilentTM ι cap M).runFrom
          (embedSilentCfg ι cap tapes heads pre out₀ c) t).workTapes j
        = tapes j ∧
      ((embedSilentTM ι cap M).runFrom
          (embedSilentCfg ι cap tapes heads pre out₀ c) t).workTapePos j
        = heads j) ∧
    ((embedSilentTM ι cap M).runFrom
        (embedSilentCfg ι cap tapes heads pre out₀ c) t).inputPos
      = (M.runFrom c t).inputPos ∧
    ((embedSilentTM ι cap M).runFrom
        (embedSilentCfg ι cap tapes heads pre out₀ c) t).output = out₀ := by
  rw [embedSilentTM_runFrom ι cap hcap]
  refine ⟨?_, rfl, rfl⟩
  intro j hj hjc
  simp [embedSilentCfg, embedSlot_unselected ι j hj, hjc]

/-- **R1 space, suppressing flavor, selected tapes** (spec, fill pending —
design §12: "cells visited on host tape `ι i` equal cells visited on
source tape `i`"). The visited set of host tape `ι i` up to time `t` is
exactly the source's visited set of tape `i`, so the per-tape space
agrees on the nose.

**Proof sketch.** Both visited sets are images of `Finset.range (t + 1)`
under the respective head trajectories
(`Turing.MultiTapeTM.visitedByTapeHead`), and the lockstep equation
`embedSilentTM_runFrom` makes the trajectories pointwise equal at `ι i`
via the transport's `workTapePos` clause and `embedSlot ι (ι i) = some i`.
The cardinality clause is `congrArg Finset.card`. -/
theorem embedSilentTM_visitedByTapeHead (ι : Fin m ↪ Fin k) (cap : Fin k)
    (hcap : cap ∉ Set.range ι) (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre out₀ : List Bool) (c : Cfg m Bool S x) (t : ℕ) (i : Fin m) :
    (embedSilentTM ι cap M).visitedByTapeHead
        (embedSilentCfg ι cap tapes heads pre out₀ c) t (ι i)
      = M.visitedByTapeHead c t i ∧
    (embedSilentTM ι cap M).spaceUsedByTape
        (embedSilentCfg ι cap tapes heads pre out₀ c) t (ι i)
      = M.spaceUsedByTape c t i := by
  have hv : (embedSilentTM ι cap M).visitedByTapeHead
      (embedSilentCfg ι cap tapes heads pre out₀ c) t (ι i) =
      M.visitedByTapeHead c t i := by
    unfold MultiTapeTM.visitedByTapeHead
    congr 1
    funext u
    rw [embedSilentTM_runFrom ι cap hcap]
    simp [embedSilentCfg, embedSlot_selected]
  exact ⟨hv, congrArg Finset.card hv⟩

/-- **R1 space, suppressing flavor, unselected tapes** (spec, fill
pending — design §12: "unselected tapes visit nothing new"). A host tape
outside the selected bank and distinct from the capture tape visits
exactly the singleton of its initial head position, so its space usage is
one cell.

**Proof sketch.** By `embedSilentTM_frame` the head of such a tape never
moves, so the trajectory image collapses to `{heads j}`; the cardinality
clause is `Finset.card_singleton`. -/
theorem embedSilentTM_visitedByTapeHead_frame (ι : Fin m ↪ Fin k)
    (cap : Fin k) (hcap : cap ∉ Set.range ι) (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre out₀ : List Bool) (c : Cfg m Bool S x) (t : ℕ)
    (j : Fin k) (hj : j ∉ Set.range ι) (hjc : j ≠ cap) :
    (embedSilentTM ι cap M).visitedByTapeHead
        (embedSilentCfg ι cap tapes heads pre out₀ c) t j = {heads j} ∧
    (embedSilentTM ι cap M).spaceUsedByTape
        (embedSilentCfg ι cap tapes heads pre out₀ c) t j = 1 := by
  have hv : (embedSilentTM ι cap M).visitedByTapeHead
      (embedSilentCfg ι cap tapes heads pre out₀ c) t j = {heads j} := by
    unfold MultiTapeTM.visitedByTapeHead
    simp_rw [embedSilentTM_runFrom ι cap hcap]
    simp [embedSilentCfg, embedSlot_unselected ι j hj, hjc]
    exact Finset.image_const ⟨0, by simp⟩ _
  refine ⟨hv, ?_⟩
  simp [MultiTapeTM.spaceUsedByTape, hv]

/-- **R1 space, suppressing flavor, the capture tape** (spec, fill
pending — design §12; every unselected tape is accounted for, the capture
tape included). The capture tape's space usage up to time `t` is bounded
by the number of emissions recorded in that window plus one: the head
starts one past `pre ++ c.output` and advances right exactly once per
recorded emission.

**Proof sketch.** By lockstep the capture head position at time `t'` is
`|pre| + |(M.runFrom c t').output|`, which is nondecreasing in `t'` with
increments bounded by one emission per step; the visited set is therefore
the integer interval from the initial head to the final one, of
cardinality the output growth plus one
(`Turing.MultiTapeTM.output_prefix` gives the monotone growth).

**Fill appendix.** For the stated upper bound, the formal proof only
needs containment in this interval, followed by its cardinality. -/
theorem embedSilentTM_spaceUsedByTape_cap (ι : Fin m ↪ Fin k) (cap : Fin k)
    (hcap : cap ∉ Set.range ι) (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre out₀ : List Bool) (c : Cfg m Bool S x) (t : ℕ) :
    (embedSilentTM ι cap M).spaceUsedByTape
        (embedSilentCfg ι cap tapes heads pre out₀ c) t cap
      ≤ (M.runFrom c t).output.length - c.output.length + 1 := by
  have hgrowth : c.output.length ≤ (M.runFrom c t).output.length := by
    simpa using (M.output_prefix c (Nat.zero_le t)).length_le
  have hsub : (embedSilentTM ι cap M).visitedByTapeHead
      (embedSilentCfg ι cap tapes heads pre out₀ c) t cap ⊆
      Finset.Icc ((pre ++ c.output).length : ℤ)
        ((pre ++ (M.runFrom c t).output).length : ℤ) := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
    have hut : u ≤ t := Nat.le_of_lt_succ (Finset.mem_range.mp hu)
    have hlo : c.output.length ≤ (M.runFrom c u).output.length := by
      simpa using (M.output_prefix c (Nat.zero_le u)).length_le
    have hhi := (M.output_prefix c hut).length_le
    rw [embedSilentTM_runFrom ι cap hcap]
    simp only [embedSilentCfg, embedSlot_unselected ι cap hcap, ↓reduceIte,
      Finset.mem_Icc, List.length_append, Nat.cast_add]
    constructor <;> omega
  calc
    _ ≤ (Finset.Icc ((pre ++ c.output).length : ℤ)
        ((pre ++ (M.runFrom c t).output).length : ℤ)).card :=
      Finset.card_le_card hsub
    _ = (M.runFrom c t).output.length - c.output.length + 1 := by
      rw [Int.card_Icc]
      simp only [List.length_append, Nat.cast_add]
      omega

/-- Applying the forwarding core commutes with configuration transport:
selected tapes update identically, the frame stays fixed, and appending
the optional emission associates with the existing output prefix. -/
private lemma embedEmit_apply (ι : Fin m ↪ Fin k)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre : List Bool) (c : Cfg m Bool S x) (a : Action m Bool S) :
    (embedActionCore ι none a).apply (embedEmitCfg ι tapes heads pre c) =
      embedEmitCfg ι tapes heads pre (a.apply c) := by
  refine Cfg.ext rfl rfl ?_ ?_ ?_
  · funext j
    cases hs : embedSlot ι j <;>
      simp [embedActionCore, embedEmitCfg, Action.apply, hs]
  · funext j
    cases hs : embedSlot ι j <;>
      simp [embedActionCore, embedEmitCfg, Action.apply, hs]
  · simp [embedActionCore, embedEmitCfg, Action.apply, List.append_assoc]

/-- The forwarding host reads the same source action and executes it
completely in one step, including an emission on a halting transition. -/
private lemma embedEmit_step (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre : List Bool) (c : Cfg m Bool S x) :
    (embedEmitTM ι M).step (embedEmitCfg ι tapes heads pre c) =
      embedEmitCfg ι tapes heads pre (M.step c) := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => simp [embedEmitCfg, hs]
  | some q =>
    rw [show (embedEmitCfg ι tapes heads pre c).state = some q from hs]
    dsimp only
    have hr : (fun i => (embedEmitCfg ι tapes heads pre c).workTapeSymbols
        (ι i)) = c.workTapeSymbols := by
      funext i
      simp [Cfg.workTapeSymbols, embedEmitCfg, embedSlot_selected]
    change (embedActionCore ι none (M.tr q c.inputSymbol _)).apply _ = _
    rw [hr]
    exact embedEmit_apply ι tapes heads pre c _

/-- **R1 lockstep, forwarding flavor** (spec, fill pending — design §12;
[Bon26], `rename_executes`). The transported run is the transport of the
source run, at every time and with the step count preserved exactly;
emissions are forwarded, so the host's output is `pre` followed by the
source's output at every instant (through the transport).

**Proof sketch.** As `embedSilentTM_runFrom`, with the capture clause
replaced by the output clause: the one-step commutation appends the
optional emission after `pre` (associativity of `++`, exactly as in
`emit_apply`), and `Turing.MultiTapeTM.runFrom_comm_of_step` iterates. -/
theorem embedEmitTM_runFrom (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre : List Bool) (c : Cfg m Bool S x) (t : ℕ) :
    (embedEmitTM ι M).runFrom (embedEmitCfg ι tapes heads pre c) t =
      embedEmitCfg ι tapes heads pre (M.runFrom c t) := by
  exact MultiTapeTM.runFrom_comm_of_step (embedEmitCfg ι tapes heads pre)
    (embedEmit_step ι M tapes heads pre) c t

/-- **R1 frame, forwarding flavor** (spec, fill pending — design §12).
Along the whole transported run, every host tape outside the selected
bank is byte-identical to its ambient frame with its head unmoved, the
input position tracks the source's, and the host's physical output is
`pre` followed by the source's output so far.

**Proof sketch.** Project `embedEmitTM_runFrom` componentwise, as in the
suppressing flavor; the output clause is the transport's definition. -/
theorem embedEmitTM_frame (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre : List Bool) (c : Cfg m Bool S x) (t : ℕ) :
    (∀ j : Fin k, j ∉ Set.range ι →
      ((embedEmitTM ι M).runFrom
          (embedEmitCfg ι tapes heads pre c) t).workTapes j = tapes j ∧
      ((embedEmitTM ι M).runFrom
          (embedEmitCfg ι tapes heads pre c) t).workTapePos j = heads j) ∧
    ((embedEmitTM ι M).runFrom
        (embedEmitCfg ι tapes heads pre c) t).inputPos
      = (M.runFrom c t).inputPos ∧
    ((embedEmitTM ι M).runFrom
        (embedEmitCfg ι tapes heads pre c) t).output
      = pre ++ (M.runFrom c t).output := by
  rw [embedEmitTM_runFrom]
  refine ⟨?_, rfl, rfl⟩
  intro j hj
  simp [embedEmitCfg, embedSlot_unselected ι j hj]

/-- **R1 space, forwarding flavor, selected tapes** (spec, fill pending —
design §12). The visited set of host tape `ι i` up to time `t` is exactly
the source's visited set of tape `i`; per-tape space agrees on the nose.

**Proof sketch.** As `embedSilentTM_visitedByTapeHead`: pointwise equal
head trajectories from `embedEmitTM_runFrom`, then image and
cardinality. -/
theorem embedEmitTM_visitedByTapeHead (ι : Fin m ↪ Fin k)
    (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre : List Bool) (c : Cfg m Bool S x) (t : ℕ) (i : Fin m) :
    (embedEmitTM ι M).visitedByTapeHead
        (embedEmitCfg ι tapes heads pre c) t (ι i)
      = M.visitedByTapeHead c t i ∧
    (embedEmitTM ι M).spaceUsedByTape
        (embedEmitCfg ι tapes heads pre c) t (ι i)
      = M.spaceUsedByTape c t i := by
  have hv : (embedEmitTM ι M).visitedByTapeHead
      (embedEmitCfg ι tapes heads pre c) t (ι i) =
      M.visitedByTapeHead c t i := by
    unfold MultiTapeTM.visitedByTapeHead
    congr 1
    funext u
    rw [embedEmitTM_runFrom]
    simp [embedEmitCfg, embedSlot_selected]
  exact ⟨hv, congrArg Finset.card hv⟩

/-- **R1 space, forwarding flavor, unselected tapes** (spec, fill
pending — design §12). A host tape outside the selected bank visits
exactly the singleton of its initial head position; its space usage is
one cell.

**Proof sketch.** By `embedEmitTM_frame` the head never moves; collapse
the trajectory image to `{heads j}` and take cardinalities. -/
theorem embedEmitTM_visitedByTapeHead_frame (ι : Fin m ↪ Fin k)
    (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre : List Bool) (c : Cfg m Bool S x) (t : ℕ)
    (j : Fin k) (hj : j ∉ Set.range ι) :
    (embedEmitTM ι M).visitedByTapeHead
        (embedEmitCfg ι tapes heads pre c) t j = {heads j} ∧
    (embedEmitTM ι M).spaceUsedByTape
        (embedEmitCfg ι tapes heads pre c) t j = 1 := by
  have hv : (embedEmitTM ι M).visitedByTapeHead
      (embedEmitCfg ι tapes heads pre c) t j = {heads j} := by
    unfold MultiTapeTM.visitedByTapeHead
    simp_rw [embedEmitTM_runFrom]
    simp only [embedEmitCfg, embedSlot_unselected ι j hj]
    exact Finset.image_const ⟨0, by simp⟩ _
  refine ⟨hv, ?_⟩
  simp [MultiTapeTM.spaceUsedByTape, hv]

/-- **R1′, the returning suppressing embedding** (round-1 repair R1). As
`Turing.embedSilentTM`, on states `S ⊕ Unit`: live source states run the
capture-flavored core, but a source action whose successor is `none` lands
in the **live return anchor** `Sum.inr ()` — the halting transition is
executed in full, its emission recorded on `cap`, before control arrives at
the anchor (the `Turing.captureAction`/`Turing.emitterRightTM` halt-to-live
discipline, exported). The anchor itself idles (stationary, silent, live),
which is exactly what a seam combinator overrides as its left exit. -/
def embedSilentRetTM (ι : Fin m ↪ Fin k) (cap : Fin k)
    (M : MultiTapeTM m Bool S) : MultiTapeTM k Bool (S ⊕ Unit) where
  q₀ := Sum.inl M.q₀
  tr := fun q inp w =>
    match q with
    | Sum.inl s =>
      let a := M.tr s inp fun i => w (ι i)
      let h := embedActionCore ι (some cap) a
      ⟨h.inputTape, h.workTapes, h.output,
        some (a.state.elim (Sum.inr ()) Sum.inl)⟩
    | Sum.inr _ => ⟨0, fun _ => (none, 0), none, some (Sum.inr ())⟩

/-- **R1′, the returning forwarding embedding** (round-1 repair R1). As
`Turing.embedEmitTM`, on states `S ⊕ Unit`, with source halts landing in
the live return anchor `Sum.inr ()` after the halting transition — its
forwarded emission included — has executed in full. -/
def embedEmitRetTM (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Bool S) :
    MultiTapeTM k Bool (S ⊕ Unit) where
  q₀ := Sum.inl M.q₀
  tr := fun q inp w =>
    match q with
    | Sum.inl s =>
      let a := M.tr s inp fun i => w (ι i)
      let h := embedActionCore ι none a
      ⟨h.inputTape, h.workTapes, h.output,
        some (a.state.elim (Sum.inr ()) Sum.inl)⟩
    | Sum.inr _ => ⟨0, fun _ => (none, 0), none, some (Sum.inr ())⟩

/-- Replace an action's optional successor by the live return encoding,
without changing any input, work-tape, or output effect. -/
private def embedReturnAction (a : Action k Bool S) : Action k Bool (S ⊕ Unit) :=
  ⟨a.inputTape, a.workTapes, a.output, some (a.state.elim (Sum.inr ()) Sum.inl)⟩

/-- Encode a closed host configuration with live left states and a live
right return anchor, preserving all four non-control fields. -/
private def embedReturnCfg (c : Cfg k Bool S x) : Cfg k Bool (S ⊕ Unit) x :=
  { c with state := some (c.state.elim (Sum.inr ()) Sum.inl) }

/-- At a live configuration, the return encoding is ordinary left state
mapping; at a halt it instead uses the live right anchor. -/
private lemma embedReturnCfg_live (c : Cfg k Bool S x) (hc : c.state ≠ none) :
    embedReturnCfg c = c.mapState Sum.inl := by
  cases hs : c.state with
  | none => exact (hc hs).elim
  | some q => simp [embedReturnCfg, Cfg.mapState, hs]

/-- Direct comparison of a closed host step with a returning host step.
**Proof sketch.** At a live left state, both hosts execute the same action
and only the successor encoding differs. At a closed halt, the returning
anchor's idle action preserves every non-control field, just as absorption
does on the closed side. No property of a source embedding is needed. -/
private lemma embedReturn_step (N : MultiTapeTM k Bool S)
    (R : MultiTapeTM k Bool (S ⊕ Unit))
    (hleft : ∀ q inp work, R.tr (Sum.inl q) inp work =
      embedReturnAction (N.tr q inp work))
    (hidle : ∀ inp work, R.tr (Sum.inr ()) inp work =
      ⟨0, fun _ => (none, 0), none, some (Sum.inr ())⟩)
    (c : Cfg k Bool S x) :
    R.step (embedReturnCfg c) = embedReturnCfg (N.step c) := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => simp [embedReturnCfg, hs, hidle, Action.apply]
  | some q =>
    rw [show (embedReturnCfg c).state = some (Sum.inl q) by
      simp [embedReturnCfg, hs]]
    dsimp only
    have hin : (embedReturnCfg c).inputSymbol = c.inputSymbol := rfl
    have hw : (embedReturnCfg c).workTapeSymbols = c.workTapeSymbols := rfl
    rw [hin, hw, hleft]
    rfl

/-- The silent returning step executes the entire transported source
action, then encodes its successor as a live left state or return anchor. -/
private lemma embedSilentRet_step (ι : Fin m ↪ Fin k) (cap : Fin k)
    (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre out₀ : List Bool) (c : Cfg m Bool S x) (hc : c.state ≠ none) :
    (embedSilentRetTM ι cap M).step
        ((embedSilentCfg ι cap tapes heads pre out₀ c).mapState Sum.inl) =
      embedReturnCfg (embedSilentCfg ι cap tapes heads pre out₀ (M.step c)) := by
  have h := embedReturn_step (embedSilentTM ι cap M) (embedSilentRetTM ι cap M)
    (fun _ _ _ => rfl) (fun _ _ => rfl)
    (embedSilentCfg ι cap tapes heads pre out₀ c)
  rw [embedReturnCfg_live (embedSilentCfg ι cap tapes heads pre out₀ c) hc,
    embedSilent_step] at h
  exact h

/-- A live-step transport reaches the return anchor exactly at a positive
first halt, with all transported data intact.
**Proof sketch.** The initially live state and terminal halt imply positive
time. Induct over the strict live prefix, where the successor encoding is
ordinary left mapping. Execute the step from the last live configuration
separately; its halted successor encodes the return anchor. Earlier states
are left constructors, so none is the right anchor. -/
private lemma embedThroughHalt (M : MultiTapeTM m Bool S)
    (R : MultiTapeTM k Bool (S ⊕ Unit))
    (E : Cfg m Bool S x → Cfg k Bool S x)
    (hstate : ∀ d, (E d).state = d.state)
    (hstep : ∀ d, d.state ≠ none →
      R.step ((E d).mapState Sum.inl) = embedReturnCfg (E (M.step d)))
    (c : Cfg m Bool S x) (T : ℕ) (hc : c.state ≠ none)
    (hlive : ∀ t < T, (M.runFrom c t).state ≠ none)
    (hhalt : (M.runFrom c T).state = none) :
    (∀ t < T, R.runFrom ((E c).mapState Sum.inl) t =
      (E (M.runFrom c t)).mapState Sum.inl) ∧
    R.runFrom ((E c).mapState Sum.inl) T =
      { E (M.runFrom c T) with state := some (Sum.inr ()) } ∧
    ∀ t < T, (R.runFrom ((E c).mapState Sum.inl) t).state ≠
      some (Sum.inr ()) := by
  have hT : 0 < T := by
    by_contra hn
    have hz : T = 0 := by omega
    subst T
    exact hc (by simpa using hhalt)
  have hrun : ∀ t < T, R.runFrom ((E c).mapState Sum.inl) t =
      (E (M.runFrom c t)).mapState Sum.inl := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ t ih =>
      intro ht
      rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega),
        hstep _ (hlive t (by omega)), ← MultiTapeTM.runFrom_succ_eq_step']
      apply embedReturnCfg_live
      rw [hstate]
      exact hlive _ ht
  refine ⟨hrun, ?_, ?_⟩
  · have hlast : T - 1 + 1 = T := by omega
    calc
      R.runFrom ((E c).mapState Sum.inl) T =
          R.step (R.runFrom ((E c).mapState Sum.inl) (T - 1)) :=
        (congrArg (R.runFrom ((E c).mapState Sum.inl)) hlast).symm.trans
          MultiTapeTM.runFrom_succ_eq_step'
      _ = embedReturnCfg (E (M.runFrom c T)) := by
        rw [hrun _ (by omega), hstep _ (hlive _ (by omega)),
          ← MultiTapeTM.runFrom_succ_eq_step', hlast]
      _ = _ := by simp [embedReturnCfg, hstate, hhalt]
  · intro t ht
    rw [hrun t ht]
    simp only [Cfg.mapState, hstate]
    cases (M.runFrom c t).state <;> simp

/-- **R1′ through-halt contract, suppressing flavor** (spec, fill pending —
round-1 repair R1): if the source first halts at time `T`, the returning
embedding runs in `Sum.inl`-lockstep through every live time and, at `T`,
sits at the **live return anchor** over the completed transport — the
halting transition's emission recorded on `cap`, the source tape residue
preserved on the selected bank, the frame untouched — having visited the
anchor first exactly there. The start must be **live** (`hc` — round-2
blocker: an initially halted `c` at `T = 0` satisfies the other hypotheses
vacuously while the handover state projection would demand
`none = some (Sum.inr ())`; under `hlive` **and** `hhalt` together, `hc` is
equivalent to `0 < T` — the forward direction uses `hhalt`, the reverse
`hlive 0` (round-3 finding 1 sharpened the earlier `hhalt`-only phrasing).
The smallest case is the round-1 counterexample cured: a one-state source
that emits and halts on its first transition lands at time `1` in
`Sum.inr ()` with `pre ++ [b]` on the capture tape (the audit's S8 check).

**Proof sketch.** Live times: the `Sum.inl` branch applies the very core of
`Turing.embedSilentTM`, so `embedSilentTM_runFrom`'s one-step commutation
transports verbatim under `Cfg.mapState Sum.inl` (`Cfg.mapState_apply`).
At the halting step, the source action's tape and capture effects are those
of the closed flavor — `Turing.FinTM.bufferTape_append` records the final
emission — while the successor `Option.elim` lands in `Sum.inr ()` instead
of `none`; the anchor cannot occur earlier because live source states map
into `Sum.inl`. Fill obligations, named: the two `Option.elim` successor
equations; the through-halt step case; the first-visit projection. -/
theorem embedSilentRetTM_run (ι : Fin m ↪ Fin k) (cap : Fin k)
    (hcap : cap ∉ Set.range ι) (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre out₀ : List Bool) (c : Cfg m Bool S x) (T : ℕ)
    (hc : c.state ≠ none)
    (hlive : ∀ t < T, (M.runFrom c t).state ≠ none)
    (hhalt : (M.runFrom c T).state = none) :
    (∀ t < T,
      (embedSilentRetTM ι cap M).runFrom
          ((embedSilentCfg ι cap tapes heads pre out₀ c).mapState Sum.inl) t =
        (embedSilentCfg ι cap tapes heads pre out₀
          (M.runFrom c t)).mapState Sum.inl) ∧
    (embedSilentRetTM ι cap M).runFrom
        ((embedSilentCfg ι cap tapes heads pre out₀ c).mapState Sum.inl) T =
      { embedSilentCfg ι cap tapes heads pre out₀ (M.runFrom c T) with
          state := some (Sum.inr ()) } ∧
    ∀ t < T,
      ((embedSilentRetTM ι cap M).runFrom
          ((embedSilentCfg ι cap tapes heads pre out₀ c).mapState Sum.inl)
          t).state ≠ some (Sum.inr ()) := by
  exact embedThroughHalt M (embedSilentRetTM ι cap M)
    (embedSilentCfg ι cap tapes heads pre out₀) (fun _ => rfl)
    (embedSilentRet_step ι cap M tapes heads pre out₀) c T hc hlive hhalt

/-- The forwarding returning step preserves the complete source action,
including its final emission, and changes only the successor encoding. -/
private lemma embedEmitRet_step (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre : List Bool) (c : Cfg m Bool S x) (hc : c.state ≠ none) :
    (embedEmitRetTM ι M).step ((embedEmitCfg ι tapes heads pre c).mapState Sum.inl) =
      embedReturnCfg (embedEmitCfg ι tapes heads pre (M.step c)) := by
  have h := embedReturn_step (embedEmitTM ι M) (embedEmitRetTM ι M)
    (fun _ _ _ => rfl) (fun _ _ => rfl) (embedEmitCfg ι tapes heads pre c)
  rw [embedReturnCfg_live (embedEmitCfg ι tapes heads pre c) hc, embedEmit_step] at h
  exact h

/-- **R1′ through-halt contract, forwarding flavor** (spec, fill pending —
round-1 repair R1): as `Turing.embedSilentRetTM_run` with the final
emission forwarded to the physical output (`pre ++ (M.runFrom c T).output`
at the anchor).

**Proof sketch.** As `embedSilentRetTM_run`, with the forwarding core: live
times transport under `Cfg.mapState Sum.inl` by `embedEmitTM_runFrom`'s
one-step commutation, the halting step applies the closed forwarding core's
tape and output effects (the final emission appended to the physical
output) with the successor `Option.elim` landing in `Sum.inr ()`, and the
first-visit clause projects from the `Sum.inl` lockstep. Fill obligations,
named: the successor equations; the through-halt step case; the
first-visit projection. -/
theorem embedEmitRetTM_run (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre : List Bool) (c : Cfg m Bool S x) (T : ℕ)
    (hc : c.state ≠ none)
    (hlive : ∀ t < T, (M.runFrom c t).state ≠ none)
    (hhalt : (M.runFrom c T).state = none) :
    (∀ t < T,
      (embedEmitRetTM ι M).runFrom
          ((embedEmitCfg ι tapes heads pre c).mapState Sum.inl) t =
        (embedEmitCfg ι tapes heads pre (M.runFrom c t)).mapState Sum.inl) ∧
    (embedEmitRetTM ι M).runFrom
        ((embedEmitCfg ι tapes heads pre c).mapState Sum.inl) T =
      { embedEmitCfg ι tapes heads pre (M.runFrom c T) with
          state := some (Sum.inr ()) } ∧
    ∀ t < T,
      ((embedEmitRetTM ι M).runFrom
          ((embedEmitCfg ι tapes heads pre c).mapState Sum.inl) t).state ≠
        some (Sum.inr ()) := by
  exact embedThroughHalt M (embedEmitRetTM ι M)
    (embedEmitCfg ι tapes heads pre) (fun _ => rfl)
    (embedEmitRet_step ι M tapes heads pre) c T hc hlive hhalt

/-- Direct host comparison preserves every visited-head set, from any
initial configuration and for every finite horizon.
**Proof sketch.** Initially halted configurations stay halted on both
sides. From a live start, iterate the direct step comparison under the
return encoding, whose head positions are unchanged. Equality of the
head trajectories gives equality of their finite images. This uses no
termination hypothesis, source simulation, or capture-tape separation. -/
private lemma embedReturn_visited (N : MultiTapeTM k Bool S)
    (R : MultiTapeTM k Bool (S ⊕ Unit))
    (hleft : ∀ q inp work, R.tr (Sum.inl q) inp work =
      embedReturnAction (N.tr q inp work))
    (hidle : ∀ inp work, R.tr (Sum.inr ()) inp work =
      ⟨0, fun _ => (none, 0), none, some (Sum.inr ())⟩)
    (c : Cfg k Bool S x) (t : ℕ) (j : Fin k) :
    R.visitedByTapeHead (c.mapState Sum.inl) t j = N.visitedByTapeHead c t j := by
  unfold MultiTapeTM.visitedByTapeHead
  congr 1
  funext u
  by_cases hc : c.state = none
  · rw [R.runFrom_of_halt _ (by simp [Cfg.mapState, hc]), N.runFrom_of_halt _ hc]
    rfl
  · have hrun := MultiTapeTM.runFrom_comm_of_step embedReturnCfg
      (embedReturn_step N R hleft hidle) c u
    rw [embedReturnCfg_live c hc] at hrun
    exact congrArg (fun d => d.workTapePos j) hrun

/-- **R1′ space, suppressing flavor** (spec, fill pending — round-1 repair
R1): at every time and on every tape, the returning embedding's visited set
from the `Sum.inl`-mapped seam equals the closed embedding's from the plain
seam — the trajectories coincide through the halt, and afterwards one idles
at the live anchor while the other sits halted, both stationary.

**Proof sketch.** For `t` up to the first source halt, both machines apply
identical tape actions (`embedSilentRetTM_run`'s lockstep and the halting
step's shared core); beyond it, the anchor's idle action and the halted
absorption are both stationary, freezing both visited sets.

**Fill appendix.** The direct host comparison `embedReturn_visited`
handles initially halted and live starts separately. It uses neither
through-halt contract nor a capture-separation hypothesis. -/
theorem embedSilentRetTM_visitedByTapeHead (ι : Fin m ↪ Fin k) (cap : Fin k)
    (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre out₀ : List Bool) (c : Cfg m Bool S x) (t : ℕ) (j : Fin k) :
    (embedSilentRetTM ι cap M).visitedByTapeHead
        ((embedSilentCfg ι cap tapes heads pre out₀ c).mapState Sum.inl) t j =
      (embedSilentTM ι cap M).visitedByTapeHead
        (embedSilentCfg ι cap tapes heads pre out₀ c) t j := by
  exact embedReturn_visited (embedSilentTM ι cap M) (embedSilentRetTM ι cap M)
    (fun _ _ _ => rfl) (fun _ _ => rfl)
    (embedSilentCfg ι cap tapes heads pre out₀ c) t j

/-- **R1′ space, forwarding flavor** (spec, fill pending — round-1 repair
R1): the forwarding analogue of
`Turing.embedSilentRetTM_visitedByTapeHead`.

**Proof sketch.** As the suppressing flavor: identical tape actions through
the first source halt, then the live idle and the halted absorption are
both stationary, freezing both visited sets — the trajectories coincide at
every time. -/
theorem embedEmitRetTM_visitedByTapeHead (ι : Fin m ↪ Fin k)
    (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre : List Bool) (c : Cfg m Bool S x) (t : ℕ) (j : Fin k) :
    (embedEmitRetTM ι M).visitedByTapeHead
        ((embedEmitCfg ι tapes heads pre c).mapState Sum.inl) t j =
      (embedEmitTM ι M).visitedByTapeHead
        (embedEmitCfg ι tapes heads pre c) t j := by
  exact embedReturn_visited (embedEmitTM ι M) (embedEmitRetTM ι M)
    (fun _ _ _ => rfl) (fun _ _ => rfl) (embedEmitCfg ι tapes heads pre c) t j


/-! ### Selected-tape exports (§13 Z1 rider, decision D-R1)

The retrofit inventories (`audits/retrofit-inventory/`) found, three times
independently, that no old-code R1 consumer can be proved from this file's
public surface: the frame lemmas cover only unselected tapes, and
`embedSlot_selected` is private. These four projections export the
selected-tape fields of the two configuration transports. They are
skeleton-time proofs (statement-phase additions flagged for the A-S1
audit): each is definitional at `embedSlot_selected`. -/

/-- The silent transport holds the source's tape `i` on host tape `ι i`. -/
theorem embedSilentCfg_selected_tape (ι : Fin m ↪ Fin k) (cap : Fin k)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre out₀ : List Bool) (c : Cfg m Bool S x) (i : Fin m) :
    (embedSilentCfg ι cap tapes heads pre out₀ c).workTapes (ι i) =
      c.workTapes i := by
  simp [embedSilentCfg, embedSlot_selected]

/-- The silent transport holds the source's tape-`i` head on host tape
`ι i`. -/
theorem embedSilentCfg_selected_pos (ι : Fin m ↪ Fin k) (cap : Fin k)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre out₀ : List Bool) (c : Cfg m Bool S x) (i : Fin m) :
    (embedSilentCfg ι cap tapes heads pre out₀ c).workTapePos (ι i) =
      c.workTapePos i := by
  simp [embedSilentCfg, embedSlot_selected]

/-- The forwarding transport holds the source's tape `i` on host tape
`ι i`. -/
theorem embedEmitCfg_selected_tape (ι : Fin m ↪ Fin k)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre : List Bool) (c : Cfg m Bool S x) (i : Fin m) :
    (embedEmitCfg ι tapes heads pre c).workTapes (ι i) = c.workTapes i := by
  simp [embedEmitCfg, embedSlot_selected]

/-- The forwarding transport holds the source's tape-`i` head on host tape
`ι i`. -/
theorem embedEmitCfg_selected_pos (ι : Fin m ↪ Fin k)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre : List Bool) (c : Cfg m Bool S x) (i : Fin m) :
    (embedEmitCfg ι tapes heads pre c).workTapePos (ι i) = c.workTapePos i := by
  simp [embedEmitCfg, embedSlot_selected]

end Turing
```
