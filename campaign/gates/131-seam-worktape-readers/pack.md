# Gate 131 — the seam right transition and the work-tape equation's home

Codex audit, PR [#253](https://github.com/Shilun-Allan-Li/tcslib/pull/253).
**Not yet clear to merge: #253 — external audit open.** Exact Lean: `1d88037a8b2a0cd1858245a979ced7dea4a7172c`,
branch `codex/ab34-seam-and-worktape-readers`, target `complexity/arora-barak-ch3-4`.
Baseline Lean: `9b5dcf46408db681bcbc721930ef2203fa6bc47d` (MAC8). Records and exchange pins and bundle SHA-256 are
given with the dispatch prompt. Seyoon dispatches, decides design/debt and merges.

## Scope and contracts

Seyoon approved the non-simp right transition, then explicitly approved moving
the existing optional-write equation beside its definition, grouped in the
same prerequisite PR. He separately approved exactly one import of CfgFacts
in Seam, for the existing private right-step proof. Only three owner files
change; no machine definition, existing formal statement, attribute, theorem
name or mathematical fill is changed.

- `Turing.seamCompTM_tr_inr`, new, in Seam: for a right summand control
  `Sum.inr q` and arbitrary input/work reads, the action of the seam is
  the second machine's action at q with its optional successor mapped into
  the right summand. Movement, write and output are unchanged. It does not
  assert a left table row, a dispatch, a whole step or a bound.
- `Turing.Action.apply_workTapes`, moved from Simulation to Configuration:
  applying an action on tape i updates the old work tape at its head to the
  write option's value, using the old scanned symbol when there is no write.
  Outer none preserves content; some none erases. The name, statement and
  proof text are exact, and there is one active owner. Adjacent owner references
  and the historical docstring parenthetical change.
- Existing private `seamComp_step_right` keeps its exact header. For a halted
  source, use step-of-halt on both sides. For a live state, the new table equation
  and Cfg.mapState_apply identify the two steps after matching input and work
  reads. The sole new import supplies Cfg.inputSymbol_congr. A proof sketch is
  the only edit after the complete 403-module replay.

Public freeze: Configuration gains the moved name (21→22), Simulation loses it
there (65→64), Seam adds one reader (26→27); private counts are unchanged and
only the named right-step proof changes. These are implementation readers,
not separately stated textbook results. Check zero work tapes, halt/live
successor, arbitrary displaced tape heads, and no-write versus explicit erase.

## Executed checks and limits

- Actual full 403-module replay on `d26b7340265ff1318d44838aaca2cd660f8528f3` after the approved import,
  from a complete MAC8 clone: all pass, zero static mismatches,
  59 inherited direct admissions in that replay population. Whole
  input and output maps each contain 895 .olean objects. An earlier interrupted
  403 attempt is invalid and not reused.
- Exact final source adds only one documentation comment to that already replayed
  Lean tree. A separate actual Seam compilation on a complete clone of that
  replay passes; the other 894 objects are byte-identical. The current clean
  prospective merge has the exact final Lean tree. The three complete maps,
  module/source logs and exact comment-only diff were rehashed. A strict post-run
  static recheck accounts for every one of the 403 ordered rows; the checker
  rejects deliberately missing, duplicate and mismatched rows. No fresh full
  403 execution at the comment-only source is claimed.
- The early three-owner native and producer checks are recorded at their actual
  pre-import source. The moved theorem's type matches after normalization of
  generated universe and binder names; literal compiled expression identity
  is not claimed. The final actual snapshot independently confirms both public
  owners and non-simp/non-unfold flags. The new row uses Quot.sound; the
  moved theorem's standard axiom set is unchanged. No new axiom or admission.
- The moved reader has zero ordinary foreign definitions in the new owner, so
  no vacuous seal is claimed. Its explicit reads of Action.apply and
  Cfg.workTapeSymbols are now in their home. The full new reader proof passes
  with Action.mapState opaque, using its four public field equations and the
  same-file table. The two paired controls pass unsealed and fail at their
  intended sealed goals; a fresh run in the final import context is retained.
- The exact right-step proof passed a separate complete target guard over six
  foreign ordinary definitions, with the active Action.apply unfold entry
  removed; twelve matched point/equation controls passed unsealed and failed
  sealed at the intended goals. The formal header and other selected metadata
  stayed exact; the existing Classical.choice dependency is added to its
  closure. The final comment changes no proof tokens. These checks are for
  the selected roots; they do not certify every preceding proof or imply
  equality of all downstream axiom closures.

## Duplication and source QA

The complete bounded preflight captured 589 named refs/392 source heads and
18 then-open PRs, including prepared and delivery source. It contains 8,625
distinct source objects, 55,933 uncapped raw hit lines, and 1,178 complete
candidate chunks with occurrence and disposition records. The current
supplement separately fetches and searches all 16
currently open PR heads and preserves their deltas. Repeated snapshots of
the same declaration and raw prepared/report fragments are not additional
live definitions. The narrower literal-shape results are the two canonical
equations; other candidates have full configuration, restricted tape,
left/exit, release, run or trajectory contracts. Source search is bounded
candidate enumeration and inspection, not a global semantic absence proof.

The old inline right-table reduction in seamComp_step_right is repointed.
The release and left-step contracts run different machines/guards and are
not covered by the selected right row. The current phase-host dispatch already
uses Action.apply_workTapes. Older unrelated definitions and proofs are not
newly certified or acknowledged by this gate. No retirement is recorded before
Seyoon merges; no family-wide debt acceptance is implied.

The complete 56-file comparison starts from an actual 53-file BASE screen.
It checks the unchanged 2,872 row inputs and considers all 412,794 ordered
pairs incident to the 71 added BASE rows, with 7,440 actual tilings. This
gives all 2,534 BASE56 pairs. At the repaired source it reuses 2,941 identical
rows and considers all 17,652 ordered pairs incident to the three changed,
moved or added rows, with 252 actual tilings. HEAD56 has 2,522 pairs,
0 new, 12 gone, no changed scores. All 2,944 final row inputs and pair scores
are exact after the comment, so there was no new affected tiling. Source
coverage, raw rows and comparisons are supplied; no new full quadratic
execution is claimed. Ordinary style has the same 11
inherited finding identities after adding the sketch. Campaign lint has
0 FAIL and 73 WARN over 94 TuringMachine files. The sizes are reported in
the raw lint; they are not a split or a hygiene exemption.

## Auditor remit

Read the bundled standards, exact owner files, source patch and all relevant
evidence. Independently restate both selected equations, assess at least three
boundary cases, and review the home/namespace/attribute/type evidence. Check
the single approved import, exact right-step proof, seals and controls, and
actual-versus-reused replay/copy accounting. Inspect the closest candidates
and state any evidence or governance gaps at the template severity. The
Fresh/Prepared consumer proposals are included as motivation, not adopted
source or mathematical fills. The DATA-CARRIER and RECOVERY note retain
the raw inputs, outputs and failed/interrupted attempts.

Use the findings table and verdict counts from the template. **Deliver your
findings as a downloadable file named `gate131-seam-worktape-readers-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste
its content in your reply. Do not push or edit branches, dispatch other agents,
accept debt or merge.
