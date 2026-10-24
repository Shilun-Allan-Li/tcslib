# Review: megafill C's C1 brief draft and cover draft (review sub-agent, 2026-10-24)

**Verdict: issue after the listed edits.** No blocker and no major. The C1 brief is complete
against the drafting brief's §5 and the model, its frozen statement is byte-identical to the
source, and its route is sound: the review proves the target end to end from published lemmas
under a 21-definition seal (F1). Nine minors are text fixes (`suggested-fix.diff`, applies with
`git apply` at `6e8db28f`) or issue-time steps; the cover needs the user's rulings Q-B1, Q-U1 and
Q-M2 before it can be issued, and its self-referential SHA-256 row removed (F8).

Scope: `campaign/fills/c1/drafts/c1-fill-replaycanon.DRAFT.md` and its pre-ship
`preship-77f1eb4f/`; `campaign/fills/megafill/drafts/megafill-C.DRAFT.md` and
`megafill-C-env-77f1eb4f/`; the placeholders of `s13d-fill-g4-cont4.DRAFT.md` and how the cover
treats it; Q-M1 and Q-M2. Repository at `6e8db28f23386c567466dd6a7357d8ec35d1cde8` (PR #157's
merge), read-only. Drafting base `77f1eb4fb74deb7a1ac7bae7bc4e98d5d0f9a532`: its Lean content
equals the tip's and `906a9d7b`'s (`git diff --name-only … -- '*.lean'` empty both ways). Every
Lean run: `leanelab.sh` on the review worktree against `oleans-lslsk`, one at a time. The screen
ran once, niced, under the screen lock.

## Checks

| # | Check | Result | Evidence |
|---|---|---|---|
| 1 | Completeness against §5 and `c1-fill-core-cont2.md`; the frozen statement | complete; statement and docstring identical to `NDCodeSimulator.lean:80–99`; regions (home 79, body 99, status paragraph at the end of 95) right; weaker points F2–F6 | `out/01-completeness.md`, `out/01a-frozen-statement.txt` |
| 2 | Every cited declaration exists, is public, has the route's signature | the draft's probe re-run: identical output (102, 0 errors); 14 cited names it lacks all resolve (`C1RCImportProbeX`, 125 checks, 0 errors); no `Primrec.list_take` at the pin (confirmed) | `out/02-cited-declarations.txt`, `probe/C1RCImportProbe*.out` |
| 3 | The route: invariant, layouts, `Primrec` feasibility, seal and controls | sound; the review proves `rc_g_serialize`, `rc_g_primrec` and the target (standard three axioms) under a 21-definition seal; the route probe's seal misses `optBoolBits`, `optStateBits` (F3); route probe, controls (15/15) and definitions probe reproduce; the brief states the correctness lemma (`rc_g_serialize`) and does not rest on `#eval` | `out/03-route-soundness.md`, `probe/C1RCReviewFeasibility.*`, `probe/C1RCReviewSealControlX.*`, `probe/C1RCReviewWalk.*`, `probe/C1RCRouteProbeWalk.*` |
| 4 | Order list, roots, base sorries | identical to the pre-ship's (119, 41, 31) at the base and at the tip; the queue's union is 41 roots; both consumers' only admission source is the target | `out/04-order-roots-sorries.txt`, `out/fillinputs*/`, `probe/C1RCReviewSorrySources.*` |
| 5 | Duplication population and screen | population complete for the route (every cited file and the known hazards; searched the tree and #156/#135); the screen re-run is byte-identical to the screen base (541, 173, 86,076; no pair on the owned file); F7 | `out/05-duplication.md`, `out/05-screen.*` |
| 6 | The owned file elaborates with exactly the target's sorry | one warning, `96:8`; blob `e2cdab7b…` | `out/06-elab-owned-file.txt`, `out/06-elab-NDCodeSimulator.raw` |
| 7 | The cover against A, B, the addendum and §7 | complete; F8, F9, F10; Q-M1 and Q-M2 below | `out/07-cover.md` |
| 8 | Placeholders and hashes | every hash resolves and means what the text says; one unfillable placeholder (F8); three G4 issue-time items missing from the report's list (F11) | `out/08-placeholders-hashes.md` |
| 9 | Text: 100-column reflow; public-facing Lean text | only titles and table rows exceed 100; the prescribed docstrings are public-facing; `rc_widen` lacks one (F5) | `out/09-text.md` |

## Findings

**F1 (note) — the review proves the target.** `probe/C1RCReviewFeasibility.lean` (344 lines,
about 300 of Lean) takes the brief's recommended definitions (renamed `rvc_`) and proves the skip,
the generalised rounds, the key list's length `27 (n + 1)`, the table identity, the header,
`rvc_g_serialize`, `rvc_g_primrec` (by exactly the brief's decomposition), and `rvc_target`, the
target's statement verbatim, by the brief's composition. 0 diagnostics; all on `[propext,
Classical.choice, Quot.sound]`. Sealed over 21 TCSlib definitions (the route probe's 14, the
brief's five, `optBoolBits`, `optStateBits`); the 7 added ones have controls that close unsealed
and fail sealed (`C1RCReviewSealControlX`); a constant walk finds every reached TCSlib definition
sealed; the inspection table (`C1RCReviewFeasibility.inspection.tsv`, 106 arguments) has only
theorems, hypotheses and own definitions. The size estimate (350–550 lines) and the 3-hour budget
are generous. *Decision D1 below.*

**F2 (minor) — the import probe does not check every cited name.** The brief says the probe's
"102 checks of 102 names" are "every declaration this brief cites" (150, 312). Unchecked:
`Turing.EffectiveNDMachineCode`, `exists_effectiveNDMachineCode`, `CodeFormat.exists_canonizer`,
`CodeFormat.primrec_scan`, `FinTM.exists_comp_on_image`, `FinTM.ComputesInTime`,
`MultiTapeTM.ComputesInTimeAndSpace`, `exists_ndInterpreterCore`, `exists_timed_universal_NDTM`,
`Primrec.nat_sub`, `Fin.fin_one_eq_zero`, `Function.iterate_succ_apply`, `List.append_assoc`,
`Nat.bits`. All resolve (out/02). **Fix (in the diff):** the probe extended to 123 checks of 123
names (these, less the universal NDTM, which needs `NTimeHierarchy` and stays in the axiom probe;
plus the seal's two definitions and the six lemmas F5's pitfalls name), run at the base: 0 errors,
0 warnings (`probe/C1RCImportProbeIssue.out`); the brief's count and paragraph, and a README note.

**F3 (minor) — two reached definitions are not sealed.** The route probe reaches `optBoolBits` and
`optStateBits` inside `actionBitsK_eq` (`probe/C1RCRouteProbeWalk.out`) but does not seal them, and
the brief's "at least" list for the fill's seal (rule 10) omits them. Nothing closes through them
(the review's 21-definition seal holds). **Fix (diff):** name both in rule 10's list and in the
pre-ship paragraph.

**F4 (minor) — rule 6 allows a Mathlib import.** "A Mathlib import only if a needed lemma requires
it" contradicts the frozen imports (186–187), and in a megafill a new Mathlib root is outside the
shared cache (41 roots fetched once). The review's proof needs no import. **Fix (diff):** no
import of any kind; a lemma that seems to need one is an escalation.

**F5 (minor) — pitfalls and a docstring.** Three pitfalls the review met: `codeReadUnary_append`
wants `false :: xs` (rewrite `List.singleton_append` after `unaryFin_eq`, `List.append_assoc`);
`have h : Primrec fun a => (o a).casesOn …` fails to elaborate (let Lean infer the composite,
`Primrec.to₂`, then `of_eq` by `rintro`/`unfold`/`rcases`/`rfl`); core definitions out of `rw`
(`Function.iterate_zero_apply`, not a rewrite that unfolds `id`), with the key-list length
lemmas. The recommended `rc_widen` has no docstring though every new declaration needs one.
**Fix (diff).**

**F6 (minor) — banner and delivery text.** The banner carries "(the cover's proposal)" and lacks
the model's "then deliver this item's zip, partial if need be, and start the next item"; "If Lean
never runs" lacks "deliver the environment report only"; the zip's shared-log list (65–66) names
fewer logs than the cover (55–56); the issue-time comment omits the move to `briefs/`, staging,
and the banner's parts. **Fix (diff).**

**F7 (note) — duplication population.** Complete for what the route proves: every cited file and
the known hazards; no private copy of a record skip, lockstep rounds, widening, replay-table
identity, `workReadsK` snoc lemma or running maximum exists in the tree or on #156's or #135's
heads. The re-run is byte-identical to the base (out/05). Optional: add
`Uncomputability/Computable.lean` (`Computes.exists_computesFunInTime`, a 6-line length-indexed
`Finset.univ.sup` weakening, the idiom nearest to the composition's bound) at no cost;
`UniversalK`'s `ss_lengthBound` is the same idiom. `Deterministic.lean` (home of the sealed-only
`MultiTapeTM.ComputesInTimeAndSpace`) needs no screening.

**F8 (minor) — the cover lists its own SHA-256.** Line 37 ("this cover | ⟨…⟩") cannot be filled: a
file cannot contain its own hash. A and B take every hash from the dispatch message. **Fix
(diff):** the cover's own from the dispatch message, the item briefs' in the table.

**F9 (minor) — cross-item effects at issue are not stated.** (a) Under Q-B1 (A) the harvest PR
re-points `NDCodeSimulator` (the report's recommendation): C1's blob check (`e2cdab7b…`) would
fail at the fill's first step, and its lines (79, 95, 96, 99), counts (2,325; 22 private), order
list, screen population (which should gain the new module) and screen base change. (b) #156's head
moved after drafting (`0e5f210b`, 2026-10-24 04:53 UTC, gate 69's major): it now also edits
`CodeSimulator` (B5a's owned file, a private proof), `Build/StepBlock` (in C1's population),
`Build/WindowRun`, `Build/OracleSim`, `SpaceComplexity/Inclusions`, besides `Build/Seam` (in
G4's population); no import changes. C1's citations are unaffected, but C1's and G4's screen bases
and B5a's pre-ship change if #156 merges first; C1's in-flight note ("#156, `Build/Seam`") is stale.
**Fix (diff):** both issue-time comments (C1, cover) and the in-flight note.

**F10 (minor) — dropping an item.** "Removed from the queue at issue, and the queue renumbered"
(29–30) is safe (no item depends on another; the 41-root union and every other item's base and
order list are unchanged by a drop), but the dropped item is named in eight places of the cover
and in C1's in-flight sentence. **Fix (diff):** "this cover is issued without it (every mention
removed, the queue and the remaining banners renumbered)".

**F11 (minor) — G4's issue-time items.** Besides the placeholders the report lists, G4's draft has
three stale or unlisted issue-time items: "95 modules" (551; 96 at `6e761018` and at the drafting
base, with `Build/InputRewind`), "33 WARN over 39 files" (573; 40 files at `6e761018`), and the
placeholder ⟨the other modules' sorries …⟩ (583–584; at the base: `CodeSimulator`'s
`exists_uniformSimulator`, `NDCodeSimulator`'s `exists_replayCanonizer`, `UniversalK`'s two). Its
comment still describes the `97299639` pre-ship (30 sorries). G4's lists at the drafting base
re-derived: 96, 40 roots, 27 sorries (`out/fillinputs-g4/`). **Fix (diff):** the two numbers and
the comment.

## Q-M1 (the queue order): keep C1, B5a, U2, G4

C1 first: the review's complete proof makes it near-certain inside its slot, and it makes the
interpreter core and the universal NDTM admission-free (their only admission source is the target).
B5a second while the session is young, if Q-B1 is settled in the shared base; U2 third if Q-U1's
API PR is in; G4 last with "the rest", since its open-ended checkpoint chain is the only item that
benefits from unbounded time. (U2 before B5a would deliver more if the session died early, but
megafills A and B both ran to the end.) Full reasoning: `out/07-cover.md`.

## Q-M2 (B5a's 87-minute screen against its 5-hour budget)

**Recommendation: the drafting agent's option, made precise** (in the diff, still marked ⟨Q-M2⟩):
B5a's budget counts up to the start of its after run; B5a writes its last checkpoint zip first,
starts the after run at the latest when the budget ends, writes `REPORT.md` while it runs, and the
next item's branch is created only after the run has ended and the zip is written. Inside the
budget the two runs would take about 174 of 300 minutes; a 6-hour inclusive budget still leaves
about 4.5 hours of proof time. Alternative (more efficient, the user's call): the after run on a
separate worktree (the screen reads every input before comparing), the next item started at once,
and B5a's zip completed when the run ends, as the one permitted return to an earlier item.

## Decisions for the user

- **D1 (F1): what to do with the review's complete proof.** (a) Issue C1 as drafted and keep the
  proof as audit evidence (3 hours); (b) **recommended:** supply it as a verified input (the
  precedent: R cont2's overlay of the review's verified privates), C1 porting it into house style
  with the full protocol (seal, screens, probes), about 2 hours, the freed hour to B5a; (c) land
  it as a maintainer PR with a fill gate and drop C1 from megafill C.
- **Q-M1:** keep the drafted order (above).
- **Q-M2:** the precise budget rule (above), or the worktree alternative.
- **Q-B1 and Q-U1** (other reviewers' scope) decide whether B5a and U2 are in the queue; under
  Q-B1 (A), C1's pre-ship is regenerated after the harvest PR merges (F9).
- **#156:** whether it merges before issue decides which pre-ships move (F9).

## Files

- `REVIEW.md`, `suggested-fix.diff` (5 files: the C1 draft, its import probe and README, the
  cover, the G4 draft; 105 insertions, 35 deletions; `git apply --check` passes at `6e8db28f`).
- `out/`: one record per check (01–09), the reproduced lists (`fillinputs/`, `fillinputs-tip/`,
  `fillinputs-g4/`, `union-roots.txt`), the screen (`05-screen.*`), raw greps.
- `probe/`: the draft's four probes re-run (`.lean` copies, `.out`), the extended import probes
  (`C1RCImportProbeX`, `C1RCImportProbeIssue`), the review's proof (`C1RCReviewFeasibility`), its
  controls, walk, inspection, and the consumers' sorry-source walk.
- `scripts/`: `frozen_compare.py`, `cited_spans.py`, `rwargs.py`, `run-screen.sh`, and the three
  asserted edit scripts behind the diff (`edit_c1.py`, `edit_cover.py`, `edit_g4.py`; three small
  asserted rewraps and the README note were run inline). The diff is the authority.
