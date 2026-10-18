# External audit pack — B7 fill gate: deterministic logspace (12 targets, five deliveries)

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md` §4e, cluster B7). B7 fills
the deterministic-logspace part of [AB09] §4.3 and the contracts it rests on, across five files
in `TCSlib/Complexity/SpaceComplexity/Logspace/`. The statements were audited true at two gates:
- **P4.4** (`audits/ch4-p44-findings.md`, `-resolutions.md` and `-resolutions-addendum.md`, the
  binding route changes): the five chapter statements;
- **P4.4b** (`audits/b7-statements-findings.md`, `-resolutions.md`): the seven contracts the
  route needs, because the received `LogProg` layer had no oracle-served input and no random
  access to a non-unary input.

| # | Target | Book | File |
|---|---|---|---|
| 1 | `Complexity.LogProg.OIS.run` | the oracle-input simulator, [AB09, Fig. 4.3] | `PreimageHost` |
| 2 | `Complexity.LogProg.OIS.compile_decides` | its compilation | `PreimageHost` |
| 3 | `Complexity.mem_LOGSPACE_preimage` (N2) | Lemma 4.17's proof | `PreimageHost` |
| 4 | `Complexity.mem_LOGSPACE_of_logspaceReducible` (T3) | Lemma 4.17(2) | `Reductions` |
| 5 | `Complexity.NL_eq_LOGSPACE_of_nlComplete_mem_LOGSPACE` (T5) | after Lemma 4.17 | `Reductions` |
| 6 | `Complexity.LogProg.readIn_run` | reading a binary-indexed input bit | `InputAccess` |
| 7 | `Complexity.implicitlyLogspaceComputable_id` (N1) | input random access in `L` | `InputAccess` |
| 8 | `Complexity.implicitlyLogspaceComputable_dropIdx` (N3) | Lemma 4.17's proof | `QueryReshape` |
| 9 | `Complexity.ImplicitlyLogspaceComputable.compQ` (N4) | Lemma 4.17's proof | `QueryReshape` |
| 10 | `Complexity.ImplicitlyLogspaceComputable.comp` (T1) | Definition 4.16, Lemma 4.17 | `Reductions` |
| 11 | `Complexity.LogspaceReducible.trans` | Lemma 4.17(1) | `Reductions` |
| 12 | `Complexity.multLang_mem_LOGSPACE` (T11) | Example 4.7 | `Mult` |

Five deliveries, each integrated by `git am -3` with Codex authorship:

| Delivery | Brief | Integrated | Targets |
|---|---|---|---|
| 1 | `briefs/ch34-b7.md` (ancestor `315571be`) | `b0738c89`, PR #34 | 1–6 |
| continuation 1 | `briefs/ch34-b7-cont.md` | `9ad832e7`, PR #39 | 7, with three shared exports |
| continuation 2 | `briefs/ch34-b7-cont2.md` | `55166461`, PR #50 | 8, with six shared exports |
| continuation 3 | `briefs/ch34-b7-cont3.md` | `9ce4c35a`, PR from `integrate/fills-4` | 9–11 |
| multiplication | `briefs/ch34-b7-mult.md` | `f521bfbc`, PR from `integrate/fills-4` | 12 |

The last two ran **in parallel** on disjoint files (user decision, 2026-10-11), so they were
first combined at integration. The maintainer replayed the combined tree.

**Every proof is kernel-checked**; the replay and axiom evidence is below. All twelve targets now
print within `[propext, Classical.choice, Quot.sound]`. Fill gates close on zero blockers and
zero majors (`workflow.md` §4), and the duplication rule (`audits/TEMPLATE.md`, failure mode 5)
is in force. The standards are attached.

## What changed (verify)

| Class | Declarations |
|---|---|
| **Target bodies, `sorry` → proof** | all twelve |
| **Flagged public exports** (`InputAccess`, brief rule 3) | `pairEncode_getD`, `LogProg.inputLength_loop`, `LogProg.alignedPair_loop` (continuation 1); `LogProg.register_update_le`, `registerCopy_loop`, `registerScale_loop`, `canonicalTail_loop`, `boundedDecode_loop`, `indexedSeek_loop` (continuation 2) |
| **Privates** | `InputAccess` 58, `PreimageHost` 16, `QueryReshape` 112, `Reductions` 1, `Mult` 62 |
| **Imports** | unchanged in all five files |
| **Landed definitions** (frozen) | `RdPh`, `readTr`, `OIS.*`, `inputBitLang`, `inputLenLang`, `dropIdx`, `compQ`, `multLang` |
| **Docstrings** | flagged appendices where a route was refined; status tags and module labels now "proved" |

## Brief for the auditor

1. **Freeze.** Re-establish it from the attached bases (at `315571be`), the head and the
   cumulative patch (`audits/evidence/b7/fill-gate/`; computed at `b0e922ab`, and the files are
   unchanged at the final head):
   - every statement is unchanged, and so is every landed definition;
   - only the twelve target bodies changed;
   - the only new publics are the nine flagged exports;
   - the imports are unchanged.
2. **Routes** (P4.4 resolutions with the addendum; the briefs' routes 1–12).
   - **The oracle-input simulator** (1–2): its oracle laws are required only on genuine queries
     (P4.4b note 7), and the scalar radius `B` accommodates a non-monotone `sb` (note 8).
   - **N1** (7): the query index is compared with the counter while streaming and never copied
     into workspace; a non-canonical index is rejected (note 5).
   - **N3** (8): `dropIdx` decodes pair shape only; the dropped and retained payloads stay
     arbitrary words (note 10). The tail is rejected when over-wide **before** the query value
     is decoded.
   - **N4** (9): overflow is handled with `compQ_length_le` (note 11). The inner field `b` is
     validated canonical **without decoding its value**, since that value may be exponentially
     large. `F = |f x|` is found by a capped lifted-length search, with the cap itself when every
     query succeeds and `F = 0` with no query when the cap is `0`.
   - **10–11** are the prescribed corollaries.
   - **MULT** (12): the column/carry invariant is **proved**, not assumed (note 12; the statement
     probe only assumed it).
3. **The audit contracts** (P4.4 findings, verbatim in the briefs): T1 (composition in logspace,
   malformed and oversized queries rejected within the bound, each simulation halting), T11
   (three canonical fields, every relevant output bit compared, excessive result length
   rejected, no final carry, zero operands with no extra hypothesis), Q2 (the overflow test
   before storing the index) and Q8 (zero-padded result bits; "simultaneous end" not assumed).
   Confirm each is discharged as its delivery's report says.
4. **The nine exports.** Rule on whether each is genuinely shared (used by more than one target
   or delivery) and correctly stated.
5. **Duplication** (failure mode 5). The 22-file B7 population screen runs from the brief base
   (192 declarations, 53 pairs) to 416 declarations and 79 pairs at the head (`audits/logs/b7-fills-45-screen-combined.txt`). Every
   new pair is in-file and below 90%, with one exception: the cross-batch pair below.
   - **The cross-batch pair:** `Mult.lean::mult_addresses` reproduces
     `QueryReshape.lean::comp_suffix_address` at 55%, found only at integration (each batch's own
     screen could not see the other's work). Both are short applications of the public
     `pairEncode_getD` lookup law to different nested layouts (`pairEncode a (pairEncode b c)`
     against `pairEncode (pairEncode x b) tail`). The maintainer classifies this as idiom: the
     shared argument is already public. Rule on it.
   - The highest in-file pairs: `drop_u_prepare` ← `drop_lookup_prepare` 89% (continuation 2;
     about 310 characters of tactic idiom around the shared `drop_copy_run`), and
     `multRow_cons` ↔ `multRows_cons` 80–81% (two short recurrence lemmas).
   - The hazards the briefs named: every `arm_decides_poly` assembly against
     `UnaryLogspace::ltLang_mem`; reachability against `ARMProof::AReach.trans`; re-walking
     `alignedPair_loop` or `inputLength_loop` inside a target; the multiplication invariant
     against `Machines/Bin`.

   All 22 population files and the screen script are attached for a rerun.
6. **The parallel split.** Confirm that the two parallel batches' changes are disjoint and
   compose: the combined replay covers both at once.
7. **Documentation.** Check the appendices, the status tags and each new private's sketch
   against the delivered proofs.
8. **Size.** `InputAccess` 1,569 → 2,016 lines, `QueryReshape` 297 → 2,621, `Mult` 74 → 1,463,
   `Reductions` 153 → 184, `PreimageHost` as delivered. The briefs set no cap and require the
   helpers to be private in the owned files; file size alone is not a driver (user, 2026-10-11).
   Say whether you disagree.
9. Report anything else the fill or its records misstate, in the standard table.

## Repository-side attestations (verify or challenge)

* **Delivery integrity.** Every delivery's `SHA256SUMS` was all OK; the five manifests are
  attached. Deliveries carried environment shims (`lean-self-path.c`, `app-path.c`) and agent
  helper scripts. None was compiled or run, and nothing references any of them. These are
  maintainer attestations.
* **Freeze:** per delivery, `audits/logs/b7-fill-{1,2,3,4,5}-freeze.log`; cumulative,
  `audits/evidence/b7/fill-gate/freeze-cumulative.log`.
* **Replays** (user-run, fresh `.oleans` into tip-consistent snapshots): one per delivery, and
  the combined tree for continuation 3 and the multiplication batch
  (`audits/logs/fills-4-replay.log`): 11 modules, **0 errors**; `QueryReshape`, `Reductions` and
  `Mult` have 0 sorry warnings.
* **Axioms** (`audits/logs/b7-fills-45-axioms.log`): all 51 publics of the five files print within
  the standard triple; the admission walks of all twelve targets are empty; the private-constant
  censuses (365, 80, 1,182, 3 and 500 private constants) find no `sorryAx`.
* **Pre-ship probe** `audits/evidence/b7/B7StatementsProbe.lean.txt`, rerun at each issue tree.
* **Lint:** 0 FAIL over `SpaceComplexity`; the warnings are all file-size ones.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into `audits/b7-fill-findings.md`.
The B7 fill gate closes when it has zero blockers and zero majors; cluster B7 is then complete.
