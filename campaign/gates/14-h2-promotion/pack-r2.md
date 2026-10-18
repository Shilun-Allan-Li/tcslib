# External audit pack — H2-S, round 2: promoting the step block (repairs and re-audit)

Round 2 of the statement gate for host H2, the step block promoted from
`TuringMachine/CodeSimulator.lean` to a public module `Build/StepBlock.lean` (namespace
`Turing.StepBlock`). Round 1 (`audits/h2-promotion-findings.md`, attached verbatim): **gate open,
0 blockers, 3 majors, 5 minors**, no false copied contract. The round-1 pack and bundle are
immutable and unchanged; this pack is additive. The gate closes on zero blockers and zero
majors across both rounds. Record findings in `audits/h2-promotion-r2-findings.md`.

**What did not change.** The seven copied contracts and every copied definition: their code is
byte-identical to round 1's draft (58 of 58, `fidelity-r2-pass.log`), and still faithful to the
private originals. The repairs are in the additive results, the design note, the scripts and the
evidence.

**What changed underneath.** Since round 1, PR #84 (fills-8, campaign commit **1781a230**)
integrated the two B5a continuations into `CodeSimulator.lean`: H1's hosted clock (11 private
declarations that cite the block's contract), the canonizer's parse front end, and H1's style
cleanup, which rewrote the proof bodies of 24 step-block declarations without changing a
statement. **Every round-2 check was run at 1781a230**, read-only, against that commit's full
olean snapshot. The round-1 move probe is therefore stale for those 24 bodies; the move manifest
is recomputed there (design note §1.5).

Every `file:line` in this pack and the design note is at 1781a230. In the logs, `h2/r2/` is
`audits/evidence/h2/r2/`.

**Maintainer note (since drafting).** The B6 hosts' statement-gate pack
(`audits/b6-hosts-statements-pack.md`, issued separately) restates the ruler host
`exists_rulerHostTM` in landing form as a block simulation. It adds the lower bound `t ≤ t'`, the
exit cut, intermediate frames and `0 < C`. Its landing-form unit
`audits/evidence/b6hosts/gate/B6Hosts.lean.txt` is attached for brief item 2. That gate audits
H5's statements; this one audits only H2's requirement on them.

## Resolutions (detail: `audits/h2-promotion-resolutions.md`)

| # | Round 1 | Round 2 |
|---|---|---|
| 1 | major: `roundTM_iterate` lacks a lower bound | **Repaired.** Restated `∃ T, t ≤ T ∧ T ≤ t·B ∧ …`, proved (positive round times); new `roundTM_firstExit_unique`; the reset/forward wrapper is the consumer obligation CO-RF. |
| 2 | major: H5 as literal lockstep | **Repaired.** H5 is a positive, finite block simulation (frames, output, exit cuts, envelopes), literal lockstep its `L = 1` case, with per-consumer resource guarantees; the ruler device and the user's 2026-10-13 decisions taken in. |
| 3 | major: missing sources, no manifest | **Repaired.** Sources bundled; `importclosure.py` and its output; probes distinguished from the H2-M replay. |
| 4 | minor: reset output invariant | CO-RF in the auditor's form; data-level steps probed. |
| 5 | minor: ownership manifest | `movemanifest.py`, by name, at the integration base; a rehearsal of commit 1 elaborates. |
| 6 | minor: `fidelity.py` | `fidelity-r2.py` with inventory, whitelist, nonzero exit, seven negative controls. |
| 7 | minor: size | Layering/consumer analysis; a split would publish 19 private declarations; one module. |
| 8 | minor: descriptions | All corrected; line lengths in Unicode characters; the axiom claim qualified. |
| — | (new) H1's rule-11 escalation | Handled in the H2-M move: re-wrapping and `hr` → `_hr`, α-equivalent, checked by a probe with a negative control. |
| — | O5 (narrower surface) | 15 helpers private, 56 public names, no contract changed. |

## Scope

| Item | Where |
|---|---|
| Lean under audit | `audits/evidence/h2/r2/StepBlockDraft-r2.lean.txt`: **only** `roundTM_iterate` (restated and reproved), `roundTM_firstExit_unique` (new), and the docstrings of `outputSummary` (rewrap), `Key`, `roundTM_effect` and the module; the probes `MovePlusAdditive-r2`, `PostMove-CodeSimulator`, `AlphaProbe`/`AlphaNeg`, `ResetProbe` as evidence |
| Design | `audits/evidence/h2/r2/H2-design-r2.md` (the revised note; changes marked [r2], listed in its §0) |
| Source text | [AB09] §1.4.1, proof of Theorem 1.9 (motivation only: the private source is the fidelity reference, as in round 1) |
| Out of scope | the seven copied contracts and copied definitions (unchanged; round-1 NF2), the C1 table identity (round-1 NF5), tactic proofs, colleague-owned files |

## Brief for the auditor (round 2)

1. **Finding 1.** Check `roundTM_iterate`'s new statement and proof: the lower bound `t ≤ T`, its
   use for an arbitrary physical horizon (docstring), and that the statement still concerns
   the silent block only. Check `roundTM_firstExit_unique`: is "exactly one positive first
   visit to `entry` or `halt`" the right uniqueness for H1's `h1RoundTime` (`CodeSimulator.lean:5764`,
   by `Nat.find`) and for MIG-0b's `RoundContract.time` (`Contract-mig0b-draft.lean.txt:1636`)?
   Both are proved in the draft modulo the sorried contract and, in `MovePlusAdditive-r2`,
   against the proved one.
2. **Finding 2.** The revised H5 requirement (design note §2.3a): are the five items (positive
   finite block, frames, output, exit cuts, envelopes) right and sufficient for each consumer's
   guarantee (Z1/H1, `U₀`, `SU` at `C·s` through the ruler, C1, U-1)? Does the B6 draft's
   `exists_rulerHostTM` (`B6HostsDraft.lean.txt:1244`) fit as a checkpoint statement, and is
   the recommended cofinality addition the only gap? Compare with the landing form in
   `audits/evidence/b6hosts/gate/B6Hosts.lean.txt` (maintainer note above).
3. **Finding 4.** CO-RF (§2.3b): is it complete, including the halting round and the ledger?
   The three probe lemmas check only its data-level steps.
4. **O5.** The tier rule (§4.2) and its mechanical check (`movemanifest.out`, *Surface*): is any
   tier-C helper (`payload`, `applyPayload`, the ranks, `skipPart`, `skipRed`, `seekRouterTM`,
   `seekNext`, `seekPart`, `seekRed`, `seekTM`, `twoMoveTM`, `part`, `red`) needed by a consumer?
   Is keeping the carrier types (`SeekCtrl`, `SeekKey`, `SeekPh`) public right?
5. **Finding 5 and the integration base.** The manifest (`movemanifest.out`) and the rehearsal
   (`PostMove-CodeSimulator.lean.txt`): the `section StepBlockClients` with `open StepBlock`
   around the summary-clock family and H1's clock, the 35 renamed references, the status text,
   the timing rule. Is the comparison with round 1's probe (exactly the 24 cleaned-up
   declarations differ, 12 only in whitespace or comments, no statement) sound?
6. **The H2-M text edits** (§4.7): is the claim "no statement or definition changes, up to
   α-equivalence" established by the token-identity check, the elaboration, and the
   `with_reducible rfl` probe with its negative control? Should `hr` be renamed `_hr` (proposed)
   or dropped?
7. **Finding 6.** `fidelity-r2.py` as the H2-M freeze basis: coverage and failure handling;
   are the seven negative controls the right ones?
8. **Finding 7.** The size ruling under the user's rule (size alone never justifies a split):
   are the layering and consumer reasons and the measured cost (19 private declarations
   published) adequate, and is the resolution point well defined?
9. **Finding 8 and records.** The corrected descriptions and attestations below.
10. Report anything else the revised draft, note or evidence misstates, in the standard table.

## Maintainer attestations (verify or challenge)

1. **Elaboration** (`audits/logs/h2-statements-r2-elaboration.log`, every transcript included or
   attached; `bash tools/leanelab.sh` read-only, no olean written, Lean `v4.25.0`):
   - the draft: **0 errors, 7 `sorry` warnings (the seven contracts), 0 other warnings**;
   - the axiom-probe copy (64 prints): **54** declarations within `{propext, Classical.choice,
     Quot.sound}`; **10** add `sorryAx`: the seven contracts and `roundTM_visited`,
     `roundTM_iterate`, `roundTM_firstExit_unique`, through the main contract;
   - `MovePlusAdditive-r2` (the 121 declarations generated by name at 1781a230, proposed
     visibility, H2-M edits, plus the 6 additives): **0 errors, 0 sorries, 0 warnings; all 127
     prints within the standard triple**;
   - `PostMoveProbe` (the module, then `CodeSimulator.lean` after commit 1, one file):
     **0 errors, 2 sorries (`exists_polyCanonizer`, `exists_uniformSimulator`), 0 warnings**;
   - `AlphaProbe`: **0 errors** (9 `sorry` warnings, the theorem copies `X_orig`); `AlphaNeg`:
     **exactly 1 error**, the expected `rfl` failure;
   - `ResetProbe`: 0 errors; its three lemmas within the standard triple.
2. **Fidelity** (`fidelity-r2-pass.log`): 58 of 58 copied declarations match after renaming;
   58 of 58 byte-identical in code to round 1's draft; the six additives exactly the whitelist;
   exit 0. Negative controls (`fidelity-r2-negctl.log`): 7 of 7 exit 1; the round-1 script exits
   0 on three of them (finding 6's defect, shown).
3. **Move** (`movemanifest.out`): 121 of 121 declarations found by name in three regions; no
   moved code uses staying code; against round 1's probe, the code of exactly the 24 declarations
   that H1's cleanup touched differs (12 at the token level, all in proof bodies; 12 in
   whitespace or comments); 35 references in H1's clock renamed, all to public names; no other
   library file names a moved declaration; with the H2-M edits, no line over 100 characters and
   every edit token-identical (up to one binder name). Negative control
   (`movemanifest-negctl.log`): exit 1, 4 failing checks.
4. **Closure** (`importclosure.out`): 625 modules, no dangling import; replay set **8 modules**
   (asserted); O3 and O9 alternatives 24 and 224.
5. **Lines** (`linelen.out`, Unicode characters): round 1's moved source at fills-7 had **83**
   lines over 100 (**101** counted in UTF-8 bytes, round 1's mistaken metric); round 1's probe 75;
   both drafts 0; at 1781a230 the moved region has 14; the H2-M module, **0**.
6. **Size** (`splitcost.out`): a Record/Seek/Round split would cut 19 private declarations.
7. **Style** (`style-lint.out`, the repository's lint on a copy of the draft): one line, the
   draft's size (1,039 lines; reported, not acted on, per the user's rule).

8. **The maintainer's re-check.** With the same tool, checkout and snapshot, the maintainer
   re-elaborated the draft, the axiom-probe copy, `MovePlusAdditive-r2`, `PostMoveProbe`,
   `ResetProbe`, `AlphaProbe` and `AlphaNeg`, with the counts above (the axiom prints recounted:
   64 with 10 `sorryAx`; 127 with none). It also re-ran `fidelity-r2.py`: the pass run exits 0
   (58 of 58, byte-identical to round 1), and each of the seven negative controls exits 1. These
   are transcripts of the maintainer's own runs, distinct from the drafter's.

Corrections to round 1's attestations: "the axiom prints use at most the standard three"
should have excluded `roundTM_visited` and `roundTM_iterate` (attestation 1 above); "101 lines
over 100 columns" counted bytes (attestation 5); the maintainer's "independent second
elaboration" had no transcript, so round 2 attaches every transcript it cites.

## Verification appendix

* Everything is regenerated by `audits/evidence/h2/r2/run-all.sh.txt` (`python3 -I` only; Lean
  only through `tools/leanelab.sh`, whose four lines are quoted in the elaboration log).
* The probe files that begin with the generated module are given as their appended part
  (`AlphaProbe-tail`, `AlphaNeg-tail`, `ResetProbe-tail`, `PostMove-CodeSimulator`); the generated
  module itself is the first part of `MovePlusAdditive-r2.lean.txt`, up to its line
  `/-! ## Additive results (round-2 draft, appended for the axiom probe) -/`.
* The H1 escalation is quoted from `audits/b5a-fill-agent-reports/h1-3-REPORT.md` (lines
  100–158, with its SHA-256) in `h1-3-escalation-excerpt.md`; the full report (about 478 KB,
  mostly screen output) is not attached.
* Not attached: `Build/Catalog.lean` (imported only; 653 KB), round 1's C1 probe (NF5 closed),
  `NDCodes.lean`.

## Bundle manifest — 68 attachments after this pack

In bundle order (`BUNDLE-FILES.txt` has the exact paths):
- the standards and records: `audits/TEMPLATE.md`, `policy.md`, `workflow.md`,
  `machine-library-design.md`, `backlog.md` (5);
- round 1's findings (verbatim), the resolutions, round 1's pack (3);
- the revised design note, the round-2 draft, the elaboration log (3);
- fidelity: the script, its pass log, the mutation script, the negative-control log (4);
- the import manifest: the script, its output, the full graph (3);
- the move manifest: the script, its output, the strict comparison with round 1's probe, the
  simulated-base script and its log (5);
- the probes: move plus additives (file and output), the rehearsed `CodeSimulator` (file and
  output), the alpha probe and its negative control (tails and outputs), the reset tail (9);
- the helper scripts and outputs: `mkprobes`, `mkalpha`, `elabsummary`, `linelen` (script and
  output), `splitcost` (script and output), the lint output, the driver `run-all.sh` (9);
- the H1 escalation excerpt (1);
- round 1's design note, draft, move probe and fidelity script (4);
- the fills-8 integration record (1);
- the sources (17): `CodeSimulator`, `CodeFormat`, `Build/Seam`, `Build/CounterLoop`,
  `Build/VirtualInput`, `Build/Contract`, `Configuration`, `Deterministic`, the
  `TuringMachine` facade, `UniversalBlock`, `UniversalStartup`, `UniversalInterpreter`,
  `Universal`, `ClassNP/TMSAT`, `Codes2Tape`, `Diagonalization/EXPCOM`,
  `Diagonalization/NTimeHierarchy`;
- MIG-0b's draft, the B6 host note and draft, and the B6 hosts' landing-form unit (4).

Total 5 + 3 + 3 + 4 + 3 + 5 + 9 + 9 + 1 + 4 + 1 + 17 + 4 = **68**.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/h2-promotion-r2-findings.md`. This pack is immutable once sent.
