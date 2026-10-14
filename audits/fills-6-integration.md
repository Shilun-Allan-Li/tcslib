# fills-6: eight deliveries (three complete, five partial): integration record

Side branch `integrate/fills-6`, stacked on the gate-close branch `gate/t2a-vendor-close` (PR #65).
Each delivery was applied by `git am -3` with Codex authorship. Every owned file was unchanged
between the agent's base and the integration base, and each matches the delivered snapshot byte
for byte. The two B5a batches own disjoint declarations of `CodeSimulator.lean`, and H1 applied
cleanly on top of the canonizer. Maintainer commits are comment-only, apart from S1b's one-line
fix.

| Delivery | Brief | Agent commit (base) | Integrated | Report |
|---|---|---|---|---|
| §12.10 W2-S, continuation 2 (**complete**) | `briefs/w2-fill-oraclesim-cont2.md` | `1ff39af0` (`3462c1b4`) | `a7644554` | `audits/wave1-fill-agent-reports/oraclesim-3-REPORT.md` |
| §12.8b record tables, continuation 2 (partial) | `briefs/w1-fill-recordtable-cont2.md` | `3f80dd13` (`3462c1b4`) | `500f6580` | `audits/wave1-fill-agent-reports/recordtable-3-REPORT.md` |
| B5a, the canonizer (partial) | `briefs/b5a-fill-canon.md` | `4a42e855` (`3462c1b4`) | `0a6a36f0` | `audits/b5a-fill-agent-reports/canon-1-REPORT.md` |
| B5a, H1 (partial) | `briefs/b5a-fill-h1.md` with addendum 1 | `672b26cd` (`3462c1b4`) | `c0a85970`, `57d9478b` | `audits/b5a-fill-agent-reports/h1-1-REPORT.md` |
| B4, TQBF membership (partial) | `briefs/ch34-b4-mem.md` with addendum 1 | `92c9a743` (`3462c1b4`) | `b97b1dec` | `audits/ch34-fill-agent-reports/b4-mem-REPORT.md` |
| B3a, constructibility (**complete**) | `briefs/ch34-b3a.md` | `fe512dd4` (`ebc58d67`) | `595f5237` | `audits/ch34-fill-agent-reports/b3a-REPORT.md` |
| B5b, the `EXPCOM` summit (**complete**, modulo B5a) | `briefs/ch34-b5b.md` | `7a2ed9ed` (`ebc58d67`) | `2df46a3e` | `audits/ch34-fill-agent-reports/b5b-REPORT.md` |
| S1b, the configuration-graph summit (partial) | `briefs/ch34-s1b.md` | `3e7e2a79` (`ebc58d67`) | `5075c4a2`, fix `1f3a1fb3` | `audits/ch34-fill-agent-reports/s1b-REPORT.md` |

## Results

- **W2-S: 1/1.** `Turing.FinOracleTM.exists_plain_simulation` is proved with no admissions, with
  20 new privates: the stable frame, the two initialization handovers, the service seam
  (the inherited copy and the relocated call, composed by R2 with its first-return cut), the
  global invariant and the time ledger. A query costs at most `2·|p| + 2·|z| + tCall + 13`.
  Its corollaries and `POracle_eq_P_of_mem_P` now have empty admission walks.
- **B3a: 2/2.** `spaceConstructible_logSpace` and `spaceConstructible_linear` are proved, with 15
  privates, through the sanctioned `InputLength`, `VirtualInput`, `Seam` and `Machines.Bin`
  imports.
- **B5b: 1/1, proved modulo the two §12.11 rows.** `NPOracle_EXPCOM_subset_EXP` follows design
  §12.10's compositional route: the W2-V certificate shell, the W2-C choice-word machine and
  W2-S's oracle-call trace, around a private `EXPCOM` decider. It has 17 privates. The delivery
  cited W2-S as a third admission; W2-S lands in the same integration, so the summit now rests
  only on `exists_polyCanonizer` and `exists_uniformSimulator`.
- **Record tables: still 14/20.** This continuation proves the finite table-find round and its
  clocked interface (20 privates); the find wrapper, append and rows 17–20 remain. **User,
  2026-10-12: narrow to rows 17–18** (template and initial record, which B6's window route
  needs). Rows 15, 16, 19 and 20 pause as retirement candidates (backlog MIG-23); the proved
  find round is kept.
- **B5a canonizer: still 0/1** of its target. 23 privates: the canonical-bit scan
  (`canonBitsTM`), the canonical-header check `exists_canonHeaderOKTM`, the nonoverflowing
  successor counter `exists_canonCountTM`, and the inherited guard specialized to the
  post-header offset (`canonGuard_run`), with the rejection law `decode_of_canonGuard` for the
  single block size `max F.guard ((4k + 5)·3^(k+1))`. Open: connecting the preloaded guard to
  the loader (the count must reach the counter tape, by extraction then an install call), the
  record parser, the suffix check, prefix/fallback emission and the ledger.
- **B5a H1: still 0/1.** 16 privates: the selected-record component `h1RecordTM`, which reads a
  canonized record's `4k + 4` fixed bits into finite control and executes them on the mirrored
  tapes and the native input in exactly `4k + 5` steps, recording the emission in the summary
  cell. Its control depends only on `k`. **Addendum 1 is proved for this component**
  (`h1Record_envelope`, included in `h1Record_effect`): only the last step moves a mirrored or
  input head, by at most one; the table head advances by `min u (4k + 4)`; the summary head is
  fixed. Open: record lookup, successor installation, the round seam, the whole round's
  envelope, the nested-input load, the canonizer install and the hosted counter loop.
- **B4 membership: still 0/1.** 45 privates, 29 of them theorems: input validation (pair and
  grammar automaton) and a generic AND/OR core, `b4mValue`, `b4mValue_truth` and
  `b4mWalk_value`, with framed leaf contracts. **User, 2026-10-12: stop; do it as a program.**
  TQBF ∈ PSPACE becomes a program of the §15 language compiled by stage 2, with the proved pure
  core as its specification (backlog MIG-22). The leaf-contract definitions are unused and lack
  an input/records precondition; they are not promotion-ready.
- **S1b: 2 of 3 bodies, proved modulo the simulation.** `NL_subset_P` and
  `polyTimeReducible_of_mem_NL` rest only on `NSPACE_subset_exp_dtime`, which keeps its
  admission, with 18 privates. The delivery could not finish module verification in its
  environment and did not compile at integration: a redundant `rfl` after `rw` in
  `s1b_record_accepts` (fixed in `1f3a1fb3`). **User, 2026-10-12: stop at this partial.** The
  simulation is to be proved as a program (design §16, MIG-19).
- No delivery adds a public declaration, changes a statement, or touches another batch's file.

## Verification (maintainer)

- **Integrity.** Every `SHA256SUMS` entry is OK: 55, 42, 38, 81, 23, 27, 41 and 27. Each git
  bundle verifies inside the repository, its tip equals the delivered snapshot, and the
  patches reproduce the bundle's tree. The deliveries' environment shims are excluded:
  `app-path.c`, `self-exe-compat.c`, `runtime-app-path.c` and `self-exe.c`. So are the agent
  scripts and the copies of repository tools: `axiom_summary.py`, `env.sh`, `freeze_check.py`,
  `reproduce.sh`, `screen.sh`, `screen_changed.py`, `verify_probe.py`, `verify_screen.py`,
  `verify_sweep.py`, `audit_verification.py`, `environment.sh`, `lean-one-worker.sh`,
  `screen_delta.py`, `check_freeze.py`, `run_final_verification.py`, `check-freeze.py`,
  `check-sorries.py`, `make-development.py`, `make-probes.py`, `screen-new.py`,
  `verify-evidence.py`, `audit-logs.py`, `measure-copies.py` and `evidence/repository-tools/`.
  None was compiled or run, and no patch references any of them. Every added line of every
  patch was scanned for `#eval`, `run_cmd`, `IO`, `unsafe`, `implemented_by`, `extern`, new
  syntax or elaborators, and `native_decide`: none. (Four matches are the word "initialize" in
  docstrings.)
- **Freeze** (`audits/logs/{w2-oraclesim-fill-cont-2,w1-recordtable-fill-cont-2,b5a-fill-canon-1,b5a-fill-h1-1,ch34-b4-mem-1,ch34-b3a-1,ch34-b5b-1,ch34-s1b-1}-freeze.log`).
  - No statement changed, and no public was added or removed. S1b's log shows a public `of`,
    a false match on a docstring line.
  - The only changed bodies are the authorized targets and their flagged appendices.
  - Privates added: OracleSim 20, RecordTable 20, CodeSimulator 23 + 16, TQBF 45,
    Constructible 15, EXPCOM 17, ConfigGraph 18. No existing private changed.
  - The only import changes are the sanctioned ones: B3a's three and the optional
    `Machines.Bin`, B5b's two, S1b's `RecordTable`.
- **Duplication.** Each per-batch screen was run on a tree holding only that agent's file over
  its base, with the brief's population. Every one matches its agent's screen byte for byte;
  S1b supplied no after-screen, and its maintainer screen stands alone.

  | Delivery | Before | After | New pairs |
  |---|---|---|---|
  | W2-S | 1,477 / 1,747 | 1,498 / 1,749 | two in-file (`oracleHost_initial` against two preparation lemmas, 51–52%) |
  | Record tables | 1,477 / 1,747 | 1,495 / 1,749 | two in-file (the find round's scan and skip phases, 60–68%) |
  | B5a canonizer | 1,572 / 1,801 | 1,590 / 1,802 | one in-file (`canonHeader_length` against `canonHeaderOK_iff`, 56%) |
  | B5a H1 | 1,572 / 1,801 | 1,583 / 1,801 | none |
  | B4 membership | 1,472 / 871 | 1,508 / 873 | two in-file (`b4mRank_progress` and `b4mBack_run` against the record-carry lemmas, 53–62%) |
  | B3a | 1,228 / 1,520 | 1,243 / 1,520 | none |
  | B5b | 871 / 522 | 887 / 524 | `expcom_bits_two_pow` against Separation's private `bits_two_pow` (94% / 84%), pre-disclosed as forced |
  | S1b | 1,175 / 761 | 1,190 / 761 | none |

  **Combined screens at the integration head**
  (`audits/logs/fills-6-{wave1,b5a,ch34}-screen-combined.txt`; populations in
  `audits/evidence/fills-6/`).
  - **Wave 1** (24 files; 1,545 / 1,748) and **B5a** (27 files; 1,656 / 1,802): against the union
    of the per-batch screens, no pair is new at the head, so there is **no cross-batch pair**.
    Four standing pairs are gone: `catalog_space_bound` against three `f2_` space lemmas and
    `a2_map_space`, retired by the gate-close derivation (T2a note 16).
  - **Chapters 3–4** (the union of the four wave-5 and B4 populations, 66 files; 2,685 / 2,464).
    It pairs files that no single population held together, so most of its unseen pairs are
    old pairs between untouched files. Two involve a fills-6 declaration, and neither is a
    copy. `rt_find_read` reproduces all of `SAT.satRed_one` (63 characters), whose body is the
    one-line `rw [runFrom_succ_eq_step, runFrom_zero]` that dozens of declarations contain.
    `expcom_front_poly` reproduces half of `SAT.sat_pipeline_poly` (255 of 505): both compose
    the polynomial-time closure rows, and the shared text is their citation names.
  - **Older pairs exposed by the wider population** (they predate fills-6, and go to the W2-S
    and B5a fill gates): OracleSim's `oracleChoiceAction`, `oracleChoiceCfg` and
    `oracleShadowAction` against `Simulation.lean`'s `leftAction`, `rightAction` and `rightCfg`
    (53–75%); OracleSim's `oracleBankCfg_eq` against Loop's `emCall_exit_fixed` (56%); and
    `CodeSimulator.guardBlock_orbit` (fills-5) against `Games.playOut_eq_iterate` (74%). No
    earlier population held both sides.
- **Reviewer findings** (three read-only reviews):
  - **S1b:** `s1b_radius_bits` restates a `Nat.bits` length fact without disclosure; it is the
    fifth private copy, after EXP, Nondeterminism, EXPCOM and Separation.
  - **B3a:** `b3a_seam_space` re-derives the public Seam space lemma in reworded text, which the
    screen does not catch; it is disclosed as a promotion candidate. `b3a_cfg` is close to
    `Cfg.ofWords`.
  - **B5b:** `expcom_inc_prefix` restates Catalog's `catalog_increment_value` without
    disclosure. Two proofs, `expcom_summit_budget` and `expcom_all_true`, lacked proof sketches;
    the maintainer added them (`36503704`). The delivery's conservative ledger puts `EXPCOM`'s
    copied material at **36.52%**, above one fifth, in a file already under CH34-D3: the
    `backlog.md` §1 item **CH34-D4** is opened, as `workflow.md` §4 requires.
  - **W2-S:** clean. `oracleEmbed_updateTape` is worth promoting.
  - **Record tables:** `rt_find_scan` overlaps CfgRecord's `recordStep_scan_preserves`. The note-50
    empty-tag case is a placeholder. The next brief should name the outer host and a public
    head-displacement lemma: Catalog's `f2_head_steps` is private, and the public
    `workTapePos_step_le` suffices.
  - **B5a canonizer:** `canonBits_of_last` and `canonBits_value` overlap semantically with
    `ntc_bits_codeBitsNat_append_true`, `bits_foldr_bit_one` and `ntc_codeBitsNat_eq_ofDigits`.
  - **B5a H1:** clean; it cites the public record reader, `tapeAction` and
    `workTapePos_apply_le`. It names one gap: no row reads a fixed-width undelimited prefix into
    finite control.
  - **B4:** its "H1" (the host registry's AND/OR evaluator) clashes with the B5a batch named H1.
    Briefs now say "registry H1" or "B5a H1".

  The promotion and deduplication requests are collected in `backlog.md` §1, **F6-1**.
- **Lint** (`audits/logs/fills-6-stylelint.log`): 0 FAIL over `TuringMachine`,
  `Diagonalization`, `SpaceComplexity`, `ClassPSPACE` and `ClassOracle`. The warnings are all
  file-size ones.
- **Sizes and counts** (public / private): `OracleSim` 2,604 lines (13 / 87); `RecordTable` 2,470
  (28 / 33); `CodeSimulator` 1,717 (13 / 78); `TQBF` 2,639 (8 / 164); `Constructible` 538 (3 / 15);
  `EXPCOM` 761 (9 / 18); `ConfigGraph` 944 (16 / 30). The briefs waive size.
- **Replay** (user-run, fresh `.oleans` into the snapshot, at `56258cb5`;
  `audits/logs/fills-6-replay.log`). It covered the downstream closure of the twelve changed
  modules, the gate-close edits among them: **41 modules, all with 0 errors.** The sorry
  warnings are exactly the expected open rows, including `OracleSim` 0, `EXPCOM` 0,
  `Constructible` 0, `CodeSimulator` 2, `RecordTable` 6, `ConfigGraph` 1, `TQBF` 3 and `Zone` 2.
  The branch was later rebased onto two non-Lean gate-close commits (the `TCSlib` tree is
  identical), and `36503704` adds the two sketches (comment-only; `EXPCOM` elaborates with no
  errors after it).
- **Axioms and admission walks** (`audits/logs/fills-6-axioms.log`; probe
  `audits/evidence/fills-6/AxF6.lean.txt`, against the replay tree). Every public of the eight
  owned files and of `Catalog`, `Zone`, `ClassOracle/Classes`, `Relativization`, `Hierarchy` and
  `Savitch`, 239 in all:
  - no non-standard axiom;
  - 207 walks are empty, among them W2-S's four rows, `POracle_eq_P_of_mem_P` and B3a's two;
  - 21 open rows rest on themselves alone;
  - `EXPCOM`, `expCode`, the scheme instance, `EXP_subset_POracle_EXPCOM`, the summit, the three
    chained identities and `baker_gill_solovay` rest on exactly the two §12.11 rows;
  - `NL_subset_P` and `polyTimeReducible_of_mem_NL` rest on exactly `NSPACE_subset_exp_dtime`;
  - the private censuses of all thirteen files find no `sorryAx` (OracleSim 350 constants,
    RecordTable 235, CodeSimulator 225, TQBF 528, Catalog 1,559 and the rest).

## Maintainer commits (comment-only unless stated)

- `1f3a1fb3` (**code**): drops the redundant `rfl` in `s1b_record_accepts`; `rw` closes the goal.
- `bc04b204`: `ConfigGraph`'s status and docstrings no longer say "unverified"; they record the
  program route (MIG-19) and that `spaceConstructible_logSpace` is proved.
- `5ca96aa3`: `CodeSimulator`'s module status lists what both B5a deliveries prove and what
  remains; H1's appendix starts its own paragraph.
- `4a5b646b`: the `oracleHost` docstring, `POracle_eq_P_of_mem_P`'s appendix and `EXPCOM`'s header
  no longer describe W2-S as pending.
- `36503704`: proof sketches for `expcom_summit_budget` and `expcom_all_true`.

## Disposition

All go in by PR, stacked on PR #65. The gate packs for the three complete deliveries
(W2-S, B3a, B5b) and the next continuation briefs follow in their own PRs.
