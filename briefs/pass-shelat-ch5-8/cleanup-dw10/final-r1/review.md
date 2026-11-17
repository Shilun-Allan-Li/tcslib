# DW-10 seal inventory (`dw10-seal-inventory`), final: maintainer's static review

**Delivery** exchange `exchange/pass-shelat-ch5-8` commit `57cd9272d5739fae252cf486297c696f7b90d2bd` ("audit
dw10-seal-inventory: final", parent `607034428468ffd88adec313eb293e3e60520f59`), folder `inbox/audits/dw10-seal-inventory/`.
Checkpoint 1 was `82d1966006fec33ec8c5c34e2bdd0b8a07365e56`. **Issued** `cleanup-dw10/issued-r1/` (records pin
`4367db3c9f3c0b4dd81117ab001e6707aa42c0c5`, pack `d4cfd2f893fb9b448c5d997f037d6ba055cbc031`). **Reviewed at** records
`659542ecd9413b504d30da8c937b9805e6c1f71f`. The review is static only: git, `python3 -I` and text tools, with no Lean and no
`lake`. The delivery was extracted by `git archive` into an empty scratch directory, and the review scripts ran from a
separate directory. The worker's REPORT is treated as a claim; every count below was recomputed from the raw logs and the
sources at the base.

## Verdict: **ACCEPT WITH NOTES**

The inventory is complete and its numbers are exact.
- The 434 owners are sealed in all four variants: 1,736 owner-variants, 1,487 probes run and 249 deduplicated.
- 0 install or EOF gaps.
- Every count in `seals.tsv`, `seal-decls.tsv` and `inventory.tsv` reproduces from the 1,487 raw logs.
- All 1,779 input items are present, and 331 rows are NEW.
- The STATEMENT class is confirmed by an independent header test.
- Q1 and Q3 are applied correctly.

The notes are listed below:
- Two fix texts are corrected in the Stage 2 derivative (F02, F03).
- The `statement_level` column covers only the canonical variant, so 51 SEAL-B-ONLY declarations are statement-level
  under seal B (F01). This matters for the B-only ruling.
- Stage 1 was not cross-referenced (F04). Done here: Stage 1 resolves the three STATEMENT rows.
- One tool header is incomplete (F05).
- 28 Stage 2 items have unsettled fixes (F06), and 28 of the 74 new readers have no concrete statement (F07).
- The process records are F08–F10, and the records-side notes are F11–F14.

No round trip is needed: everything the Stage 2 brief needs is in `stage2-seal-items.tsv` and `stage2-readers.tsv`.

## 1. Integrity

| Check | Result |
|---|---|
| Delivery commits | `82d19660` and `57cd9272` change only `inbox/audits/dw10-seal-inventory/`. The issued exchange commit `d4cfd2f8` is an ancestor. `57cd9272` is the exchange tip |
| Top-level `SHA256SUMS` | 209 entries, all OK; the path set equals the delivered files (excluding itself) exactly; no `./` prefixes |
| `evidence/SHA256SUMS` | 206 entries, all OK; the path set equals `evidence/` exactly |
| 9 evidence ZIPs (7,557 entries, 6.4 GB uncompressed) | every entry matches its `.entries.txt` (path, bytes, SHA-256): 0 extra, 0 missing, 0 mismatched; `testzip` clean; largest part 87.3 MB (≤ 90 MB) |
| Archived Gate 06/10 tools | byte-identical to bb1-sim's copy (exchange `d929cc21`, tree `e25f7bf0…`). `mkseals_ab.py`/`mkseals_coe.py`/`scan*`/`touched.py`/`mkcollect.py` are unchanged. `runner_full.py`, `ctlcheck2.py` and `NmCollect.template.lean` are adapted (F05) |
| Commit signatures | `82d19660` carries `gpgsig` (disclosed; F10); `57cd9272` has none |

## 2. Pins

| Pin | Verified |
|---|---|
| Issue base | `f472accd5e000a53d0fbe02b5414435429ce4a70`: `git diff --quiet a6d01b1b… f472accd… -- TCSlib TCSlib.lean audits lakefile.lean lake-manifest.json lean-toolchain` exits 0. `TCSlib` tree `06b51ea90a9a0ef49e1dc3e7034ba32ec9b75fe6` at both |
| Records tip used by the worker | `cbc44b6e4ff3036860a77cc6a1c3bca0b0d33428`, an ancestor of the review tip. It has no `.lean`/toolchain/manifest change after the base |
| Records pin and pack | `4367db3c:…/issued-r1` = `d4cfd2f8:outbox/audits/dw10-seal-inventory` + `dispatch.md` (the only difference) |
| `main` | `a954201d` (start) is an ancestor of `b986b862` (merge of #353, §4.1 *Lean parallelism*) |
| Bootstrap | Recounted from the 613 raw boot logs: 613 modules, rc 0, 0 errors (both forms), 22 `sorry` warnings in 9 modules. This equals `base-sorries.txt` per module. Every source hash equals `SOURCE-SHA256SUMS` |
| Lean drift after the base | The review tip changes 19 TCSlib files after the base (bb1-sim, pairings; F13). Of the owners, only `Games/Probability.lean` and the facade `Games.lean` are changed; neither has a Stage 2 item |

## 3. Coverage and recount (from raw logs)

- **Seals.** All 434 owners have exactly four `seals.tsv` rows (strict-A/B, coe-A/B).
  - The 1,487 run logs map one to one onto the run modules.
  - rc, errors (form `^\S+\.lean:\d+:\d+: error[:(]`: 1,852 `error:` and 30 `error(`), install and EOF records
    (requested = verified, summed over `SEAL_CHUNK` parts) and log SHA-256 all agree with `seals.tsv` and `results*.jsonl`.
    There are 0 mismatches.
  - Every probe contains its owner's base source verbatim (subsequence check against `git show f472accd:<path>`, 1,736/1,736).
  - All 249 deduplications are byte-equal after the `SealB_`→`SealA_` label normalization.
  - The variant request sets differ exactly as specified:
    - strict-A − coe-A = {`FinDist.instCoeFunForallReal`} (376 owners, else 0);
    - B − A = {`Complexity.PolyExpr.eval`} (353 owners, else 0).
- **Totals reproduced.**

  | variant | failing owners | errors |
  |---|---|---|
  | strict-A | 67 | 424 |
  | strict-B | 99 | 737 |
  | coe-A | 62 | 385 |
  | coe-B | 94 | 698 |

  The request sums are 549,103 / 549,456 / 548,727 / 549,080 (max 3,926–3,928).
  - `seal-decls.tsv` sums equal `seals.tsv` per owner and variant.
  - The inventory's four count columns equal `seal-decls.tsv` on every row.
  - Every failing (path, declaration) has a seal row.
- **Attribution re-derived.** All 1,882 raw error lines were mapped probe line → source line → enclosing declaration
  independently. 1,868 agree with `seal-errors.jsonl`. The other 14 are the file-level `attribute [local irreducible]`
  lines (DW10-W5).
- **Controls.** `controls.tsv` has 434 owners: 280 pairs, 29 negative-only, 123 that define nothing and 2 with no passing
  candidate.
  - All 40 checked harnesses per variant are recounted from the 60 raw control logs: each log's errors equal its expected
    total, and there are no stray errors.
  - Sealed probes have their install and EOF records. 309 negatives fail once, and 280 positives pass in both strict and
    coe. `ALL_OK True`.
- **Scan.** 36,127 items and 135 foreign TCSlib items.
  - The 414 owners with items are covered. The other 20 owners contain no `simp`/`rw`/`unfold`/`delta`-family tactic at
    all (checked in the source).
  - Every foreign item is an open unfold row, except the 4 local-`P` false positives (DW10-W7).
- **Generated-equation reads.** There are 5 refs. C3-0002/0003/0004 are reconciled, and NEW:331 is new. The `exec.eq_def`
  ref is unattributed (no owner declaration's value).
- **Known records reproduced.**
  - DW-9: `ModuleHost` 10 and `IterateFindHost` 16 errors, plus 27 scan items.
  - F-01: `IterateFind` 20 errors.
  - Gate 35: `Universal` 10 (A) / 12 (B).
  - BS-F06: `Games/Probability` strict 1, coe 0.
  - SY-F07: 24 errors in 9 declarations.
  - SG-F07: group 6e/5d.
  - Requests: IterateFind 595, ModuleHost 241, IterateFindHost 251, Yao coe-A 3,046.

## 4. Reconciliation with the inputs (brief § *Reconciliation*)

**Rows present, missing, new.** All 1,779 input rows are present: 764 `H:` rows, 813 current ids, 124 provider pairs
(`EFF72:`/`LEV52:`) and 78 named-finding rows. 0 are missing, there are no duplicate ids, and 331 rows are NEW. The total
is 2,110. The #248 ledger JSON (`11-final-read-ledger.zip`, SHA-256 verified) holds 764 historical rows and 813 current
observations.

| source | HANDED-OFF | FIXED_SINCE | STILL_OPEN | CHANGED | NEW | total |
|---|---|---|---|---|---|---|
| #248 historical | 9 | 603 | 106 | 46 | – | 764 |
| #248 current | 437 | 36 | 286 | 54 | – | 813 |
| provider pairs (72 + 52) | 102 | 0 | 21 | 1 | – | 124 |
| SG-F07 / SY-F07 / C-F02 | 60 | 0 | 18 | 0 | – | 78 |
| new | – | – | – | – | 331 | 331 |
| **total** | **608** | **639** | **431** | **101** | **331** | **2,110** |

Scope → status (input `scope`, `base_match`):

| input | scope | → status |
|---|---|---|
| historical | HANDED-OFF | 9 → HANDED-OFF |
| historical | NO-DECLARATION | 7 → CHANGED ("declaration removed") |
| historical | OWNER, same-path | 410 → FIXED_SINCE, 106 → STILL_OPEN, 7 → CHANGED |
| historical | OWNER, moved | 192 → FIXED_SINCE, 32 → CHANGED |
| historical | OWNER, ambiguous | 1 → FIXED_SINCE |
| current | HANDED-OFF | 437 → HANDED-OFF |
| current | NO-DECLARATION | SEAL-0306/0307 → STILL_OPEN (file-level, W5) |
| current | OWNER, same-path | 31 → FIXED_SINCE, 283 → STILL_OPEN, 3 → CHANGED |
| current | OWNER, moved | 5 → FIXED_SINCE, 51 → CHANGED |
| current | OWNER, private-home | 1 → STILL_OPEN |
| provider pairs | efficiency-72, OWNER | 21 → STILL_OPEN, 1 → CHANGED (EFF72:SEAL-0207, moved) |
| provider pairs | efficiency-72, HANDED-OFF | 50 |
| provider pairs | levin-52, HANDED-OFF | 52 |

- Each provider pair carries its SEAL id's status: 124/124 agree.
- Named findings: SG-F07 9 and SY-F07 9 are STILL_OPEN, each with the recorded per-declaration count. SY-F07's 2
  `Uniform` rows and C-F02's 58 rows are HANDED-OFF.
- The 608 HANDED-OFF rows are the same items, by file and declaration, as `cleanup-dw10/handoff-complexity/items.tsv`.
  The id numbering of the named findings differs (F11).
- FIXED_SINCE: no FIXED_SINCE seal row has an A-variant error left in its declaration.

## 5. Classification

Class by tier (open rows, recounted from `inventory.tsv`; equal to the REPORT):

| tier | STAGE2 | STAGE2-PROVIDER-READER | SEAL-B-ONLY | STRICT-ONLY (notation, no fix) | STATEMENT | no class |
|---|---|---|---|---|---|---|
| T1 | 584 | 17 | 194 | 26 | 3 | 11 (W5) |
| T2 | 13 | 0 | 0 | 5 | 0 | 3 (W5) |

- The 7 `-`-tier rows (historical NO-DECLARATION) are CHANGED with no class.
- **Class against counts:** every class is consistent with the four count columns, with 0 exceptions:
  - STRICT-ONLY rows have coe = 0;
  - SEAL-B-ONLY rows have A = 0 and B > 0;
  - every STAGE2, PROVIDER-READER and STATEMENT row has coe-A > 0;
  - every strict-only failure is classed STRICT-ONLY (Q3).
- **Q1.** All 17 STAGE2-PROVIDER-READER rows name `Complexity/TuringMachine/Encoding.lean`, a handed-off file. Every STAGE2
  "add" reader lands in an owner: 94 add-clauses in T1 files, 19 in T2. No fix lands in a handed-off or other Complexity
  file. `Repetition.lean` is a Complexity-directory file, but it is campaign-created (T1).
- **STATEMENT, independent test.** Each canonical error was located against its declaration's header (bracket-aware search
  for the header's `:=`/`where`; docstring-position errors go to the next declaration). Only `host_dispatch`, `host_branch`
  and `host_halt` (IterateFindHost; 10 coe-A errors) fail in a header. That is exactly the 3 STATEMENT rows. The 31
  STATEMENT→STAGE2 overrides of the sub-agents are therefore right.
- **Overrides.** All 842 open rows have exactly one override row: lead 395, sub-A 288, sub-B 117, lead delta 42. Every
  inventory row equals its override in class, fix and `statement_level`. The 5 unmatched override rows are explained in
  `review/unmatched-overrides.txt` (W5/W7 and the C3 duplicate).
- **Reader names.** 797 reader names in "use" clauses were resolved against a static declaration index of the base and
  the worker's reader index. All resolve, except local terms and Mathlib names (`List.ofFn_congr`, …) and one forward
  reference to a reader that another row adds (`decGraphAt_apply`). None of the "add" readers already exists under that
  name. The GI/Col shadow namespaces do have equally named readers (`GI.decGraphAt_apply`, `GI.encInstance_eq`), and this
  is the DW10-W6 design.

**Spot check, 46 rows.** Each row was checked against its raw error message, the base source lines and the cited
definition:
- STAGE2 "use": H:205, H:60, SEAL-0200, SEAL-0184, SEAL-0191, SEAL-0287, SEAL-0288, SEAL-0253, SEAL-0367, C1-0313, C1-0300,
  NEW:329, NEW:304.
- STAGE2 "add": SEAL-0251, SEAL-0213, SEAL-0214, SEAL-0384, C1-0306, H:169, SEAL-0390, C3-0002.
- Other STAGE2: SEAL-0298, SEAL-0341, H:171.
- F-01: SEAL-0055.
- STAGE2-PROVIDER-READER: NEW:277, NEW:321, SEAL-0282, SEAL-0283.
- SEAL-B-ONLY: NEW:150, NEW:43, NEW:161, NEW:171, NEW:205.
- STRICT-ONLY: NEW:196, NEW:195, NEW:191, SEAL-0465.
- STATEMENT: NEW:9, NEW:10, NEW:11.
- FIXED_SINCE: SEAL-0400, H:220, H:276.
- CHANGED: H:68, SEAL-0232.

Results:
- 44 rows are right: the read is the cited definition, the reader exists or is genuinely missing, and the class follows.
  - SEAL-0251's proposed `yaoRaw_eq` has only a schematic statement (F07).
  - H:68 also fails under B in its statement (F01).
- **SEAL-0298 (and its twin H:127) is wrong** (F02).
- **C3-0002's companion C3-0004 is inconsistent** with the three GGM/Reduction rows that share its read (F03).

## 6. Findings

- **DW10-F01 (classification note; matters for the B-only ruling).** `statement_level` reflects only the canonical
  failure.
  - Under seal B, 54 declarations fail inside their statement headers:
    - 51 are SEAL-B-ONLY (190 declarations in that class). Examples: Lamport 14, `Yao` 5 (`yaoHybrid_callA`/`_callB`,
      `yaoSeed_good_whp`, `yaoHybrid_simulators`, `yaoHybrid_hbcSecure`), OneWay 4, SG-F07's `garbling_good_whp` and
      `nestedSpecial_wrongKeyBot`.
    - 3 are STAGE2 (`FunFamily.glPad_f`, `glBit_append`, `invProbAt_reduction_ge`).
  - Their headers mention `Fin (….eval n)` types that need `PolyExpr.eval` to reduce. Any decision to *fix* B failures
    would need statement changes for these.
  - No inventory change is needed. The list is in this review's evidence (`stmtcheck.txt`).
- **DW10-F02 (fix error, corrected in the derivative).** H:127 and SEAL-0298, `PadQuad.family_inLen`
  (`UniversalPadding.lean:114`).
  - The fix says "`family` is sealed after its definition in the whole-file seal; prove the reader through
    `unfold family`". That is wrong: own-file definitions are not in the request set. The coe-A probe's 1,080 requests
    include `FunFamily.ofString` and not `PadQuad.family`.
  - The read is `FunFamily.ofString` (`family := FunFamily.ofString (gStr F ℓ d) (.mul (.const 2) .var)`). Only
    `ofString_inLen_eval` is published for it, which is the `.eval` form.
  - Corrected fix: add `TCSlib.Cryptography.FunFamily.ofString_inLen : (ofString f p).inLen = .var` (by `rfl`) in
    `Asymptotic/OneWay.lean`, an owner. Then prove `family_inLen` by `unfold family` and `ofString_inLen`.
  - The lead's review log states the same wrong rule ("readers proved by `rfl` in the definition's own file").
- **DW10-F03 (inconsistent fix, harmonized in the derivative).** C3-0004 (`Candidates/Concrete.lean`,
  `rbl_loop_poly`) reads the splitter of `polyTimeComputable_iterateFind.match_1`. The match sits in the statement of
  the T1 theorem in `Repetition.lean`.
  - The row proposes a reader `polyTimeComputable_iterateFind.match_1_eq` for a compiler-generated matcher.
  - The three GGM/Reduction rows with the same read use sub-B's `Complexity.polyTimeComputable_iterateFind_elim` (the
    `Option.elim` form) in `Repetition.lean`.
  - The derivative uses the latter for all four. The lead log lists C3-0004 as "not resolved by the lead".
- **DW10-F04 (cross-reference missing; done here).** The brief asks whether Stage 1 or #347 already supplies each fix. The
  REPORT marks only #347.
  - Checked against Stage 1 (`land/cleanup-stage1` `d3c7cb00092ad5913904654d922f30fc7d5fce4a`, #355) and #347
    (`cleanup/dw5-derand-readers` `daa6e173cdd94cad1475b9a96eca613bce53ba61`): none of the 74 new readers is added by
    either.
  - Stage 1 adds `host_dispatch_view`, `host_branch_view` and `host_halt_view` (`IterateFindHost.lean:399/415/437` there).
  - After #347 the old `host_*` lemmas have no callers at `daa6e173` or `d3c7cb00`. At the base, `IterateFind` used them.
  - `cleanup-stages.md` Stage 2 already deletes "the public host lemmas left unused by DW-5". The 3 STATEMENT rows
    therefore need no frozen-statement change (DW10-Q9).
- **DW10-F05 (tool header incomplete).** `evidence/tools/seal/runner_full.py` lists changes (1) host paths and (2) resume,
  and says "Nothing else changed".
  - The delivered code also adds per-worker `RUN_TAG` result files, a `MemAvailable` ≥ 4.5 GiB start guard, and claim
    files with dead-pid takeover. `seals/PARALLEL.txt` calls the last one "change 5".
  - The takeover is a read-then-overwrite and is not atomic. It caused the double run (F09).
  - The brief requires every change to be in the header. Recorded; no re-run needed, since outcomes are unaffected (§3).
- **DW10-F06 (unsettled fixes).** 28 Stage 2 items carry a tentative fix. They are flagged `fix_confidence = needs-check`
  in `stage2-seal-items.tsv`.
  - 6 rows say "to be identified/confirmed by a Lean check": `Hybrid.exists_hybridBound` (H:116, SEAL-0277),
    `TrapdoorPredictor.tdpPredictor_runAtL` (H:117, SEAL-0279) and the two `CommitmentLemmas.acceptProb_distinguisher*`
    (SEAL-0318/0319), where a residual `X = X` differs in hidden arguments.
  - 22 rows are the lead's and sub-A's "needs a check" rows.
  - The Stage 2 worker must probe these first.
- **DW10-F07 (reader statements missing).** 28 of the 74 new readers have no concrete statement: `<its coin polynomial>`,
  "defining equations", "the unfolded … condition", a body placeholder, or none. 20 of them are W6 shadow-bridge readers.
  The Stage 2 brief must either state them or delegate the statements under the reader rules (formula docstring, `_eq`
  naming).
- **DW10-F08 (process: parallelism; recorded).** The brief and the dispatch prompt required one Lean process at a time
  through one lock. Lean phases and limits:
  - Before the override, these ran strictly serially: the bootstrap, the 5 collectors, the scan kinds probes, the locator,
    the first 12 seal probes (`results.jsonl`) and controls pretest attempt 1.
  - The user then overrode the rule mid-run. The worker quotes it: "I'm overriding the 'one Lean process at a time on the
    host' rule ...".
  - Seyoon's ruling (`workflow.md` §4.1 *Lean parallelism*, "user ruling, 2026-11-17", main #353 merge
    `b986b8620fc6117034462212df7070c80a79ff65`, 2026-11-17 05:13Z) then applied.
  - The seal phase ran 3, then 4 workers (pool = nproc 4), with a 4.5 GiB `MemAvailable` start guard.
  - `logs/memsample.log` (872 samples) shows at most 4 Lean processes, minimum `MemAvailable` 9.39 GiB and peak anonymous
    memory per process 518 MiB.
  - This is within §4.1: pool ≤ nproc, ≥ 2 GB (15%) available. The running phase was not interrupted, as §4.1 asks.
  - The sub-agents ran no Lean.
- **DW10-F09 (process: one probe ran twice; recorded).** `DW10Probe/S/SealA_Cryptography_Encryption_PrivateKey_FromPRF_Hybrid`
  (strict-A of `Encryption/PrivateKey/FromPRF/Hybrid.lean`) was taken by workers w2 and w4.
  - This happened at the 07:11:57Z restart, by the non-atomic claim takeover (F05).
  - Both runs recorded rc 0, 0 errors and the same log SHA-256 `162056f7235d…`. No olean is written.
  - It is the only module of 1,487 with two records. The outcome is identical, so there is no effect on the inventory.
- **DW10-F10 (process: signed checkpoint, disclosed).** Checkpoint 1 `82d19660` carries an SSH signature. The cause was
  `pull --rebase` under the host's global `commit.gpgsign=true`, the same as BS-F08. It was not force-pushed. The final
  commit is unsigned. No action.
- **DW10-F11 (records: id crosswalk).** `handoff-complexity/items.tsv` numbers SY-F07's `Uniform` rows `SY-F07:1–2` and
  C-F02 `C-F02:3–60`. The inventory uses `SY-F07:10–11` and `C-F02:1–58`, sequential per finding in
  `named-findings.tsv`. The items are the same 60 by declaration. Add a crosswalk when the handoff is released.
- **DW10-F12 (records conflict).** `cleanup-stages.md` § Stage 2 still says "Clear … `Uniform.lean`'s 4 inherited failures
  (SY-F07) through readers". DW-10 Q1, a later ruling, hands `Uniform` off, and the inventory carries the rows as
  HANDED-OFF (DW10-Q10).
- **DW10-F13 (Stage 2 base drift).**
  - #347 changes `IterateFindHost.lean` and `ModuleHost.lean` (DW-9 rows: 52 Stage 2 items).
  - Stage 1 (#355) changes those two, plus `Encryption/PublicKey/Trapdoor.lean` (6 items) and
    `InformationTheory/Entropy.lean` (3 items).
  - Line numbers in the derivative are at the issue base. The Stage 2 brief must re-derive them at its own base. Its gate
    re-seals every touched owner anyway.
  - The 23 F-01 rows (`IterateFind`, pending #347) are excluded from the derivative. Stage 1 is stacked on #347, so #347
    merges before Stage 2. The Stage 2 gate should confirm that `IterateFind` seals clean.
- **DW10-F14 (cosmetic).** C1-0328, C1-0335 and C1-0336 (`ColSimMachine`; `simp` with `Function.comp`, `Fin.divNat`,
  `Fin.modNat`) are FIXED_SINCE with `change` `-`. At the base these are core/Mathlib names, never TCSlib reads; the change
  text could say so. No status change.

## 7. Questions for Seyoon (recommended option first)

The worker's DW10-W1 to W7 are below. In each, (a) is what the inventory applied.

- **DW10-W1 (moved items).**
  - (a) A moved item whose failure is gone is FIXED_SINCE, with the move noted, and a moved item that still fails is
    CHANGED.
  - (b) Every moved item is CHANGED.
  - **Recommend (a).** FIXED_SINCE is defined by the failure. Moves are kept in `change`.
- **DW10-W2 (recorded under A, now fails only under B; 12 rows).**
  - (a) CHANGED ("now B-only"), classed SEAL-B-ONLY.
  - (b) FIXED_SINCE, plus a NEW B row.
  - **Recommend (a).**
- **DW10-W3 (controls where no reader is `rfl`-checkable; 29 owners negative-only, 2 with no candidate).**
  - (a) Record "no reader"; it is not seal debt and not Stage 2 work.
  - (b) Stage 2 adds definitional readers for these owners.
  - **Recommend (a).**
- **DW10-W4 (`show`/`change` reads not in the archived lexer).**
  - (a) Accept: the seals catch every such read.
  - (b) Extend the lexer in a later job.
  - **Recommend (a).**
- **DW10-W5 (file-level `failed to set [local irreducible]`; 14 rows in 7 files, incl. SEAL-0306/0307).**
  - (a) Not seal debt. The rows keep no class. The Stage 2 gate's seal harness skips, or reports separately, definitions
    an owner already makes locally irreducible. Otherwise the gate's "no seal failure in a touched file" target trips on
    them.
  - (b) Stage 2 drops the owners' own attribute lines.
  - **Recommend (a), with the gate rule.**
- **DW10-W6 (shadow transfers; 48 Stage 2 items, about 33 new readers in `GI`/`ColProofs`/`ColSimMachine`/`GIZK`).**
  - (a) Stage 2 bridges each main-file definition to its shadow (`X = GI.X` from the shadow's readers) and transports
    the results. This is proof-only, with no statement change. Open a duplication-ledger entry for retiring the shadows
    later.
  - (b) Retire the four shadow copies in Stage 2 and state the results once on the main definitions. This is a larger
    refactor.
  - **Recommend (a).**
- **DW10-W7 (lexer false positives from local `P` bindings; 4 items, C1-0284 among them).**
  - (a) Drop them; C1-0284 is FIXED_SINCE.
  - (b) Keep them as items with fix "none".
  - **Recommend (a).**

The questions below come from this review.

- **DW10-Q8 (the SEAL-B-ONLY list: 194 rows, 190 declarations; 51 of them statement-level under B, F01).**
  - (a) Treat `PolyExpr.eval` failures as recorded diagnostics with no fix, as the `FinDist` coercion is under Q3. This
    is consistent with its notation ruling of 2026-11-07.
  - (b) Fix the proof-level B-only items in Stage 2 and record the 51 statement-level ones.
  - (c) Fix all of them, with statement changes.
  - **Recommend (a).**
- **DW10-Q9 (the 3 STATEMENT rows, `host_dispatch`/`host_branch`/`host_halt`, F04).**
  - (a) They are resolved by Stage 1's `host_*_view` lemmas plus Stage 2's scheduled deletion of the host lemmas left
    unused by DW-5. No statement change is needed. The Stage 2 gate checks that they are gone.
  - (b) Keep them and change their statements (a freeze exception).
  - (c) Keep them as recorded debt.
  - **Recommend (a).**
- **DW10-Q10 (`Uniform.lean` in Stage 2's scope text, F12).**
  - (a) Q1 supersedes: `Uniform`'s 4 failures go to the Complexity handoff, and `cleanup-stages.md` is amended.
  - (b) Stage 2 clears them anyway.
  - **Recommend (a).**
- **DW10-Q11 (placement of the 2 provider readers in `Complexity/TuringMachine/Encoding.lean`; 17 owner items).** The two
  readers are `Turing.CodeTM.toFinTM_tm`, and the case equations of `Turing.pairDecode` (only `pairDecode_nil` is
  published).
  - (a) Stage 2 adds them additively in `Encoding.lean`, next to the definitions, as readers our owners need (Q1). The
    handoff chat is told.
  - (b) Hold the 17 items open until the Complexity handoff, after the campaign merge.
  - (c) Restate them as owner-side lemmas. This does not clear the seal: their proofs would read the sealed definition.
  - **Recommend (a).**

## 8. Stage 2 input (`stage2-seal-items.tsv`, `stage2-readers.tsv`)

**Selection.** Rows with class STAGE2 or STAGE2-PROVIDER-READER: 614. The 23 F-01 rows pending #347 are removed, which
leaves **591 items**.
- They cover 264 declarations and 290 work units (owner file × declaration × channel) in **56 owner files**: 54 T1 and
  2 T2.
- Out of scope: SEAL-B-ONLY (194, Q8), STATEMENT (3, Q9), STRICT-ONLY (31, Q3: no fix), the W5 rows (14) and HANDED-OFF
  (608).
- The F02 and F03 corrections are applied and marked `maintainer_correction`.

**Columns of `stage2-seal-items.tsv`.**
- Identity: owner file, tier, area, item id, source, channel, declaration, status, work unit.
- The read: `failing_read` (coe-A first error line, message class and providers, or the scan item).
- The fix: `fix_kind`, `new_readers`, `reader_homes`, `reader_statements`, the worker's `fix` text, `fix_confidence`,
  `w6_dependent`, `maintainer_correction` and `known_record`.

**Fix kinds:**

| fix kind | items |
|---|---|
| USE-PUBLISHED | 432 |
| ADD-READER | 104 |
| BRIDGE-SHADOW (W6) | 29 |
| ADD-PROVIDER-READER | 17 |
| PROOF-ONLY | 9 |

- 48 items depend on W6. 28 are needs-check (F06).

**By area** (Stage 2 items / work units):

| area | files | items | work units |
|---|---|---|---|
| Complexity/Randomized | 4 | 108 | 38 |
| Complexity/TuringMachine | 1 | 20 | 9 |
| Cryptography/Asymptotic | 13 | 117 | 57 |
| Cryptography/Candidates | 1 | 1 | 1 |
| Cryptography/Encryption | 5 | 27 | 12 |
| Cryptography/HardcoreBit | 1 | 5 | 2 |
| Cryptography/NumberTheory | 2 | 2 | 2 |
| Cryptography/Pseudorandom | 5 | 43 | 22 |
| Cryptography/ZeroKnowledge | 22 | 257 | 142 |
| InformationTheory | 2 | 11 | 5 |
| **total** | **56** | **591** | **290** |

- Complexity-directory owners (T1, campaign-created) hold 128 items. Of these, 52 are DW-9 (`ModuleHost`,
  `IterateFindHost`), and 12 in `PairSplit`/`UnaryMul` need the provider reader.
- All open rows by area and class:

| area | STAGE2 | PROVIDER-READER | SEAL-B-ONLY | STRICT-ONLY | STATEMENT | total |
|---|---|---|---|---|---|---|
| Complexity/Randomized | 119 | 12 | 3 | 0 | 3 | 137 |
| Complexity/TuringMachine | 20 | 0 | 0 | 0 | 0 | 20 |
| Cryptography/Asymptotic | 112 | 5 | 69 | 0 | 0 | 186 |
| Cryptography/Authentication | 0 | 0 | 16 | 0 | 0 | 16 |
| Cryptography/Candidates | 1 | 0 | 18 | 0 | 0 | 19 |
| Cryptography/Encryption | 27 | 0 | 19 | 0 | 0 | 46 |
| Cryptography/Foundations | 0 | 0 | 0 | 2 | 0 | 2 |
| Cryptography/Games | 0 | 0 | 0 | 1 | 0 | 1 |
| Cryptography/HardcoreBit | 5 | 0 | 0 | 0 | 0 | 5 |
| Cryptography/NumberTheory | 2 | 0 | 1 | 0 | 0 | 3 |
| Cryptography/Pseudorandom | 43 | 0 | 27 | 0 | 0 | 70 |
| Cryptography/Randomness | 0 | 0 | 0 | 16 | 0 | 16 |
| Cryptography/SecureComputation | 0 | 0 | 28 | 0 | 0 | 28 |
| Cryptography/ZeroKnowledge | 257 | 0 | 13 | 0 | 0 | 270 |
| InformationTheory | 11 | 0 | 0 | 12 | 0 | 23 |
| **total** | **597** | **17** | **194** | **31** | **3** | **842** |

**Per owner file:**

| owner file | tier | items | declarations | work units | use | add | provider | bridge (W6) | proof-only | needs check |
|---|---|---|---|---|---|---|---|---|---|---|
| Complexity/Randomized/Build/IterateFindHost.lean | T1 | 32 | 6 | 11 | 32 | 0 | 0 | 0 | 0 | 0 |
| Complexity/Randomized/Build/PairSplit.lean | T1 | 55 | 13 | 20 | 49 | 0 | 6 | 0 | 0 | 0 |
| Complexity/Randomized/Build/UnaryMul.lean | T1 | 19 | 4 | 5 | 12 | 0 | 6 | 0 | 1 | 1 |
| Complexity/Randomized/Primitives.lean | T1 | 2 | 2 | 2 | 2 | 0 | 0 | 0 | 0 | 1 |
| Complexity/TuringMachine/Build/ModuleHost.lean | T1 | 20 | 9 | 9 | 20 | 0 | 0 | 0 | 0 | 0 |
| Cryptography/Asymptotic/Collections.lean | T1 | 2 | 1 | 1 | 0 | 0 | 0 | 0 | 2 | 0 |
| Cryptography/Asymptotic/Ensembles.lean | T1 | 20 | 8 | 8 | 20 | 0 | 0 | 0 | 0 | 0 |
| Cryptography/Asymptotic/EnsemblesLemmas.lean | T1 | 11 | 10 | 10 | 11 | 0 | 0 | 0 | 0 | 3 |
| Cryptography/Asymptotic/GoldreichLevinDomain.lean | T1 | 2 | 1 | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| Cryptography/Asymptotic/HardCore/Functions.lean | T1 | 12 | 6 | 6 | 10 | 2 | 0 | 0 | 0 | 4 |
| Cryptography/Asymptotic/HardCoreCollection.lean | T1 | 14 | 6 | 6 | 14 | 0 | 0 | 0 | 0 | 0 |
| Cryptography/Asymptotic/HardCoreGL.lean | T1 | 8 | 4 | 4 | 6 | 2 | 0 | 0 | 0 | 0 |
| Cryptography/Asymptotic/HardCoreLemmas.lean | T1 | 2 | 1 | 1 | 2 | 0 | 0 | 0 | 0 | 0 |
| Cryptography/Asymptotic/OneWayYao.lean | T1 | 14 | 5 | 5 | 10 | 4 | 0 | 0 | 0 | 8 |
| Cryptography/Asymptotic/SamplingFinDist.lean | T1 | 3 | 2 | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| Cryptography/Asymptotic/Universal.lean | T1 | 14 | 4 | 4 | 9 | 0 | 5 | 0 | 0 | 0 |
| Cryptography/Asymptotic/UniversalLemmas.lean | T1 | 5 | 3 | 3 | 5 | 0 | 0 | 0 | 0 | 0 |
| Cryptography/Asymptotic/UniversalPadding.lean | T1 | 10 | 4 | 4 | 5 | 5 | 0 | 0 | 0 | 0 |
| Cryptography/Candidates/Concrete.lean | T1 | 1 | 1 | 1 | 0 | 1 | 0 | 0 | 0 | 0 |
| Cryptography/Encryption/PublicKey/EnsembleSecurity.lean | T1 | 10 | 4 | 4 | 10 | 0 | 0 | 0 | 0 | 0 |
| Cryptography/Encryption/PublicKey/Hybrid.lean | T1 | 5 | 2 | 2 | 4 | 0 | 0 | 0 | 1 | 2 |
| Cryptography/Encryption/PublicKey/HybridMachine.lean | T1 | 2 | 1 | 1 | 2 | 0 | 0 | 0 | 0 | 0 |
| Cryptography/Encryption/PublicKey/Trapdoor.lean | T1 | 6 | 3 | 3 | 0 | 6 | 0 | 0 | 0 | 0 |
| Cryptography/Encryption/PublicKey/TrapdoorPredictor.lean | T1 | 4 | 2 | 2 | 0 | 0 | 0 | 0 | 4 | 2 |
| Cryptography/HardcoreBit/InnerProduct.lean | T2 | 5 | 2 | 2 | 5 | 0 | 0 | 0 | 0 | 0 |
| Cryptography/NumberTheory/Chebyshev.lean | T1 | 1 | 1 | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| Cryptography/NumberTheory/Primality.lean | T1 | 1 | 1 | 1 | 1 | 0 | 0 | 0 | 0 | 1 |
| Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Reduction.lean | T1 | 7 | 4 | 4 | 4 | 3 | 0 | 0 | 0 | 0 |
| Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Run.lean | T1 | 18 | 8 | 8 | 6 | 12 | 0 | 0 | 0 | 0 |
| Cryptography/Pseudorandom/Generators/Asymptotic/Defs.lean | T1 | 7 | 5 | 6 | 4 | 3 | 0 | 0 | 0 | 0 |
| Cryptography/Pseudorandom/Generators/Asymptotic/FromPermutation.lean | T1 | 3 | 1 | 1 | 0 | 3 | 0 | 0 | 0 | 0 |
| Cryptography/Pseudorandom/Generators/Asymptotic/Stretch.lean | T1 | 8 | 3 | 3 | 4 | 4 | 0 | 0 | 0 | 0 |
| Cryptography/ZeroKnowledge/Commitment.lean | T1 | 13 | 5 | 5 | 9 | 4 | 0 | 0 | 0 | 0 |
| Cryptography/ZeroKnowledge/CommitmentLemmas.lean | T1 | 6 | 6 | 6 | 3 | 2 | 0 | 0 | 1 | 2 |
| Cryptography/ZeroKnowledge/Defs.lean | T1 | 16 | 6 | 6 | 16 | 0 | 0 | 0 | 0 | 0 |
| Cryptography/ZeroKnowledge/EncodingPermutations.lean | T1 | 7 | 4 | 4 | 5 | 2 | 0 | 0 | 0 | 0 |
| Cryptography/ZeroKnowledge/GraphIsomorphism.lean | T1 | 33 | 16 | 16 | 13 | 0 | 0 | 20 | 0 | 0 |
| Cryptography/ZeroKnowledge/GraphIsomorphism/Concrete.lean | T1 | 4 | 2 | 3 | 2 | 2 | 0 | 0 | 0 | 0 |
| Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRep.lean | T1 | 4 | 4 | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRepGI.lean | T1 | 3 | 2 | 2 | 3 | 0 | 0 | 0 | 0 | 0 |
| Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean | T1 | 7 | 2 | 2 | 7 | 0 | 0 | 0 | 0 | 0 |
| Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean | T1 | 13 | 5 | 5 | 11 | 2 | 0 | 0 | 0 | 0 |
| Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean | T1 | 9 | 3 | 3 | 9 | 0 | 0 | 0 | 0 | 2 |
| Cryptography/ZeroKnowledge/GraphIsomorphismZK.lean | T1 | 6 | 5 | 5 | 5 | 0 | 0 | 1 | 0 | 0 |
| Cryptography/ZeroKnowledge/GraphIsomorphismZK/Closeness.lean | T1 | 18 | 8 | 8 | 6 | 12 | 0 | 0 | 0 | 0 |
| Cryptography/ZeroKnowledge/GraphIsomorphismZK/Simulator.lean | T1 | 8 | 4 | 4 | 4 | 4 | 0 | 0 | 0 | 0 |
| Cryptography/ZeroKnowledge/InteractiveProofs.lean | T1 | 10 | 5 | 7 | 9 | 1 | 0 | 0 | 0 | 0 |
| Cryptography/ZeroKnowledge/NP.lean | T1 | 7 | 3 | 3 | 7 | 0 | 0 | 0 | 0 | 0 |
| Cryptography/ZeroKnowledge/NPLemmas.lean | T1 | 15 | 9 | 10 | 15 | 0 | 0 | 0 | 0 | 0 |
| Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean | T1 | 16 | 8 | 8 | 6 | 2 | 0 | 8 | 0 | 0 |
| Cryptography/ZeroKnowledge/ThreeColoring/ProtocolProofs.lean | T1 | 11 | 4 | 4 | 4 | 7 | 0 | 0 | 0 | 0 |
| Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean | T1 | 17 | 8 | 8 | 8 | 9 | 0 | 0 | 0 | 2 |
| Cryptography/ZeroKnowledge/ThreeColoring/SimulatorMachine.lean | T1 | 14 | 14 | 14 | 4 | 10 | 0 | 0 | 0 | 0 |
| Cryptography/ZeroKnowledge/ThreeColoring/SimulatorNumeric.lean | T1 | 20 | 10 | 15 | 18 | 2 | 0 | 0 | 0 | 0 |
| InformationTheory/Entropy.lean | T1 | 3 | 3 | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| InformationTheory/LeftoverHash.lean | T2 | 8 | 1 | 2 | 8 | 0 | 0 | 0 | 0 | 0 |
| **total (56 files)** | | **591** | **264** | **290** | | | | | | |

**New readers (`stage2-readers.tsv`, deduplicated across rows).** There are **74**: 63 in T1 files, 9 in T2 files and
**2 in a handed-off Complexity file** (Q1 flag; Seyoon decides placement, DW10-Q11).
- The two flagged readers, in `TCSlib/Complexity/TuringMachine/Encoding.lean`:
  - `Turing.CodeTM.toFinTM_tm`: 5 items in `Asymptotic/Universal.lean`;
  - the case equations of `Turing.pairDecode`: 12 items in `Randomized/Build/PairSplit.lean` and `UnaryMul.lean`.
- `Complexity.polyTimeComputable_iterateFind_elim` lands in `Complexity/Randomized/Repetition.lean`. That file is T1
  (campaign-created), so it is not a Q1 case.
- 33 readers are W6-dependent: the `GI.*`, `ColProofs.*`, `ColSimMachine.*` and `GIZK.*` bridge readers.
- 28 lack a concrete statement (F07). The `statement_complete` column marks them.
- Columns: reader, home, home tier, Q1 flag, statement, `statement_complete`, `w6_dependent`, fix kinds, owner files,
  item count, item ids.
- The reader names and homes come from the worker's fix text by a parser (`evidence/scripts/stage2.py`) and were checked
  by hand.
  - Unqualified names are qualified by their definition's namespace.
  - "next to X" resolves to X's file.
  - Readers that already exist are dropped, since they are uses.

## 9. Evidence

`dw10-final-r1-review-evidence.zip` (beside this file; its SHA-256 is in `evidence-SHA256SUMS`) holds:
- the review scripts: integrity, seal recount, probe/source and dedup check, re-attribution, header test, reconciliation,
  spot dump, reader-name check, Stage 2 derivation;
- their outputs: `spot.txt` (the 46-row dump), `stmtcheck.txt` (the header test, F01), `s2summary.txt`, `logcounts.json`
  (per-run error counts) and `reattr.json` (the independent attribution of the 1,882 error lines).

The scratch extraction is outside the records.
