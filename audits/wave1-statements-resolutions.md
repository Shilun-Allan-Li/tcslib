# Wave-1 statement gate (§12.8b, §12.10, §12.11): resolutions (CLOSED, round 2)

## Round 1 (2026-10-11): 0 blockers, 2 majors, 6 minors, 42 notes

Round 1 (`audits/wave1-statements-findings.md`, verbatim) returned **FAIL: 0 blockers, 2 majors,
6 minors, 42 notes**. All 26 sorried statements were found **true as stated**, with adequate
consumers and no vacuity. The two majors are about evidence and duplication accounting. The
repairs are on the statement branch at `b47992fd` (PR #43), which is the round-2 object. The
round-2 pack is `audits/wave1-statements-r2-pack.md`.

## User decisions (2026-10-11)

- **Finding 2: factor all three now.** The copied split argument and both disclosed mirrors
  are replaced by shared public lemmas. Acknowledging them as debt was the alternative not
  taken.
- **Note 45: both §12.10 scope exceptions accepted.**
  - The oracle-call layer is **time-only**: the oracle model has no space measure, and every
    named oracle consumer is a time class. This is an exception to the §12/§13 space mandate.
  - **W2-C (`FinOracleNDTM.exists_choiceTM`) stays public with one named customer.** It is the
    core of a relativized Theorem 2.6. This is an exception to the two-customer rule of
    admission.

## Majors

| # | Disposition |
|---|---|
| 1 | **Accepted; repaired in the packet.** The round-1 bundle was built before PR #42 (stream A) merged, so it attached a pre-A `Catalog.lean`, while the pack called Part 3 proved. The branch now merges the campaign tip `4aafe9e4`, which contains #42, and the round-2 bundle attaches the dependency sources at the round-2 head. A maintainer admission walk at that head lists, for every row the 26 statements' sketches cite, its sorry sources. The remaining fill prerequisites are named exactly: R8.0b `counterLoopTMVia` and R8.6 `expandTM_run_ofCfg` (PR #38, held for its own gate), and `exists_recordStepTM` (C continuation, issued in PR #45). The other §12.8 rows the sketches cite are proved. |
| 2 | **Accepted; factored** (user decision above). New module `TuringMachine/ChoiceWords.lean` with five publics: `append_split_unique`, `certificateLength_strictMono`, `expCertificateLength_strictMono`, `choiceBudget_le`, `run_take_of_halted`. `Oracle.lean` gains the public `OracleTM.step_radius` and `OracleTM.runFrom_radius`. The changes, file by file, follow this table. **No statement changed anywhere.** |

The changes for finding 2:
- **`Build/CertShell`:** `certificateShell_proj` cites the shared split.
- **`ClassNP/Nondeterminism`:**
  - the private `certificate_split_strictMono`, `certificate_split_unique`,
    `choice_budget_le`, `e3_split_strictMono` and the one-line wrapper `e3_split_unique`
    are removed, and their call sites re-pointed;
  - `acceptsWithin_iff_of_halts` is re-derived from the shared lemmas.
- **`Build/OracleSim`:** `mem_iff_exists_choiceOut` cites `choiceBudget_le` and
  `run_take_of_halted`, and W2-0 cites `runFrom_radius`.
- **`Oracle.lean` and `OracleNondeterministic`:** the private initialized invariant and
  `runWith_headBlank` are re-derived from `step_radius`/`runFrom_radius`.

The exponential certificate-length monotonicity moved with its polynomial sibling. Moving
only the polynomial one would have turned their old in-file pair into a new cross-file pair
(84%). One pre-existing in-file pair still becomes cross-file: `a3n_unpad_EXP` (Nondeterminism)
reproducing `expCertificateLength_strictMono` at 63%, which the base screen also shows at
63%. The shared text is one monotone-power inequality inside an unrelated padding proof, and
the round-2 pack puts it to the auditor.

## Minors

| # | Disposition |
|---|---|
| 3 | **Accepted.** `exists_tableFindTM`'s sketch now escapes **before** skipping an accepted final field, and names the explicit-verdict-bit alternative. A permanent sanity case for the last matching entry is in the §12.8b probe (`m = 1`, `h = [1]`, `es = [[[2]]]`: `findIdx? = some 0`, offset 2 nonblank, end offset 4 blank). Comment-only. |
| 4 | **Accepted.** `exists_choiceTM`'s docstring qualifies the query trace: at exhaustion on `N`'s query state the host may submit a final query and discard its answer. The I/O statement is the contract and is unchanged. |
| 5 | **Accepted.** `exists_polyCanonizer`'s sketch adds the zero-guard case: a grammar-derived necessary check `(4k + 5)·3^(k+1)·(n + 1)`, run in binary with fail-fast on an exhausted suffix, and early rejection yielding the fallback. No new `MachineFormat` hypothesis. Comment-only. |
| 6 | **Accepted.** The round-2 screen population is listed exactly in `audits/logs/wave1-statements-r2-screen-population.txt`. It adds the omitted direct imports `Build/Primitives` and `ClassP/DTIME`, the four `Universal*` interpreter files, `ClassNP/Nondeterminism` (also attached to the bundle) and `ChoiceWords`. |
| 7 | **Accepted.** `POracle_EXPCOM_subset_EXP'` is a probe-local derived inclusion: no campaign declaration of that name exists. The round-2 pack says so. The six `rfl` identities are as listed. |
| 8 | **Accepted.** The four private lemmas of `CodeSimulator` (`fin_cons_one`, `fin_cons_two`, `oneTape_skipTable_eq`, `oneTape_serialize_eq`) now have docstrings. Comment-only. |

## Notes carried forward (binding on the fills unless stated)

- **11.** Fill `fieldOffset_length` by `(length_joinFields_add_one fs hfs).symm`; no new layout
  induction.
- **25.** Append with empty new fields need not preserve `TableWF`. Consumers that seek again
  must append nonempty record and flag fields. This is covered by a sanity case in the §12.8b
  probe.
- **26.** The template's extra increment is `incrementTM` plus a one-cell overflow extension;
  await the expansion and transport prerequisites (#38).
- **39.** S1b's fill brief must make the phase bookkeeping explicit: mark the selected flag
  while its location is known, and rewind to the table origin before table-wide find/append.
- **44.** The InputLength fill records the future factoring against Catalog's private
  `f2_counterTM` in its ledger entry. No counter proof is copied now.
- **46.** File size is not a driver (user, 2026-10-11). `RecordTable`'s size is reported at
  fill, and any split serves reuse, not size.
- **47.** The generic writer `tableBitsK` against the frozen serializers stays in the existing
  item-8 residual family, with its bridges. It is not a new debt.
- **49.** Execution, freshness and final-head provenance are maintainer attestations. Round 2
  binds every attachment to the round-2 head, with a user-run replay at it.
- **50.** Permanent sanity cases:
  - **now, in the §12.8b probe:** the last matching table entry and the empty-field append;
  - **at fill, in each fill's evidence:** empty-`T` enumeration (recordNext), zero-guard huge
    headers (canonizer), exact-deadline acceptance (H1) and query-word exhaustion (W2-C).

All other notes record verified truth or adequacy and need no action.

## Round 2 (2026-10-11): 0 blockers, 0 majors, 2 minors, 18 notes

The findings are verbatim in `audits/wave1-statements-r2-findings.md`; the pack is
`audits/wave1-statements-r2-pack.md`. The auditor:

- found the five `ChoiceWords` statements and the two `Oracle.lean` radius statements true at
  the required generality (notes 3–6);
- confirmed that the three factored families are consumed by citation, closing round-1
  major 2 (notes 7, 8, 13);
- confirmed the repaired readiness evidence, closing round-1 major 1 (note 9);
- reproduced the broadened screen's delta and all seven added matches (note 10), and accepted
  the `a3n_unpad_EXP` exclusion and the writer-residual classification (notes 11, 12);
- confirmed the round-1 minor repairs (notes 14–16) and the axiom census (note 18).

| Finding | Disposition |
|---|---|
| 1 (minor): the 95-name readiness walk omits four names cited with arguments inside code spans | **Fixed.** `ReadinessWalk.lean.txt` now covers 99 names: the auditor's four are added. A token-level re-extraction finds no others. Rerun read-only against the round-2 replay tree (`audits/logs/wave1-statements-r2-close.log`): 92 proved, `expandTM_run_ofCfg` sorried (R8.6, closed by PR #38), 6 not constants in the closure. The four new names are proved |
| 2 (minor): the design, its extract and the §12.10 probe's comments contradict the repairs | **Fixed.** `machine-library-design.md` §12.10 and `audits/evidence/wave1-statements/design-sections.md` now list the three families as factored, naming the shared lemmas, and state the consumer identities exactly: six `rfl` identities, with the deterministic inclusion `POracle_EXPCOM_subset_EXP'` probe-local. The probe's comments now say the same. They also record that the cited input call and the original controls (`compareTM_run_ofCfg`, `exists_inputSeekTM`) are proved, and that `EXP_subset_POracle_EXPCOM` is the live control. The probe's code is comment-stripped identical, and its rerun output is identical apart from line numbers. **Erratum** to the round-2 probes log: its header names the former controls as `compareTM_run_ofCfg` and `exists_inputCallTM`. They were `compareTM_run_ofCfg` and `exists_inputSeekTM`; `exists_inputCallTM` was the cited row. The shipped log is kept unchanged under the archival rule |
| 15 (note): consumers that seek after an empty-field append must keep the nonempty-field invariant | **Carried forward**, binding on the §12.8b fill brief when it issues |
| 16, 20 (notes): keep the recorded fill obligations (exhaustion, zero guard, the four deferred sanity cases, S1b bookkeeping) | **Retained**, as round 1's note 50 and the S1b obligations |
| 17 (note): keep a detecting control when `EXP_subset_POracle_EXPCOM` is filled | **Carried forward**, binding on B5's fill brief when it issues; the probe comment now says so |
| 19 (note): historical equality and execution provenance remain maintainer attestations | **Recorded**, as round 1's note 49 |
| 3–14, 18 (notes) | Confirmed. No action |

**Gate CLOSED. PR #43 is clear to merge.** It has no Lean dependency on PR #38: the
statement modules cite R8.0b's `counterLoopTMVia` and R8.6 only in docstrings.
