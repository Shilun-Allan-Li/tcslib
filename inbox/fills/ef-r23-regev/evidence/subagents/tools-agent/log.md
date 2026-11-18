# tools-agent log (sub-agent of fill ef-r23-regev)

Role: check tools (Python and bash) for the lead. Date 2026-11-18.

- I ran no Lean, no `lake` and no `lean`.
- I made no git writes. I used only `git show`, `ls-tree`, `cat-file`, `grep`, `diff`, `log`, `rev-parse` and
  `merge-base` in `/home/user/ef-r23/repo`.
- I wrote only under `/home/user/ef-r23/tools/agent/` and `/home/user/ef-r23/evidence/subagents/tools-agent/`.
- Python always ran as `python3 -I`. Syntax checks used `tools/agent/pycheck.sh`, the builtin `compile()`, which
  writes no `__pycache__`. `python3 -I -m py_compile` refuses `cfile=/dev/null` and would otherwise write
  bytecode next to the tools.
- Inputs: the repo at head `daaf5e65f` (series 1+2), base `5ed465f6`, PR #377 `7563734a`,
  `origin/cleanup/stage2-s2a` (`c119a3c4`), and the bb1m reference tools under `/home/user/ef-r23/tools/bb1m-*`.

## 1. Rule-10 driver: `tools/agent/rule10_regev.sh`

- **Origin:** bb1m `drivers/rule10_final.sh` + `seal/rule10_b.sh`. The header lists adaptations (1)-(9).
- **Verbatim copies** (sha256-identical to bb1m, checked): `seal/review/{mkcollect.py, NmCollect.template.lean,
  mkseals_ab.py, mkseals_coe.py, sealsum.py, ctlcheck2.py, touched.py}` and
  `seal/review/archived-gate10-tools/*`.
- **New runner** `seal/runner_regev.py`, from bb1m `runner_full.py`:
  - The `flock` is removed. At most `$RULE10_JOBS` (default 2) `lean -DmaxErrors=0` processes run at once, with
    no `-o`. The records format is unchanged, plus a `jobs` field.
  - `$LAKE_PACKAGES` defaults to `/home/user/ef-r23/repo/.lake/packages`.
  - `DRY=1` prints the commands.
  - **Bug found and fixed in my first version:** dropped `Popen` objects let `subprocess`'s own cleanup reap a
    child before `os.wait4`, which lost one record. The `Popen` objects are now kept alive.
  - Self-test with a FAKE `lean`, a script under `dryrun/runner-fake/home/.elan/bin` that runs no Lean:
    - JOBS=2: at most 2 run at once, all 5 records written, `Bad` has rc 1 and errors 1.
    - JOBS=1: strictly sequential.
- **Probe locations:**
  - Probes are written outside the repository, under `PROBE_ROOT` (default `/home/user/ef-r23/probes/<basename
    of evidence dir>`), as absolute probe paths.
  - `mkseals_*.py` and `mkctl` accept them unchanged, because pathlib joins an absolute subdir as itself.
  - Log names are `<abs path with / -> _>.log`, used consistently by the runner, `sealsum.py`, `ctlcheck2.py` and
    the driver (`collector log:` in `print-env`).
- **Phases:**
  - `print-env`
  - `collect`: generates the collector and prints the exact commands.
  - `collect-run`
  - `collect-check`
  - `pretest`: coe seal A, controls, unsealed `ControlU_*` only, plus `ctlcheck2` on the unsealed half of the plan.
  - `seals`: `touched.py` writes `statements/touched-after.json`, then strict and coe seals A/B (B with
    `SEAL_EVAL=1`), paired controls strict and coe, one runner pass, `sealsum` ×4 and `ctlcheck2` ×2.
- **Dry run without Lean** (`dryrun/`), with a clearly MOCK collector log from `selftest/mock_collector.py`
  (invented CAT/CLOSURE/ROOT records):
  - `collect`, `collect-check`, `pretest` and `seals` ran with `DRY=1`.
  - All Python steps worked on the real sources at `daaf5e65f`. `instrument()`'s byte-preservation assertion
    passed for all 4 owners × 4 seal variants.
  - The run produced 8 control probes with 30 expected sealed failures, and 34 printed lean commands.
  - Output: `dryrun/collect.out`, `dryrun/dry-phases.out`, `dryrun/rule10-dry/`, `dryrun/probes/`. The seal probe
    `.lean` files there are instrumented REAL sources with MOCK request sets. They are not evidence, so delete
    them freely.

## 2. Controls generator: `tools/agent/mkctl_regev.py` + `control-rows.tsv`

- **Origin:** bb1m `mkctl_bb1m_readers.py`. The harness, `assemble`, the covering-subset rule and the plan format
  are verbatim. Adaptations:
  - Rows come from a TSV (`CTL_ROWS` overrides).
  - The namespace is `RegevControls`.
  - It refuses duplicate control names, empty row files, and an owner column that differs from the record's
    `home`.
  - It writes `UNCOVERED` lines and `coverage.tsv`. With `CTL_REQUIRE_ALL=1`, an uncovered target exits 3
    (tested).
  - Optional `CTL_OWNERS` restricts the candidate consumers (tested: it moves the series-1 controls into the
    Symmetric.Regev.Asymptotic probe).
- **Nine rows** (series 1: `addMod`, `vecAddStep`, `vecAddModWords`, `subsetSumStep`, `subsetSumModWords`,
  `modContext`; series 2: `shiftAdvice`, `shiftPre`, `shiftAdviceBound`):
  - Negative: `theorem ctlX <binders> : type_of% (<reader> args) := rfl`. Positive: the same statement with
    `:= <reader> args`.
  - Readers: the `*_eq` lemmas, `modContext_eq`, `shiftAdvice_eq`, `shiftPre_eq` and `shiftAdviceBound_eval`.
    Binders were copied from the two Lean files; names are fully qualified and need no `open`.
  - `unfold`/`simp [f]` are deliberately NOT used as negatives: equation lemmas ignore `irreducible`, so they
    would pass sealed.
- **Covering subset in the mock:**
  - The series-1 targets went to the facade `Encoding` probe and the series-2 targets to the facade
    `Symmetric.Regev` probe, because they have the fewest requests.
  - The real choice depends on the real collector.
  - Series-2 targets are exercised only if a consumer of `Symmetric.Regev.Asymptotic` is a sealed owner (the
    facade, or series 3's `PublicKey.Regev.Asymptotic`).

## 3. Clash scan: `tools/agent/clash/clash_scan.py`

- **Origin:** bb1m `clash/clash_scan.py` + `clash_controls.py`. The bb1m parser is used verbatim as
  `clash/clash_core_bb1m.py` (sha256 identical, `5e4cd3f4…`).
- **Names input:** a names file (StmtDump text or TSV). It is cross-checked against bb1m's git-diff-derived
  declarations over the six fill paths.
- **Full-name check** in four trees: base, #377, stage2-s2a, and head-minus-fill.
- **Same-short-name report** with `path:line`.
- **Downstream report:** the reverse import closure of the fill modules at head (over `TCSlib/`, `audits/` and
  `TCSlib.lean`), plus unqualified-use lines (code with comments and strings blanked).
- **Controls K1–K7** (`clash/clash-controls.out`): **ALL_CONTROLS_OK True**. They cover a planted existing name
  → CLASH in all trees, namespace resolution, a fresh name, same-short-name INFO, the unqualified matcher, the
  import closure, and a planted head duplicate.
- **Provisional run** (`clash/provisional-s12/`), using diff-derived names (`clash/names-s12-provisional.tsv`)
  because the StmtDump is not available yet:
  - RESULT: 47 names, 0 clashes, 0 short names declared elsewhere in the 4 trees. Spot-checked by `git grep`.
  - Cross-check: 0/0.
  - Importers at head (7): `TCSlib.lean`, `Encoding.lean`, `Encryption.lean`, `PublicKey.lean`,
    `Symmetric.lean`, `Symmetric/Regev.lean`, `Symmetric/Regev/Asymptotic.lean`.

## 4. Frozen-facade check (C7): `tools/agent/frozen/frozen_check.py` + `frozen-allow.json`

- **Origin:** bb1m `headers/frozen/`, with the method kept: revert the permitted edits, then require byte
  equality.
- **Additions:**
  - The allow-list is JSON. It gives an exact base anchor plus exact lines, or a pattern for the series-3
    PublicKey bullet.
  - difflib hunk counting, MISSING insertions, the 100-character width limit, and a declaration-list
    comparison.
  - `git diff --stat` and `--name-status` against the six paths (A for new modules, M for facades).
  - PENDING for an unchanged facade; `--final` makes it FAIL.
- **Run at `daaf5e65f`** (`frozen/s12/frozen-check.out`):
  - RESULT PASS.
  - Encoding and Symmetric/Regev: PASS (0 differences, reverted == base). PublicKey/Regev: PENDING.
  - diff-stat: 4 paths, none outside the six.
  - `--final` exits 1, as expected until series 3.
- **Controls** (`frozen/s12/frozen-controls.out`): M0–M7 on each facade, with a synthetic head for the PublicKey
  facade. **ALL_CONTROLS_OK True**.
  - M1: one altered character elsewhere gives exactly 1 difference.
  - M2: one altered character in the bullet gives 1 difference and 1 missing.
  - M3: an extra line gives 1 difference.
  - M4: a dropped import gives 1 missing.
  - M5: a moved import gives 1 difference and 1 missing.
  - M6: a deleted line gives 1 difference.
  - M7: an added declaration gives at least 1 difference and declarations ≠.

## 5. Overlap: `tools/agent/overlap_search.sh` (run 2026-11-18)

- Outputs are in `overlap/`: `search.log` (each command verbatim, its hit count and up to 60 hits),
  `run-summary.txt` (one line per search) and `overlap.md`.
- **Result:** no duplicate at base or #377.
- **Near relatives:**
  - The dyadic analogues `DyadicArithmetic.addPoly`, `DyadicLinearAlgebra.dotWords`/`matVecPoly`.
  - `BinArith.mod`/`add` in `Div.lean`.
  - `Realization.lean`'s realizesOn API.
  - `coinsCongr` and `EnsembleLemmas.acceptProb_coins_equiv`. Pre-existing duplicate copies are in
    `ReductionSupport.lean:221` and `NextBit.lean:86` (private).
  - `FromPRG.lean`'s worst-message advice.
  - #377's GSW `ReductionEfficient` (hypothesis A4) versus the proved `exists_shiftMachine` here.

## Not done or not possible here

- I ran no Lean, so nothing about the Lean behaviour of the controls is verified. In particular, it is not
  verified that each `rfl` negative passes unsealed. The `shiftAdviceBound` row also needs `PolyExpr.eval` to
  reduce by defeq; the pretest decides.
- The real collector, seals and controls must be run by the lead.
- The clash scan still needs the lead's StmtDump names file. The provisional run used git-diff-derived names.
- Series 3 (PublicKey.Regev.Asymptotic and its facade) is not written yet. It needs:
  - `owners-s123.txt` (provided);
  - new rows appended to `control-rows.tsv`;
  - the `pk-bullet` pattern in `frozen-allow.json` replaced by exact lines (optional);
  - a re-run of `clash_scan.py` / `frozen_check.py --final` / `overlap_search.sh` on the new head.
