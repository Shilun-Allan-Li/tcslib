# NOTES: the copy-text screen's basename defect (ARM gate R2-7)

Base: the campaign tip `cd450a526e71a5e437ebe84245ea958bf309eda1` (`origin/complexity/arora-barak-ch3-4`),
read-only. At the tip, `audits/evidence/retrofit/copy-text-screen.py` (v1, SHA-256 `39ce5102…c0292`)
is unchanged since it was added in `841122fc`, so every recorded screen ran this exact script. All
outputs are under `$S/screenfix/`. No Lean was run.

## Resume check

- When the work resumed, no screen process of mine was running.
- One file was half-written: `runs/arm-full-v2.txt` (0 bytes, no `.meta`; killed when the session
  was interrupted). I deleted it and re-ran it alone under `nice -n 10`. Every other output has its
  `.meta` (rc=0).
- Before the CPU rule arrived, screens ran in parallel and without `nice`. Since resuming, they run
  one at a time under `nice -n 10`.
- Two writes went outside the folder, both removed at once: a scratch `/tmp/x` holding only
  basenames, and a header digest written beside `screenfix/` and then moved into it.

## Diagnosis (v1)

- **Line 62** keys each declaration on `f.split('/')[-1]`, the basename.
- **Line 66** skips a pair when `(basename, name)` coincide.
- **Line 69** prints the basename labels.
- **What is lost:** exactly the pairs whose two declarations have the same name, sit in two
  different files and share a basename. They are never compared.
- **Same basename, different names:** reported, but both sides carry the same label.
  `tools/screendelta.py`'s cross-file test compares labels, so it counts such a pair as in-file.
- **True self-pairs** (a declaration with itself) are excluded correctly.
- **Duplicate paths:** a path listed twice is screened twice, and every pair it is in is
  double-counted.
- **Residual, in v1 and v2 alike:** two distinct declarations in one file with the same
  *extracted* name are never compared. Examples are the same name in two namespaces, and
  anonymous instances, whose "name" is the next token (e.g. `{k`).

## The fix: `copy-text-screen-v2.py` (SHA-256 `967b750d…0b8c64`; `v1-to-v2.diff`)

- **Keying:** each declaration is keyed on its normalized repository-relative path. Duplicate
  arguments are dropped. A pair is skipped only when `(path, name)` coincide.
- **Labels:** the basename when it is unique in the argument list, the repository path
  otherwise.
- **Output:** the format is otherwise unchanged. `tools/screendelta.py` and `tools/pairdiff.py`
  parse it unchanged.
- **Equivalence:** when all basenames are distinct, path to basename is injective. So the skip
  test, labels, tuples, sort and totals are identical, and the output is byte-identical to v1's.
  This was checked by `cmp` on six populations, each with v1's rerun also equal to the committed
  log:

  | Population | Commit |
  |---|---|
  | B5a cont3 | `efe6ba6a` |
  | W1 cont3 | `efe6ba6a` |
  | fills-8 head | `8348bed7` |
  | fills-8 base | `385d6e5a` |
  | K1 | `782a9118` |
  | B7 bin | `50678912` |

  Summary: `runs/equivalence-summary.txt`.
- **Regression control:** `regression-control.sh <old> <new> <empty-dir>` builds `Codec/Machine.lean`
  and `ExpBFS/Machine.lean` sharing `shI`. The old screen gives 2 pairs and no `shI`; the new one
  gives 4, with `shI` both ways at 100%. It reports PASS, exit 0 (`runs/regression-control.out`).
  With the old screen in both roles it fails, exit 1.
- **Caveat:** v2's labels differ from the flattened workaround's (`TCSlib__…`). A v2 after-screen
  compared against a flattened base shows every pair as new or gone, so re-run such a base with v2.
  `compare_runs.py` can also map the labels.

## Assessment (`assessment.tsv`; inventory in `distinct-populations.tsv`, `logmap.tsv`)

- **Scope:** 57 distinct screen populations: 44 from population files, brief and bundle commands
  and log headers at `2c3c975a`; 7 more from logs, bundles and v1's declaration census at the
  logged commit; 6 recorded since `2c3c975a`.
- **Basename collisions:** 7 of them have them.

| Screen | Files | Collision | How it was run | v1 rerun = log | Pairs v1 drops | Verdict |
|---|---|---|---|---|---|---|
| C1 batch D (before, after, agent) | 16 | `Reductions` | v1 on paths | yes ×3 | 0 | unaffected |
| ARM full | 210 | 10 basenames | flattened | yes | 17 (13 ≥90%), recorded | unaffected |
| ARM supplement | 77 | 4 | flattened | yes | 17, recorded | unaffected |
| ARM added only (rounds 1 and 2) | 73 | 4 | flattened | yes | 17, recorded | unaffected |
| §13d G2–G4 before (`f2d48ad5`) | 3 | `Catalog` (Build, Contract) | v1 on paths | yes | 0 | unaffected |
| §13d G2–G4 after (landed forms) | 5 | `Catalog` | v1 on paths | yes | 0 | unaffected |
| Record tables cont5 (`1b6b972c`) | 43 | `Catalog`/`Embed`/`Seam` | flattened | v2 = log (2,428 pairs) | 0 | unaffected |

- **The 17 ARM pairs**, all among the added files: `shI` ×2, `cpI` ×6, `dmI` ×2 and `mvI` ×2
  (all 100%), `cp_run` 93% and 83%, and `Bd.toV` 81%, 68% and 50%. They span
  `SavitchARM`/`ExpBFS`/`TQBFARM` `Machine` and `Run`.
- **Why they are recorded:** the gate ran on flattened copies. On repository paths v1 would have
  given 4,102 pairs instead of 4,119. One further ARM pair is labelled as if in one file:
  `Machines/Parse::jeqPlain_run` ← `Codec/Parse::pe_getD_snd`, 75%.
- **No pair between same-basename files:** C1d, §13d and cont5 have none at all. So §13d's
  "cross-file 0" stands.
- **ARM full v2** (repository paths, `8c23f3bc`, 2,252 s niced): 4,383 / 4,119 / 1,092,862, the same
  pair multiset as the committed flattened log. v2 reproduces the workaround exactly.

## Residual finding (not the basename defect)

- **The pair:** `Build/CfgRecord.lean` lines 1249 and 1255. These are the anonymous
  `Fintype (recordStepPhase i)` and `DecidableEq (recordStepPhase i)` instances, with the same
  66-character body. They form a 100% in-file pair both ways that v1 and v2 never compare.
- **Origin:** added by `5a460237`, s12.8 fill C continuation 1.
- **What the gate recorded:** `s12-8-fill-C-cont-integration.md` records 689 → 690 and "New
  copies: none". The occurrence-keyed counts are 689 → 692 (with Primitives, 1,363 → 1,366), and
  the brief's "≥ 90% is a copy" applies.
- **Later screens:** every later population containing CfgRecord carries the pair on both sides,
  so it is never reported as new.
- **Scope:** across the 252 files of the populations at `2c3c975a`, and the B5a canon cont3
  (`9d441a4e`), record tables cont5 and §13d trees, this is the only such pair (`samename.py`).
- **Why v2 keeps the old behaviour:** keying on occurrence would break byte-equality on every
  recent population.

## Recommendation

1. **Replace v1 by v2** (or commit v2 beside it) and run `regression-control.sh`.
2. **Retire the flatten wrappers** (`flat-screen.sh`, `flatscreen.py`) for new screens. Re-run any
   flattened base with v2 before diffing.
3. **No ledger correction for the basename defect.** No recorded screen lost a pair. The only
   population where v1 on paths would lose pairs (ARM) was run flattened.
4. **One minor ledger note:** s12.8 fill C continuation 1 and the AC gate's CfgRecord accounting
   (row 28's "maximum 86.32%") should list the 100% instance pair, or accept it as an instance
   idiom.
5. **Fix the residual at the next baseline reset:** key self-pairs on declaration occurrence in a
   v3, using `samename.py` as its control.
6. **Close `backlog.md`'s open check** (the "earlier screens" line under ARM).
