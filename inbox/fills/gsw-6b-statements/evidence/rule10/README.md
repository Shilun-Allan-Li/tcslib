# Rule 10 evidence (brief check 6), gsw-6b-statements, sub-agent `seal`

## Canonical: `r2/` (current heads)

Heads:
- base `3e51b5f28900db6190f1eb2e6d207d27ee15d541`
- O2 head `5bd5ada5f42c5e1228ea84ad70f4d8c52a3644fd`
- final head `8f92fe7d53967bc488a4075fb38210e7d40b9031`

The olean tree `/home/user/oleans/seal/TCSlib` is a byte copy of the lead's tree. That tree is bound to
`8f92fe7d`: 1452/1452 BOUND, per `/home/user/ev/build/root-final/summary.txt`.

| Run | Rev | Owners |
|---|---|---|
| `r2/o2/` | `5bd5ada5` | `LWE/BitEncoding.lean` (O2) |
| `r2/final-bitenc/` | `8f92fe7d` | `LWE/BitEncoding.lean` |
| `r2/final/` | `8f92fe7d` | `LWE/Ratio.lean`; `GSW/{Branching, DecryptFormula, Bootstrap, Circular, Leveled, LeveledSecurity, PolyRatio, Asymptotic}.lean`; facades `GSW.lean`, `LWE.lean` |
| `r2/compare-a855e111.txt` | | request sets of every r2 seal compared with the a855e111 runs: **52 compared, 0 different** |

Made with one command, with `/home/user/sub/seal` at `8f92fe7d`:

```
bash /home/user/ev/tools/seal/run_heads.sh 5bd5ada5f42c5e1228ea84ad70f4d8c52a3644fd 8f92fe7d53967bc488a4075fb38210e7d40b9031 /home/user/ev/rule10/r2
python3 -I /home/user/ev/tools/seal/xr/compare_requests.py o2 r2/o2 final-bitenc r2/final-bitenc final r2/final > r2/compare-a855e111.txt   # in /home/user/ev/rule10
```

`run_heads.sh` calls `run_checkpoint.sh` three times. For other heads or modules, run
`run_checkpoint.sh <worktree> <rev> <base> <outdir> <modules.txt> <controls-spec.json|-> [title]` directly.

`BitEncoding.lean` has the same bytes at `5bd5ada5` and `8f92fe7d` (sha256 `74cf46e4…23a4`, `source-identity.tsv`).
Its TCSlib closure (`LWE.Basic`, `LWE.Noise`) is unchanged from base to final, so the two BitEncoding seals have the
same source and the same closure. The tools key the source on a revision, so both revisions were run.

## History, kept for comparison

| Run | What it is |
|---|---|
| `o2/` | O2 head `dd84941f` |
| `final-bitenc/`, `final/` | final head `a855e111` (before the maintainer review) |
| `cp1/` | old checkpoint-1 head `292ed483` |

All of these passed. `cp1/` was built from the component tools, without `run_checkpoint.sh`. Its seals, controls and
scans are at the same paths, but it has no `source-identity.tsv`.

## Layout of one run directory `<run>/`

| Path | Content |
|---|---|
| `modules.txt`, `controls-spec.json` | owners (dotted module names); control spec: owner, definition, statement, body read (`neg`), reader (`pos`) |
| `source-identity.tsv` | per file: sha256 at the rev (git show) and of the worktree file; must be `identical` (the probes elaborate against the olean tree, built from the worktree) |
| `seal-summary.tsv` | **seal summary**: owner, variant (A, B, coe-A, coe-B), requests, verified (install/EOF sums), rc, errors, counts_ok, verdict, failing declarations, first error line, source sha256, max RSS, seconds, sorry warnings |
| `seal/seal-<V>.tsv` | sealsum.py per probe (same data, probe labels) |
| `seal/seals-<V>/` | seal sources (`<label>.lean.txt`, the exact probe bytes), records (`<label>.json`: requests, elaborated-term rows and their exclusions, line map) and `manifest.json` |
| `seal/run-<V>/` | raw logs (`mods/*.log`) and `results.jsonl` (rc, errors, sorry, max RSS, sha256 of source and log) |
| `seal/Collect.lean`, `seal/collect.log`, `seal/collect-lines.log` | the collector (CAT/ROOT/CLOSURE rows) |
| `seal/touched.{json,tsv}` | declaration spans, used to attribute an error to its declaration |
| `notation-check.tsv` | notation, never sealed. Each named abbreviation (`Parameters.columns`, `Ciphertext`, `PublicKey`, `Secret`, `Coins`, `KeySeed`, `FheView`, `Seeds`, plus `LevelCoins`, `LeveledSeeds`, `LeveledView` in `final/`), `PolyExpr.eval` and the FinDist coercion, per probe and variant: requested, not requested, own file, or outside the closure. Also the requested instances, and the requested reducible constants (must be none). Ends `RESULT unexpected=<n>` |
| `unfold/explicit-unfold-scan.txt` | scan_unfold.py: per-file hit counts, `OWN` / `notation` / `FOREIGN-UNFOLD` lines, `RESULT foreign_unfolds=…` |
| `unfold/scan-resolve.{tsv,log}`, `unfold/Resolve_*.lean`, `unfold/run-resolve/` | Lean-resolved supplement. Every simp/rw/unfold argument is resolved in the file's own name context and classified THEOREM, LOCAL, OWN-DEF, NOTATION, FOREIGN-UNFOLD or CORE-DEF (a core/Mathlib definition) |
| `controls/summary.tsv` | **controls**: per control file: harness (none / strict(A) / coe(coe-A)), rc, errors, expected errors, whether the error lies in the example, install/EOF records, verdict, error line. Ends with `pretest_unsealed_ok`, `ALL_OK` |
| `controls/src/`, `controls/records/`, `controls/run-unsealed/`, `controls/run-sealed/` | control sources, records (requests, line maps), raw logs |

The `cp1/misc-instkind/` probe shows that `Parameters.neZero_columns` is a theorem (a Prop instance), so there is
nothing to seal. `fheView_fst` and `fheView_snd` are theorems too.

## What the variants and controls are

**Seals.** These are whole-file probes made with the 6a/GSW harness (`build_seals.instrument` plus
`request_payload_adapter`: actual-Name component checks, instance unfolding mask, EOF verification).
- The probe requests every eligible TCSlib definition of the owner's full import closure. Eligible means kind
  `def` and (a matcher, or not reducible).
- Reducible definitions are never requested: abbreviations, instances declared by `instance`, and structure
  projections.
- Variants:
  - **A** (strict) excludes `PolyExpr.eval`.
  - **B** seals `PolyExpr.eval` too.
  - **coe-A** (canonical) and **coe-B** are A and B with `FinDist.instCoeFunForallReal` also excluded as notation.
- Each probe runs `lean -DmaxErrors=0` with no `-o`, through the shared pool.
- PASS means: rc 0, 0 errors, install record `requested = verified = requests`, and the same for the EOF record.
- No run needed `SEAL_CHUNK`. The largest probe has 1,651 requests.

**Controls.** Each control is a separate consumer file, `import <owner>` + one `example`. Steps per owner:
1. Pretest, unsealed: the body read (`rfl` / `Iff.rfl`) must give 0 errors.
2. The same file with the full seal harness after the import, over closure(owner) ∪ {owner}, so the definition
   itself is requested. Harnesses: strict (A exclusions) and coe (coe-A exclusions). It must give exactly 1 error,
   inside the example.
3. The reader in the same sealed file: 0 errors.
Install/EOF records are checked in every sealed control.

## Results at the current heads (`r2/`)

**Seals**: no failing declaration in any seal. Every probe is PASS, with install = EOF = requests. Sorry warnings
equal the unsealed build's (lead's `root-final` summary).

| Owner | A | B | coe-A | coe-B | Sorry warnings |
|---|---|---|---|---|---|
| `LWE/BitEncoding` at O2 `5bd5ada5` | 9 | 9 | 9 | 9 | 0 |
| `LWE/BitEncoding` at final `8f92fe7d` | 9 | 9 | 9 | 9 | 0 |
| `LWE/Ratio` | 947 | 948 | 946 | 947 | 0 |
| `GSW/Branching` | 199 | 199 | 199 | 199 | 3 |
| `GSW/DecryptFormula` | 374 | 374 | 373 | 373 | 6 |
| `GSW/Bootstrap` | 437 | 437 | 436 | 436 | 5 |
| `GSW/Circular` | 457 | 457 | 456 | 456 | 1 |
| `GSW/Leveled` | 467 | 467 | 466 | 466 | 2 |
| `GSW/LeveledSecurity` | 1,549 | 1,550 | 1,548 | 1,549 | 2 |
| `GSW/PolyRatio` | 1,382 | 1,383 | 1,381 | 1,382 | 3 |
| `GSW/Asymptotic` | 1,641 | 1,642 | 1,640 | 1,641 | 2 |
| `GSW.lean` (facade) | 1,650 | 1,651 | 1,649 | 1,650 | 0 |
| `LWE.lean` (facade) | 966 | 967 | 965 | 966 | 0 |

- B = A + 1 exactly where `PolyExpr.eval` is in the closure.
- coe = strict − 1 exactly where `FinDist.instCoeFunForallReal` is in the closure.

**Controls**: every result is as expected (`ALL_OK=True` in all three runs).
- 10 owners. Unsealed pretest: 0 errors.
- Body read under strict(A) and coe(coe-A): exactly 1 error, at the example.
- Reader under strict(A) and coe(coe-A): 0 errors.

| Owner | Definition | Reader |
|---|---|---|
| `LWE/BitEncoding` | `decodeLo` | `decodeLo_eq` |
| `LWE/Ratio` | `Family.RatioBounded` | `Family.ratioBounded_iff` |
| `GSW/Branching` | `select` | `select_eq` |
| `GSW/DecryptFormula` | `decDepth` | `decDepth_eq` |
| `GSW/Bootstrap` | `bootNoise` | `bootNoise_eq` |
| `GSW/Circular` | `WeakCircularSecure` | `weakCircularSecure_iff` |
| `GSW/Leveled` | `levelKey` | `levelKey_eq` |
| `GSW/LeveledSecurity` | `challengeDist` | `challengeDist_eq` |
| `GSW/PolyRatio` | `pBoot` | `pBoot_eq` |
| `GSW/Asymptotic` | `encodeCiphertext` | `encodeCiphertext_eq` |

The facades `GSW.lean` and `LWE.lean` define nothing, so they get no pair.

**Unfold scans**:
- 0 foreign unfolds. BitEncoding has 52 hits. The 11 final files have 49 hits, including 5 own-file unfolds:
  - `GSW/Bootstrap.lean:153,161,169`: `unfold bootGate`.
  - `GSW/Leveled.lean:140,147`: `unfold levelGate`.
- Lean-resolved: 0 core/Mathlib definitions and 0 foreign TCSlib definitions passed to simp/rw/unfold.
  - BitEncoding: 50 theorems, 2 locals.
  - Final files: 40 theorems, 4 locals (hypotheses `h`), 5 own definitions.

**Notation**: `unexpected=0` in every run.
- No abbreviation or reducible constant is ever requested.
- `PolyExpr.eval` is requested only in B/coe-B.
- The FinDist coercion is requested only in A/B.

Every Lean process ran through the shared pool (`xr/runner_pool.py` → `/home/user/ev/tools/lead/poollib.py`). The
tools and their change headers are in `/home/user/ev/tools/seal/`.

## Packaging note (lead, at delivery)
The superseded comparison runs `final/` (all owners at `a855e111`) and `cp1/` (checkpoint-1 files at `292ed483`) are
delivered as `superseded-final.zip` and `superseded-cp1.zip` (deflate; entry lists `superseded-*.entries.txt`) to keep the
delivery small; their contents are unchanged. The canonical evidence is `r2/` (O2 `5bd5ada5…`, final `8f92fe7d…`).
`o2/` and `final-bitenc/` are the earlier BitEncoding runs (old O2 `dd84941f…`, `a855e111`), kept raw.
