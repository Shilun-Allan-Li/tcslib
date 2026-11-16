# Fill `gsw-security` — checkpoint 1 (F5: column leftover hashing)

**Worker:** Claude (single agent, external Claude route: delivery pushed to
`exchange/pass-shelat-ch5-8`, path `inbox/fills/gsw-security/` only).
**Issue base:** `486f44f8414c20a2d21e452c44de8b8c8d8513a0` (head of draft PR #333, `stmt/gsw`; contains
#332's `94eae71b779c4ca0f76c138d699f4d737dbd6cee` as `486f44f8~3`). Local proof branch
`fill/gsw-security`, never pushed. **Lean** 4.25.0; Mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`
(the base's `lake-manifest.json`).
**Inputs read:** exchange `README.md`, `outbox/fills/gsw-security/{README.md, brief.md,
fill-environment-addendum.md}` at exchange commit `523d4e97302606b0301ecbcff13882abb917ec1f`; the pack
verified with `shasum -a 256 -c SHA256SUMS` (7 × OK); `policy.md` at the base.

This is **checkpoint 1**. It removes exactly the two F5 targets. The four F6 targets of
`GSW/Security.lean` are untouched (`sorry`) and follow in the final delivery.

## Status of the targets

| Unit | Target | Status at checkpoint 1 |
|---|---|---|
| F5 | `Hashing.SIS.hashColumns_eq_mul` | **proved** |
| F5 | `Hashing.SIS.distAdv_hashColumns_uniform_le` | **proved** |
| F6 | `GSW.real_uniformKey_advantage` | `sorry` (final delivery) |
| F6 | `GSW.uniformKey_uniform_advantage_le` | `sorry` (final delivery) |
| F6 | `GSW.distAdv_encrypt_le` | `sorry` (final delivery) |
| F6 | `GSW.distAdv_encrypt_le_of_width` | `sorry` (final delivery) |

Admissions: base 53 declarations in 15 modules → **51 in 14** (`evidence/checkpoint1/admissions.txt`,
PASS: removed exactly `hashColumns_eq_mul` and `distAdv_hashColumns_uniform_le`, nothing added).
No statement was weakened, no hypothesis added, no definition changed.

## Changed files

| File | Lines at base | Lines at checkpoint 1 | Change |
|---|---|---|---|
| `TCSlib/Cryptography/Hashing/SIS/Columns.lean` | 89 | 194 | two `sorry` bodies replaced; both `**Proof sketch.**` paragraphs rewritten to the delivered proofs; one import added |

- **Import added:** `TCSlib.Cryptography.Pseudorandom.Indistinguishability` (authorized by the brief, in
  `order.txt`), for `acceptProb_bind`, `acceptProb_update` and `acceptProb_fst`. No Mathlib import added, so
  no new cache root. `Columns.lean` imports nothing under `AdvancedEncryption/`.
- **Sketch edits:** `hashColumns_eq_mul` (now names `hashColumns_apply`, `hash_eq`, `Matrix.mul_apply'`);
  `distAdv_hashColumns_uniform_le` (describes hybrids `H_k`, the planting test, `acceptProb_bind` /
  `acceptProb_comp_equiv` / `acceptProb_update`, the end hybrids via `acceptProb_fst`, and the telescoping by
  `abs_sub_le_sum_hybrids`). The statement prose before each `**Proof sketch.**` is byte-identical
  (frozen-statement check below).
- **New declarations:** none (public or private). The proof uses local `let`s (`hyb`, `plant`, `test`,
  seed relabellings) and `have`s only, as the brief prefers.

### The delivered proof of `distAdv_hashColumns_uniform_le`

Seeds of hybrid `H_k`: `(A, (x, u))`, `x : Fin N → {0,1}^columns`, `u : Fin N → Z_q^dimension`; column `j`
of the second component is `u j` for `j < k` and `hash A (x j)` otherwise, all under the same `A`. The
`k`-th test plants its challenge at column `k` and simulates the other columns from coins `(x, u)` carried
beside `D`'s own coins (type `((Fin N → In) × (Fin N → Out)) × ρ`, finite and nonempty).
1. `hleft`: `acceptProb (A, hash A r) (test k) = acceptProb H_k D` — `acceptProb_bind`, a seed
   relabelling (`acceptProb_comp_equiv`), `acceptProb_update` at column `k` of `x`, then the case split
   `j = k` / `j ≠ k` (`Function.update_self`, `Function.update_of_ne`).
2. `hright`: `acceptProb id (test k) = acceptProb H_{k+1} D` — the same with the update on `u`; cases
   `j < k`, `j = k`, `j > k`.
3. `hzero`/`hfull`: `H_0` is the real sampler and `H_N` the ideal one after transposing the seeds and
   dropping the unused half (`acceptProb_comp_equiv`, `acceptProb_fst`, `hashColumns_apply`).
4. `abs_sub_le_sum_hybrids` over `range N`; each gap is `distAdv (A, hash A r) (A, y) (test k)`, bounded by
   `distAdv_hash_uniform_le`; the sum of `N` equal bounds is `N · ε` (`Finset.sum_const`). `N = 0` needs no
   special case (empty sum).

This is the route of the brief (Gate 41: the strong single-column LHL applies because the test receives
`A`). No universality claim is made for `R ↦ A R`; no SIS hardness is used.

## Overlap and reuse

No new declaration. The inline `have`s of `distAdv_hashColumns_uniform_le` re-prove instances of existing
material; each is disclosed here.

| Inline step | Nearest relative (base `486f44f8`) | Relation | Why not reused |
|---|---|---|---|
| the whole column hybrid (steps 1–4) | `TCSlib/Cryptography/Encryption/PublicKey/Hybrid.lean:88` `distAdv_tuple_le_sum` | **same argument**: a hybrid over `q+1` positions sharing one public parameter, a planting distinguisher per position, `abs_sub_le_sum_hybrids` | not importable under the brief: the module is not in `order.txt` and an import of it needs a scope request; it imports `Asymptotic.BlockEncryptor` (the NUPPT/Turing-machine layer) into the SIS hash layer, against policy §1 layering; its interface also needs one common seed type for both sides and `N = q+1`, so the adaptation (a sum-type seed, the `N = 0` case, matrix ↔ tuple relabellings) would be as long as the hybrid. Proposed for promotion below. |
| `hleft`, `hright` (planting one column) | `…/Encryption/PublicKey/Hybrid.lean:52` **private** `acceptProb_plant`; `TCSlib/Cryptography/Pseudorandom/Indistinguishability.lean:247,266` `acceptProb_multicopyRed_left`/`_right`; `TCSlib/Cryptography/TrapdoorFunctions/Lossy/Experiments.lean:138` `column_gap` | specialization of the planting identity to a shared public matrix | `acceptProb_plant` is private (not copied: re-derived from the public `acceptProb_bind`, `acceptProb_comp_equiv`, `acceptProb_update`); the multicopy lemmas have no shared key; `column_gap` is LWE-specific (pattern only, as the brief says) |
| `hzero`, `hfull` (end hybrids) | `Indistinguishability.lean` `acceptProb_multicopyHybrid_zero`/`_self` (225, 234) | same shape (ends of a hybrid ignore half the seed) | stated for `multicopyHybrid`, not for this sampler; proved here by the public `acceptProb_fst`/`acceptProb_comp_equiv` |
| telescoping + per-gap bound | `TCSlib/Cryptography/Foundations/Probability.lean:218` `abs_sub_le_sum_hybrids`; `TCSlib/Cryptography/Hashing/SIS/Universality.lean:166` `distAdv_hash_uniform_le` | **reused** directly | — |
| `hashColumns_eq_mul` | Mathlib `Matrix.mul_apply'` (`Mathlib/Data/Matrix/Mul.lean:299`) | **reused** (with `hash_eq`) | — |

`OneWayFunctions/Basic.lean:131` `OneWay.uprob_update` (used by `column_gap` and `acceptProb_plant`) was
not used: its module is not an authorized import; the authorized `acceptProb_update` covers the need.

**Searches run** (raw output in `evidence/overlap/`): `git grep` at the base over `TCSlib/` for
`hashColumns`, `columnHybrid`, `columnTest`, `column_gap`, `multicopy`, `abs_sub_le_sum_hybrids`,
`exists_hybrid_gap`, `acceptProb_update`, `uprob_update`, `acceptProb_bind`, `acceptProb_comp_equiv`,
`acceptProb_fst`, `acceptProb_snd`, `distAdv_hash_uniform_le`, `theorem distAdv_*_le`, `theorem uprob_*`,
`theorem acceptProb_*`, `theorem uexp_*`, `Function.update`, `hybrid`, `transpose…Equiv|piComm`,
`mul_apply'` (`searches-tcslib.txt`); Mathlib at the pin for `mul_apply'`, `mulVec_eq_sum`, `of_apply`,
`piComm`, `ofBijective_apply`, `symm_apply_apply`, `addRight`, `prodCongr` (`searches-mathlib.txt`).

## Scope requests

None. (Reusing `distAdv_tuple_le_sum` would have needed one — an import outside the brief's list — and
was not requested: see *Overlap and reuse*; Seyoon prefers routes without frozen-file changes.)

## Promotion requests

- **P-1 (dedup queue).** A generic shared-parameter hybrid in the probability layer
  (`Foundations/` or `Pseudorandom/Indistinguishability.lean`), stated for two samplers with *different*
  seed types `X : κ × σ → γ`, `Y : κ × τ → γ` and `N` positions (including `N = 0`), would serve
  `distAdv_tuple_le_sum`, `Lossy.column_gap`/`concealed_advantage_le` and `distAdv_hashColumns_uniform_le`
  alike; `acceptProb_plant` would then become public. Not done here (frozen files).

## Rule 10

- `Columns.lean` reads `hash` only through `hash_eq` (in `hashColumns_eq_mul`), `distAdv`/`acceptProb`
  only through `distAdv_def` and the published `acceptProb_*` lemmas, and its own `hashColumns` through
  `hashColumns_apply` (own definitions may be read directly). Mathlib definitions reduce only in the final
  `rfl` of `hashColumns_eq_mul` (`Matrix.mulVec`, `Matrix.of`, `dotProduct`) and in `congrArg`/`Prod.ext`
  definitional steps.
- **Seals** (`evidence/seals/{cp1-base,cp1}/`, summary `evidence/checkpoint1/rule10-summary.txt`):
  whole-file seals of `Columns.lean` over its full TCSlib import closure, at the base and at checkpoint 1, in
  A/B × strict/coe, each run with `lean -DmaxErrors=0`. Harness adapted from the derand fill's
  `make_seals.py` (Gate 10 lineage; `evidence/tools/make_seals.py` says what changed: labels, paths, CLI).
  Every probe logs one `GSWSEC-INSTALL` and one `GSWSEC-EOF` (harness-valid) and its full catalog.

  | Probe | A strict | **A coe (canonical)** | B strict | B coe |
  |---|---|---|---|---|
  | base `Columns.lean` | 0 errors (25 sealed) | **0** (24) | 0 (25) | 0 (24) |
  | checkpoint 1 `Columns.lean` | 0 errors (32 sealed) | **0** (31) | 0 (32) | 0 (31) |

  No failing declaration in any variant, so there is no difference to attribute. Strict seals one more
  definition than coe: the projection coercion `FinDist.instCoeFunForallReal`. A and B coincide because
  `Complexity.PolyExpr.eval` is not in `Columns.lean`'s closure. The checkpoint closure adds the
  Indistinguishability definitions (`pushSampler`, `sunglassRed`, `mixDist`, `copies`, `multicopyHybrid`,
  `multicopyRed`, `multicopyAvgRed`). The seal covers the SIS `hash` (`TCSlib.Cryptography.Hashing.SIS.hash`,
  sealed in every variant); `Regev.augmented` and `LWE.sample` are not in this file's closure (they are
  covered by the final seals of `Security.lean`).
- **Controls** (`evidence/controls/cp1/`, `ctlcheck.txt` **ALL_OK**, 35 probes): pairs for `hash`
  (`hash_eq` vs `rfl`), `distAdv` (`distAdv_def` vs `rfl`), `acceptProb` (`acceptProb_def` vs `rfl`), and a
  negative for the `FinDist` projection coercion (`p a = p.prob a := rfl`). Each runs unsealed and in the four
  variants. Positives pass everywhere; each negative passes unsealed and fails **exactly once** in every
  variant that seals its definition (the coercion only in strict, as intended).
- **Explicit-unfold scan** (`evidence/checkpoint1/unfold/`): 59 selector items in the owned files
  (base 0): 19 local or own names, 40 lemmas, **0 foreign definitions**. PASS.
- **Error counts, both forms (G26-N1)** (`evidence/checkpoint1/error-counts.txt`, regex
  `^\S+\.lean:\d+:\d+: error([:(])`): the sweep (147 logs), seals (8), bootstrap (23), base checks (2) and
  axioms: 0 `error:`, 0 `error(`. Controls: 14 `error:`, 0 `error(`, exactly the 14 expected sealed
  negatives. Development log `evidence/logs/dev/columns-01.log`: 1 `error:` (`No goals`, the first draft,
  fixed in `columns-02`).

## Checks (checkpoint 1)

| Check | Result | Evidence |
|---|---|---|
| Owned modules, native check | `Columns` 0 errors, 0 `sorry`; `Security` 0 errors, 4 `sorry` (F6, untouched) | `evidence/checkpoint1/sweep/*Columns.log`, `*Security.log`; dev logs `evidence/logs/dev/` |
| Sweep of `order.txt` (147 modules), one Lean process at a time | **ALL 147 OK**, 0 errors in both forms | `evidence/checkpoint1/sweep.log`, `sweep/` |
| Admissions vs `base-sorries.txt` | 53 → **51 in 14 modules**; removed exactly the 2 F5 targets; added 0 | `evidence/checkpoint1/admissions.txt` |
| Axioms of the targets and every stored constant of `Columns.lean` (7) | `propext`, `Classical.choice`, `Quot.sound` only (the 3 `_simp` auxiliaries: `propext`) | `evidence/checkpoint1/axioms.log`, probe `evidence/axioms/cp1/Axioms.lean` |
| Dependency trace (constant closure, `sorryAx` search) | both targets: **no sorried constant reached** (19103 and 2444 constants visited); no `gsw-core` target cited | same |
| Frozen-statement check (python3 -I) + 2 controls per file | 0 differences in both files (Columns: one import added, listed as ADDED); controls: one-character header change → exactly 1 difference, deleted reader → exactly 1 removal (PASS ×4) | `evidence/headers/` (`frozen_headers.py`, `run_headers.py`, `checkpoint1/summary.txt` and full outputs) |
| Rule 10 seals, controls, explicit-unfold scan | see *Rule 10* | `evidence/seals/`, `evidence/controls/`, `evidence/checkpoint1/unfold/` |
| Lint `campaign_style_lint.py TCSlib/Cryptography --check8b` | base **92 FAIL / 101 WARN over 364 files** (= maintainer baseline); checkpoint identical; line-set diff: only the `Columns.lean` INFO line (89 → 194 lines); owned files have no FAIL/WARN line | `evidence/lint/` |
| Name-clash scan | 0 new names (no new declaration) → PASS | `evidence/clash/name_clash.py`, `checkpoint1.txt` |
| Widths / sizes | max width 100 (`Columns`), 95 (`Security`); 194 and 217 lines | `evidence/checkpoint1/widths.txt` |
| Patch reproduction | `git am` at the base in a scratch clone reproduces `58a97f52…` and the tree | `evidence/checkpoint1/patch-reproduction.txt` |

## Environment

- **Preflight** (`evidence/logs/preflight.log`): `nproc` 4; cgroup v1 memory limit 14,338,772,992 B;
  in use (`usage − total_cache + total_shmem`) 386,310,144 B; **headroom 12.99 GiB** (floor 4); disk free on
  the clone's ext4 filesystem **18.22 GiB** (floor 12). No E-RES. The checkout, `.lake` and the olean tree
  are on ext4 (`/dev/vda`), not tmpfs.
- **Toolchain:** elan installed after the preflight with `leanprover/lean4:v4.25.0`
  (`evidence/logs/toolchain.log`); disk re-check before the cache: 15.8 GiB free (floor 8).
- **Cache** (`evidence/logs/cache-store.log`, `mathlib-roots.txt`, `cache-get.log`): the archive store
  `/root/.cache/mathlib` was **absent** before the fetch (0 archives, so none pre-existing). Narrowed fetch
  for the **84 roots** (identical to the pack's `roots.txt`): "Attempting to download 2338", "Decompressing
  2338", "Completed successfully", exit 0, no failed download. No zero-size olean. Cache probe
  (`import Mathlib.Algebra.BigOperators.Field`) elaborated, exit 0.
- **Packages** (`evidence/logs/packages-check.log`): last line
  `RESULT: PASS: 11 present packages match the manifest; absent: «doc-gen4», UnicodeBasic, BibtexQuery, MD4Lean`
  (no module of the order imports an absent package).
- **Bootstrap** (`evidence/logs/bootstrap.log`): phase 1 = the 23 modules of the order that the owned files
  and `Pseudorandom/Indistinguishability` import (`bootstrap-phase1.txt`), ALL OK; then the owned files at
  the base (`evidence/logs/base-checks/`: Columns 2 `sorry`, Security 4 `sorry`, 0 errors); the remaining
  modules were built by the checkpoint sweep of all 147, in order.
- **Lean processes:** one at a time throughout (every check serial through `check_module.py`). Peak RSS per
  check ≤ 2.9 GB (`MAXRSS_KIB` in each log; `/usr/bin/time` is absent on this host, so the peak is
  `getrusage(RUSAGE_CHILDREN)`). No `lake build`, no unfiltered `lake exe cache get`; Python always
  `python3 -I`.
- **Check scripts:** module checks and sweeps use `scripts/lean_check_tree.sh` unchanged. Seals, controls
  and probes use `evidence/tools/lean_check_tree_maxerrors0.sh`, a copy differing only in `-DmaxErrors=0`,
  failing on `error[:(]`, and taking the checkout root from the working directory.

## Evidence

All under `inbox/fills/gsw-security/`; manifests `SHA256SUMS` (every delivered file except itself) and
`evidence/SHA256SUMS` (every file under `evidence/` except itself), paths equal to the delivered files.
- `patches/0001-*.patch` (`git format-patch 486f44f8..fill/gsw-security`), `patches/COMMITS.tsv`
  (signing `none`; committed with `git -c commit.gpgsign=false`).
- `src/TCSlib/Cryptography/Hashing/SIS/Columns.lean` (equal to the branch's file).
- `evidence/logs/` (preflight, toolchain, cache, packages, bootstrap, base checks, dev iterations),
  `evidence/checkpoint1/` (sweep, admissions, axioms, unfold scan, rule-10 summary, error counts, widths,
  patch reproduction, queue output), `evidence/seals/`, `evidence/controls/`, `evidence/axioms/`,
  `evidence/headers/`, `evidence/lint/`, `evidence/clash/`, `evidence/overlap/`, `evidence/probes/`, and
  `evidence/tools/` (every script used, run as `python3 -I` from the fill checkout's root).
