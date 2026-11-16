# Fill `gsw-security` — final (F5 column leftover hashing, F6 IND-CPA of public-key GSW)

**Worker:** Claude (single agent; external Claude route: deliveries pushed to `exchange/pass-shelat-ch5-8`,
path `inbox/fills/gsw-security/` only). **Issue base:** `486f44f8414c20a2d21e452c44de8b8c8d8513a0` (head of
draft PR #333, `stmt/gsw`; contains #332's `94eae71b779c4ca0f76c138d699f4d737dbd6cee` as `486f44f8~3`).
Local proof branch `fill/gsw-security`, never pushed; its head is `a9f97eddb42c7dfc0422fa8c9ce998c658bfa4f8`.
**Lean** 4.25.0; Mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e` (the base's `lake-manifest.json`).
**Inputs read:** exchange `README.md`, `outbox/fills/gsw-security/{README.md, brief.md,
fill-environment-addendum.md}` at exchange commit `523d4e97302606b0301ecbcff13882abb917ec1f`, the pack
verified with `shasum -a 256 -c SHA256SUMS` (7 × OK); `policy.md` at the base; the Gate 41 excerpts were not
needed (no new citation tag was written).

**Deliveries.** Checkpoint 1 (F5) was pushed as exchange commit `b08456186` (`fill gsw-security: checkpoint 1`);
its report is kept verbatim as `evidence/checkpoint1/REPORT-checkpoint1.md` with its evidence under
`evidence/checkpoint1/`, `evidence/seals/cp1*`, `evidence/controls/cp1`, `evidence/axioms/cp1`. This is the final
delivery; it supersedes the checkpoint's `REPORT.md`, `patches/`, `src/` and manifests.

## Status of the targets

All six targets are proved; no statement was weakened, no hypothesis added, no definition changed.

| Unit | Target | Status | Proof |
|---|---|---|---|
| F5 | `Hashing.SIS.hashColumns_eq_mul` | **proved** (checkpoint 1) | entrywise `hashColumns_apply`, `hash_eq`, `Matrix.mul_apply'`, `rfl` |
| F5 | `Hashing.SIS.distAdv_hashColumns_uniform_le` | **proved** (checkpoint 1) | column hybrid over `distAdv_hash_uniform_le` (below) |
| F6 | `GSW.real_uniformKey_advantage` | **proved** | exact equality via `acceptProb_bind` |
| F6 | `GSW.uniformKey_uniform_advantage_le` | **proved** | relabellings + `distAdv_hashColumns_uniform_le` |
| F6 | `GSW.distAdv_encrypt_le` | **proved** | triangle inequality over the four hybrids |
| F6 | `GSW.distAdv_encrypt_le_of_width` | **proved** | `distAdv_encrypt_le` + `Regev.two_extractionError_le` |

Admissions: base 53 declarations in 15 modules → **47 in 13** (`evidence/final/admissions.txt`, PASS: removed
exactly the 6 targets, nothing added). Checkpoint 1 removed the 2 F5 targets (53 → 51 in 14).

**`gsw-core` targets:** none cited. The dependency trace of every target reaches no sorried constant, so no
`gsw-core` target (`encrypts_*`, `vecMul_secretVector_augmented`, …) is in any proof's closure. Only `gsw-core`'s
`rfl` readers `encrypt_eq`, `lift_apply` (and the definitions `gadget`, `Parameters.columns`, `Ciphertext` as
terms/notation) are used.

## Changed files

| File | Lines at base | Lines at final | Change |
|---|---|---|---|
| `TCSlib/Cryptography/Hashing/SIS/Columns.lean` | 89 | 194 | 2 `sorry` bodies replaced; both `**Proof sketch.**` paragraphs rewritten; import `Pseudorandom.Indistinguishability` added |
| `TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Security.lean` | 217 | 305 | 4 `sorry` bodies replaced; the 4 `**Proof sketch.**` paragraphs rewritten; import `Pseudorandom.Indistinguishability` added |

- **Imports:** only `TCSlib.Cryptography.Pseudorandom.Indistinguishability` (authorized, in `order.txt`), in
  both files (`acceptProb_bind`, `acceptProb_update`, `acceptProb_fst`). No Mathlib import, so no new cache root.
  `Columns.lean` imports nothing under `AdvancedEncryption/`. No helper module.
- **Sketch edits** (statement prose before each `**Proof sketch.**` byte-identical, checked):
  `hashColumns_eq_mul` (names its three equations); `distAdv_hashColumns_uniform_le` (hybrids `H_k`, the planting
  test, the end hybrids, telescoping); `real_uniformKey_advantage` (the reassociation is now `acceptProb_bind`, with
  `reduction_eq`, `realView_eq`, `uniformKeyView_eq`); `uniformKey_uniform_advantage_le` (adds `lift_apply`,
  `Equiv.addRight` and "the test that undoes both relabellings"); `distAdv_encrypt_le` (names `abs_sub_le` ×3 and
  `linarith`); `distAdv_encrypt_le_of_width` (names `mul_le_mul_of_nonneg_left`).
- **New declarations:** none, public or private. All auxiliary objects are local `let`s/`have`s, as the brief
  prefers; `## Main results` is unchanged.

## The delivered proofs

**F5 `distAdv_hashColumns_uniform_le`.** Seeds of hybrid `H_k`: `(A, (x, u))`, `x : Fin N → {0,1}^columns`,
`u : Fin N → Z_q^dimension`; column `j` is `u j` for `j < k`, else `hash A (x j)`, all under the same `A`. The
`k`-th test plants its challenge at column `k`, simulates the other columns from coins `(x, u)` carried beside
`D`'s coins (type `((Fin N → In) × (Fin N → Out)) × ρ`, finite, nonempty), and runs `D`.
1. `hleft`: on `(A, hash A r)` the test accepts as `D` on `H_k` — `acceptProb_bind`, a seed relabelling
   (`acceptProb_comp_equiv`), `acceptProb_update` on `x` at `k`; cases `j = k` / `j ≠ k`.
2. `hright`: on uniform `(A, y)` it accepts as `D` on `H_{k+1}` — the same with the update on `u`; cases
   `j < k`, `j = k`, `j > k`.
3. `hzero`/`hfull`: `H_0` is the real sampler, `H_N` the ideal one, after transposing seeds and dropping the
   unused half (`acceptProb_comp_equiv`, `acceptProb_fst`, `hashColumns_apply`).
4. `abs_sub_le_sum_hybrids` over `range N`; each gap is `distAdv (A, hash A r) (A, y) (test k)` ≤ the
   single-column error by `distAdv_hash_uniform_le` (Gate 41: valid because the test receives `A`); `N` equal
   terms give `N · ε`. `N = 0` is the empty sum. No universality claim for `R ↦ A R`; no SIS hardness.

**F6.** Write `ε = Regev.extractionError P.lwe = ½·√(q^{n+1}/2^m)`.
- `real_uniformKey_advantage`: `reduction P μ D = fun pk c => D (view P μ pk c.1) c.2` (`reduction_eq`), so
  `acceptProb_bind` turns its acceptance on `LWE.sample P.lwe χ` (resp. the identity on keys) into `D`'s
  acceptance on `fun s => view P μ (LWE.sample … s.1) s.2` = `realView P χ μ` (resp. `uniformKeyView P μ`), read
  by `realView_eq`/`uniformKeyView_eq`; then `LWE.decisionAdvantage_eq`, `distAdv_def`. Exact equality; the
  reduction's coins are `R` paired with `D`'s coins.
- `uniformKey_uniform_advantage_le`: `keyEquiv := Equiv.ofBijective (Regev.augmented P.lwe)
  (Regev.augmented_bijective P.lwe)` (keeps the whole key), `unpack := keyEquiv.symm × (· + μG)`. The ciphertext
  `Ā·lift R + μG` equals `hashColumns (columnHashParameters P) N Ā R + μG` (`encrypt_eq`, `hashColumns_eq_mul`,
  `lift_apply`; `columnHashParameters` read directly, its own file). Relabelling both samplers
  (`acceptProb_comp_equiv`) makes the gap that of `(Ā, ĀR)` vs `(Ā, U)` for `test := D ∘ unpack`;
  `distAdv_hashColumns_uniform_le (columnHashParameters P) N test` and the `columnHashParameters_{modulus,
  dimension, columns}` readers with `Regev.extractionError_eq` give `N · ε`. `Regev.hashParameters` is never
  unfolded or used.
- `distAdv_encrypt_le`: the chain real `μ₀` → uniform-key `μ₀` → uniform → uniform-key `μ₁` → real `μ₁`;
  `abs_sub_le` three times, the two exact DLWE terms and two `N · ε` terms, `linarith`.
- `distAdv_encrypt_le_of_width`: `2·(N·ε) = N·(2ε) ≤ N·2^{−κ}` by `Regev.two_extractionError_le P.lwe w κ hq hm`
  and `mul_le_mul_of_nonneg_left` (`N ≥ 0`), then `linarith`. Only the concrete fixed-bit function-level
  statements (ruling Q8): nothing about efficiency, `NUPPT` or SIS hardness; no small-secret/normal-form
  assumption (one common uniform secret, `m` rows, as `LWE.sample`).

## Overlap and reuse

No new declaration (public or private). The inline `have`s re-prove instances of existing material; each is
disclosed with its nearest relative at the base `486f44f8`.

### F5 (`Hashing/SIS/Columns.lean`)

| Inline step | Nearest relative | Relation | Why not reused |
|---|---|---|---|
| the whole column hybrid of `distAdv_hashColumns_uniform_le` (steps 1–4) | `TCSlib/Cryptography/Encryption/PublicKey/Hybrid.lean:88` `distAdv_tuple_le_sum` | **same argument**: a hybrid over `q+1` positions sharing one public parameter, a planting distinguisher per position, `abs_sub_le_sum_hybrids` | not importable under the brief: the module is not in `order.txt`, so an import needs a scope request; it imports `Asymptotic.BlockEncryptor` (NUPPT/Turing-machine layer) into the SIS hash layer, against policy §1 layering; its interface needs one seed type for both sides and `N = q+1`, so the adaptation (sum-type seeds, `N = 0`, matrix ↔ tuple relabellings) would be as long as the hybrid. Promotion P-1 below. |
| `hleft`, `hright` (planting one column) | `…/Encryption/PublicKey/Hybrid.lean:52` **private** `acceptProb_plant`; `TCSlib/Cryptography/Pseudorandom/Indistinguishability.lean:247,266` `acceptProb_multicopyRed_left`/`_right`; `TCSlib/Cryptography/TrapdoorFunctions/Lossy/Experiments.lean:138` `column_gap` | specialization of the planting identity to a shared public matrix | `acceptProb_plant` is private: not copied, re-derived from the public `acceptProb_bind`, `acceptProb_comp_equiv`, `acceptProb_update`; the multicopy lemmas have no shared key; `column_gap` is LWE-specific (pattern only, per the brief) |
| `hzero`, `hfull` (end hybrids) | `Indistinguishability.lean:225,234` `acceptProb_multicopyHybrid_zero`/`_self` | same shape (an end hybrid ignores half the seed) | stated for `multicopyHybrid`; here by the public `acceptProb_fst`, `acceptProb_comp_equiv` |
| telescoping + per-gap bound | `TCSlib/Cryptography/Foundations/Probability.lean:218` `abs_sub_le_sum_hybrids`; `TCSlib/Cryptography/Hashing/SIS/Universality.lean:166` `distAdv_hash_uniform_le` | **reused** | — |
| `hashColumns_eq_mul` | Mathlib `Matrix.mul_apply'` (`Mathlib/Data/Matrix/Mul.lean:299`) | **reused** with `hash_eq` | — |

`TCSlib/Cryptography/OneWayFunctions/Basic.lean:131` `OneWay.uprob_update` (used by `column_gap` and
`acceptProb_plant`) was not used: not an authorized import; the authorized `acceptProb_update` covers the need.

### F6 (`GSW/Security.lean`)

Gate 41 accepted the four F6 statements as GSW restatements of the Regev PKE hybrids (not duplicates); the
proofs follow those hybrids, as the brief asks.

| Inline step | Nearest relative | Relation | Why not reused |
|---|---|---|---|
| `real_uniformKey_advantage` (whole proof) | `TCSlib/Cryptography/Encryption/PublicKey/Regev/Experiments.lean:128` `Regev.real_uniformKey_advantage`; `Indistinguishability.lean:131` `distAdv_sunglassRed` | same argument for GSW's ciphertext space; `reduction P μ D` is definitionally `sunglassRed (view P μ) D` | Regev's lemma is about Regev's `view`/ciphertext type; `distAdv_sunglassRed` would require reading the foreign `sunglassRed`/`pushSampler`, which have no published readers (Rule 10). Instead the public `acceptProb_bind` (the lemma underneath `distAdv_sunglassRed`) is **reused** with the own readers. |
| `uniformKey_uniform_advantage_le` (relabellings) | `Regev/Experiments.lean:244` `Regev.uniformKey_uniform_advantage_le` | same relabelling (augmented key, ciphertext translation) | Regev's ciphertext is a vector with Regev's codepoint and single-column hash; GSW's is an `(n+1) × N` matrix bounded by the column hybrid. Reused from Regev: `augmented_bijective`, `extractionError_eq` (and `encrypt_eq`, `lift_apply` from `gsw-core`). |
| `distAdv_encrypt_le` (triangle) | `Regev/Experiments.lean:301` `Regev.distAdv_encrypt_le` | same three `abs_sub_le` steps | different view types; a 4-step chain is shorter inline than through `abs_sub_le_sum_hybrids` with a `Fin 5`-indexed function. No generic `distAdv` triangle lemma exists at the base (searched `distAdv_triangle`, `abs_chain_le`, `distAdv_le_add`, `distAdv_trans`: 0 hits). |
| `distAdv_encrypt_le_of_width` | `Regev/Experiments.lean:334` `Regev.two_extractionError_le` | **reused** | — |
| `columnHashParameters` | `Regev/Experiments.lean:154` `Regev.hashParameters` | the disclosed Q11 twin (frozen definition, not introduced here) | used only through its own `simps` readers; `Regev.hashParameters` never unfolded |

**Searches run** (raw output in `evidence/overlap/`): `searches-tcslib.txt` (F5: `hashColumns`, `columnHybrid`,
`columnTest`, `column_gap`, `multicopy`, `abs_sub_le_sum_hybrids`, `exists_hybrid_gap`, `acceptProb_update`,
`uprob_update`, `acceptProb_bind`, `acceptProb_comp_equiv`, `acceptProb_fst`, `acceptProb_snd`,
`distAdv_hash_uniform_le`, `theorem distAdv_*_le`, `theorem uprob_*`, `theorem acceptProb_*`, `theorem uexp_*`,
`Function.update`, `hybrid`, `transpose…Equiv|piComm`, `mul_apply'`); `searches-tcslib-f6.txt` (F6:
`real_uniformKey_advantage`, `uniformKey_uniform_advantage_le`, `distAdv_encrypt_le`, `two_extractionError_le`,
`extractionError`, `augmented_bijective`, `hashParameters`, `columnHashParameters`, `acceptProb_bind`,
`sunglassRed|distAdv_comp`, `abs_sub_le`, `reduction_eq`, `Equiv.addRight`, `Equiv.ofBijective`,
`mul_le_mul_of_nonneg_left`, `distAdv_triangle|abs_chain_le|distAdv_le_add|distAdv_trans`);
`searches-mathlib.txt` (Mathlib at the pin: `mul_apply'`, `mulVec_eq_sum`, `of_apply`, `piComm`,
`ofBijective_apply`, `symm_apply_apply`, `addRight`, `prodCongr`).

## Scope requests

**None.** No frozen file was edited and no import beyond the brief's list was added. Reusing
`distAdv_tuple_le_sum` would have needed one (an import outside `order.txt`); it was not requested (see above).

## Promotion requests

- **P-1 (dedup queue).** A generic shared-parameter hybrid in the probability layer (`Foundations/` or
  `Pseudorandom/Indistinguishability.lean`), for two samplers with *different* seed types
  (`X : κ × σ → γ`, `Y : κ × τ → γ`) over `N` positions including `N = 0`, would serve `distAdv_tuple_le_sum`,
  `Lossy.column_gap`/`concealed_advantage_le` and `distAdv_hashColumns_uniform_le` alike, and make
  `acceptProb_plant` public.
- **P-2 (readers).** `_eq` readers for `pushSampler` and `sunglassRed` (`Indistinguishability.lean:119,125`)
  would let consumers cite `distAdv_sunglassRed` under Rule 10 (here it would give
  `real_uniformKey_advantage` directly from `realView_eq`/`uniformKeyView_eq`).

## Rule 10

- **Reads.** `Columns.lean`: `hash` only through `hash_eq`; `distAdv`/`acceptProb` through `distAdv_def` and the
  published `acceptProb_*` lemmas; its own `hashColumns` through `hashColumns_apply`. `Security.lean`:
  `hashColumns` only through `hashColumns_eq_mul` (Columns is foreign to it); `encrypt` through `encrypt_eq`,
  `lift` through `lift_apply` (`gsw-core`'s readers); `Regev.augmented` only as a function inside
  `Equiv.ofBijective … (Regev.augmented_bijective …)`, never unfolded; `LWE.decisionAdvantage` through
  `decisionAdvantage_eq`; `Regev.extractionError` through `extractionError_eq`; `Regev.hashParameters` not
  used; its own `columnHashParameters` through its `simps` readers and, at the type level, directly (own file).
  Mathlib definitions reduce only in `rfl`/`exact`/`congrArg`/`Prod.ext` definitional steps (`Matrix.mulVec`,
  `Matrix.of`, `Equiv` coercions); none is passed to `simp`, `rw` or `unfold`.
- **Seals** (`evidence/seals/{final-base,final}/`, summary `evidence/final/rule10-summary.txt`): whole-file seals
  of both changed files over their full TCSlib import closures, at the base and at the final, A/B × strict/coe,
  each with `lean -DmaxErrors=0`; every probe harness-valid (one `GSWSEC-INSTALL`, one `GSWSEC-EOF`, all errors
  mapped). Harness adapted from the derand fill's `make_seals.py` (Gate 10 lineage).

  | File (sealed definitions strict / coe) | A strict | **A coe (canonical)** | B strict | B coe |
  |---|---|---|---|---|
  | `Columns.lean` at base (25 / 24) | 0 errors | **0** | 0 | 0 |
  | `Columns.lean` at final (32 / 31) | 0 | **0** | 0 | 0 |
  | `Security.lean` at base (115 / 114) | 0 | **0** | 0 | 0 |
  | `Security.lean` at final (115 / 114) | 0 | **0** | 0 | 0 |

  No failing declaration in any variant, so no difference to attribute. Strict seals exactly one more definition
  than coe: the projection coercion `FinDist.instCoeFunForallReal`. A and B coincide because
  `Complexity.PolyExpr.eval` is in neither file's closure. **Coverage** (`evidence/final/seal-coverage.txt`,
  PASS): in all four `Security` variants `Regev.augmented`, `LWE.sample`, the SIS `hash`, `hashColumns`,
  `encrypt`, `lift`, `gadget`, `Regev.hashParameters`, `Regev.extractionError`, `LWE.decisionAdvantage`,
  `distAdv` and `acceptProb` are sealed; `hash`, `distAdv`, `acceptProb` in all `Columns` variants.
  `Parameters.columns` and `Ciphertext` are reducible abbreviations (notation, never sealed).
- **Controls** (paired; positive = published reader, negative = `rfl` through the body; each negative alone in
  its file): checkpoint 1 with `Columns`' imports (`evidence/controls/cp1/`, 35 probes: `hash`, `distAdv`,
  `acceptProb`, `FinDist` coercion) and final with `Security`' imports (`evidence/controls/final/`, 55 probes:
  `hashColumns` (`hashColumns_apply`), `Regev.augmented` (`augmented_eq`), `LWE.sample` (`sample_fst`),
  `encrypt` (`encrypt_eq`), `distAdv` (`distAdv_def`), `FinDist` coercion). Both `ctlcheck` **ALL_OK**: positives
  pass unsealed and in every variant; every negative passes unsealed and fails **exactly once** in every variant
  that seals its definition (the coercion only in strict). A `PolyExpr.eval` control was prepared and dropped:
  its unsealed pre-check failed with `Unknown identifier` because `PolyExpr` is outside the closure
  (`evidence/logs/dev/precheck-Ctl_polyEval_neg.log`; `make_controls.py` records why).
- **Explicit-unfold scan** (`evidence/final/unfold/`, catalog from the final seal logs, 115 definitions): 90
  selector items in the owned files (base 0): 29 local or own, 61 lemmas, **0 foreign**. PASS.
- **Error counts, both forms (G26-N1)** (`evidence/final/error-counts.txt`, `evidence/checkpoint1/error-counts.txt`;
  regex `^\S+\.lean:\d+:\d+: error([:(])`): final sweep 147 logs, owned checks, all 16 final seals, the axioms
  probe: **0 `error:`, 0 `error(`**. Final controls: 22 `error:`, 0 `error(`, exactly the 22 expected sealed
  negatives (5 × 4 + 2); checkpoint controls 14, likewise expected. Development logs (`evidence/logs/dev/`):
  `columns-01` 1 `error:` (`No goals`), `security-02` 1 `error:` + **4 `error(`** (`lean.unknownIdentifier`:
  unqualified `hashColumns` names, fixed in `security-03`), the dropped pre-check 1 `error(`.

## Checks (final)

| Check | Result | Evidence |
|---|---|---|
| Owned modules, native check (after the last change) | `Columns` and `Security`: 0 errors, 0 `sorry`, no warning | `evidence/final/owned/` |
| Sweep of `order.txt` (147), one Lean process at a time | **ALL 147 OK**, 0 errors in both forms | `evidence/final/sweep.log`, `sweep/` |
| Admissions vs `base-sorries.txt` | 53 in 15 → **47 in 13**; removed exactly the 6 targets; added 0 → PASS | `evidence/final/admissions.txt` |
| Axioms: 6 targets (`#print axioms`) and all 32 stored constants of the two files | only `propext`, `Classical.choice`, `Quot.sound` → PASS | `evidence/final/axioms.log`, `axioms-check.txt`, probe `evidence/axioms/final/Axioms.lean` |
| Dependency trace (constant closure incl. theorem bodies; `sorryAx`) | **no sorried constant reached** from any target (2444–19231 constants visited); no `gsw-core` target reached | same |
| Frozen-statement check + controls | both files 0 differences, order ok (only the import additions, listed ADDED); controls: 1-character header change → exactly 1 difference, deleted reader → exactly 1 removal, in both files | `evidence/headers/` (`frozen_headers.py`, `run_headers.py`, `final/`, `checkpoint1/`) |
| Rule 10 | see above | `evidence/seals/`, `evidence/controls/`, `evidence/final/unfold/` |
| Lint `campaign_style_lint.py TCSlib/Cryptography --check8b` | base **92 FAIL / 101 WARN over 364 files** (= the maintainer's baseline); final identical; line-set diff: only the two owned files' INFO lines (sizes); no FAIL/WARN line for either owned file → PASS | `evidence/lint/` |
| Name-clash scan (namespaces resolved, public + private) | 0 new names → PASS | `evidence/clash/` |
| Widths / sizes (`python3 -I`) | max 100 / 99 characters; 194 and 305 lines → PASS | `evidence/final/widths.txt` |
| Patch reproduction (`git am` at the base, scratch clone, committer identity/date from `COMMITS.tsv`) | both hashes and the final tree reproduced → PASS | `evidence/final/patch-reproduction.txt` |
| Manifests | `SHA256SUMS` and `evidence/SHA256SUMS`: listed paths equal the delivered files exactly; `shasum -a 256 -c` all OK | — |

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
  modules were built by the checkpoint-1 sweep of all 147, in order; the final sweep re-checked all 147.
- **Lean processes:** one at a time throughout (every check serial through `check_module.py`). Peak RSS per
  check ≤ 2.9 GB (`MAXRSS_KIB` in each log; `/usr/bin/time` is absent on this host, so the peak is
  `getrusage(RUSAGE_CHILDREN)`). No `lake build`, no unfiltered `lake exe cache get`; Python always
  `python3 -I`.
- **Check scripts:** module checks and sweeps use `scripts/lean_check_tree.sh` unchanged. Seals, controls
  and probes use `evidence/tools/lean_check_tree_maxerrors0.sh`, a copy differing only in `-DmaxErrors=0`,
  failing on `error[:(]`, and taking the checkout root from the working directory.

## Evidence

All under `inbox/fills/gsw-security/`; `SHA256SUMS` lists every delivered file except itself and
`evidence/SHA256SUMS` every file under `evidence/` except itself (paths equal to the delivered files, no `./`).
- `patches/0001-*.patch`, `patches/0002-*.patch`: the whole `git format-patch 486f44f8..fill/gsw-security`
  series; `patches/COMMITS.tsv`: hash, author and committer name/email/date (raw and ISO), **signing `none`**
  for both (committed with `git -c commit.gpgsign=false`; `%G?` = N, no `gpgsig` header).
- `src/`: the final `Columns.lean` and `Security.lean` under their repository paths (byte-equal to the branch).
- `evidence/logs/`: preflight, toolchain, cache store/roots/fetch, packages check, bootstrap, base checks, the
  development iterations (`dev/`), cache probe.
- `evidence/checkpoint1/` and `evidence/final/`: sweeps (all 147 raw logs each), admissions, axioms (+ check),
  unfold scans, Rule 10 summaries, seal coverage, error counts, widths, patch reproduction, queue outputs; the
  checkpoint REPORT.
- `evidence/seals/{cp1-base,cp1,final-base,final}/`, `evidence/controls/{cp1,final}/`,
  `evidence/axioms/{cp1,final}/`: every probe source, line map, manifest, raw log and `results.jsonl`.
- `evidence/headers/`, `evidence/lint/`, `evidence/clash/`, `evidence/overlap/` (search logs), `evidence/probes/`.
- `evidence/tools/`: every script used (all run as `python3 -I` from the fill checkout's root):
  `check_module.py`, `run_list.py`, `closure.py`, `lean_check_tree_maxerrors0.sh`, `make_seals.py`,
  `run_seals.py`, `make_controls.py`, `check_controls.py`, `seal_coverage.py`, `rule10_summary.py`,
  `explicit_unfold_scan.py`, `make_axioms.py`, `check_sorries.py`, `error_counts.py`, `widths.py`,
  `make_patches.py`, `manifests.py`, and the two queue scripts.
