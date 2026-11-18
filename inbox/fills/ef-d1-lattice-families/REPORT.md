# EF-D1 `ef-d1-lattice-families`: final delivery

**Head:** `876b1cc00e6e54265f2cd1d97de985141b99c2e2` (local branch `fill/ef-d1-lattice-families`, not pushed).
**Base:** IO `5ed465f62e4ae0f93ded1a1ba49e807591b589eb`, tree `9155903018d18fbc735791f21485abaaee3e161a`
(both checked with `git rev-parse` on the fetched `iO/phase-a-base`).
**Records read:** `cryptography/pass-shelat-ch2-4` at `54dcb3021a389831e7f94c3f82616cb7594fa574`: `rulings.md`,
`COMMON.md`, `EF-D1/brief.md`, and every COMMON.md §1 input. All nine SHA-256 values match.
**Merge-tree (information only):** `git merge-tree --write-tree 876b1cc0 83375341b75f71bab3e6f20f94991cf8ad69141b`
(the records tip at delivery) gives tree `1cdea829b26406d87bde812eeefda17e8c040218`, rc 0, no conflicts
(`evidence/checks/merge-tree.txt`).
**Checkpoint 1:** exchange commit `235459a7153397a1140393459ec91df1a2c0b2d6`, head `d01d3f41`.

**Outcome in one paragraph.** Both structures are delivered, compiled and proved:

* `LWE.EfficientFamily` carries a uniform parameter map and the noise sampler in the
  `CoinSampling.SamplesEfficiently` form.
* `SIS.EfficientFamily` carries a uniform parameter map.

Delivered with them: the schedule theorems for both, the bit-seed noise constructors, the polynomial-time core of
`centeredNoise`, and one non-vacuity instance of each structure (no hardness claimed). The assumptions stay on the
raw families. All declarations are seal-clean in all four canonical variants. There are two disclosed deviations:

* **Statement changes.** The noise sampler reads its own uniformly computed parameter word, and the noise output is
  written in sign-magnitude form.
* **Scope request EF-D1-SR1** (one line each). It asks for two missing readers in `LWE/BitNoise.lean`. Until then:
  * the bit-noise and centered-noise theorems take the sample equation as a hypothesis;
  * the LWE instance uses `centeredNoise 0`.

  A probe shows that the readers make the brief's `centeredNoise 1` instance go through unchanged.

## 1. Base check, heads and commits

| # | hash | subject |
|---|---|---|
| 1 | `583c19f9493f5c3d0dcc135d667cc3a9f2eb751a` | LWE.EfficientFamily: uniform parameter map, bit-seed noise sampler in contract form |
| 2 | `d01d3f415f3b5fe88bd9f01a08603687641fb372` | SIS.EfficientFamily: uniform parameter map, dyadic schedules, facade line |
| 3 | `dc2fb62971b7009fb49bd828c763413860bc60d0` | LWE/Efficient: reuse Randomized.onesW instead of a local copy |
| 4 | `876b1cc00e6e54265f2cd1d97de985141b99c2e2` | LWE/SIS Efficient: read PolyExpr.eval through its lemmas; reuse List.count_ofFn |

All commits are unsigned (`%G?` = `N`, and `git cat-file -p HEAD | grep -c gpgsig` = 0). Author and committer are
`Claude <noreply@anthropic.com>` (`patches/COMMITS.tsv`). `git diff --stat <base>` lists only the brief's three
files: `LWE/Efficient.lean` +771, `SIS/Efficient.lean` +308, `SIS.lean` +2 (`evidence/checks/C7-diffstat.txt`).

## 2. Environment, pool and memory (addendum Part 1, *Lean parallelism*)

**Preflight** (`evidence/logs/preflight.log`):

* nproc 4; MemTotal 16.47 GB.
* No cgroup memory limit, so the headroom is MemAvailable: 15.6 GB.
* `/dev/vda` ext4 with 21.4 GB free (floor 12 GiB).
* Scratch directories are on the same filesystem (no tmpfs).
* The toolchain v4.25.0 was installed by elan after the preflight.

**Cache:**

* The archive store `~/.cache/mathlib` was absent before the first fetch (`cache-store.log`). All archives were
  fetched by this session.
* Narrowed fetches, each run alone:
  * 74 roots: 2375 files, rc 0.
  * 9 more roots: 1811 files, rc 0. My closure parser had missed imports after module docstrings.
  * 296 more roots, for the attempted root build: 3587 files, rc 0.
* No empty oleans. The packages check passes; `doc-gen4`, `UnicodeBasic`, `BibtexQuery` and `MD4Lean` are ABSENT
  (`packages-check.log`).

**Disk.** The third fetch left 2.6 GB free. I made my exchange clone sparse, which freed about 8 GB. Nothing else
was moved or deleted.

**Pool** (`evidence/logs/pool.log`): `min(nproc, MemAvailable / 4 GB)` = 3 processes, built in dependency order, one
olean tree (`.lake/tcslib-check-oleans`).

**Builds:**

* Bootstrap: 158 modules, all rc 0 (`logs/bootstrap/pool-run.tsv`). Attempt 1 stopped at a missing import caused
  by the parser bug and is kept in `logs/bootstrap-attempt1/`.
* Closure extensions for the reused hosts: 35 + 5 modules, all rc 0 (`logs/closure2/`, `logs/closure3/`).

**Peak memory.** The peak per-process maxrss was 3.34 GB (`LWE/Efficient`, `closure3`). The peak in the bootstrap
was 2.93 GB. A 4th process (seals and probes) ran next to the pool of 3 only during the root build, so the total
stayed at or below nproc. No shortage occurred: no OOM, no exit 137, and MemAvailable was at least 14.6 GB at every reading in `pool.log`.

**Sub-agents.** None: I worked alone.

## 3. Target map (brief → declarations)

| Brief target | Declarations (`TCSlib/Cryptography/…`) |
|---|---|
| A: `Parameters.encode` + readers | `LWE.Parameters.encode` (LWE/Efficient.lean:93), `encode_eq` :98, `encode_injective` :110 (moduli `≤ 2^w`), component readers `pairFstD_encode` :130, `pairFstD_pairSndD_encode` :135, `pairSndD_pairSndD_encode` :140; bridge to the residue sampler `Family.boundedModulus` :147, `boundedModulus_val` :152, `Family.pairSndD_pairSndD_encode` :158 (= `CoinSampling.modulusWord`) |
| A: `noiseWord` | `LWE.noiseWord` :169 (sign-magnitude; see *Statement changes*), `noiseWord_eq` :172, `noiseWord_injective` :179 |
| A: `EfficientFamily extends Family` | `LWE.EfficientFamily` :208 with fields `params_uniform`, `noiseInput`, `noiseInput_uniform`, `encodeSeed`, `noise_efficient` |
| A: `params_uniform_of_schedule (N M W)` | `LWE.params_uniform_of_schedule` :252 (with `natToList_two_pow` :229, `polyTimeComputable_twoPowWord` :239) |
| A: dyadic schedule constructors | `LWE.dyadicParameters` :271 (+3 readers), `LWE.dyadicFamily` :294 (+5 readers), `dyadicFamily_params_uniform` :325, `EfficientFamily.ofBitSeeds` :657 (+3 readers), `EfficientFamily.ofDyadic` :711 (+2 readers) |
| A: `noise_efficient_of_bitNoise` | generic `drawSamplable_bitSeeds` :425, `noise_efficient_of_bitSeeds` :456; `LWE.noise_efficient_of_bitNoise` :486 (with hypothesis `hs`, see EF-D1-SR1); seed words `seedModulusWord` :338 (+4 readers, `seedModulusWord_uniform` :361), `seedWord` :369 (+2), `seedModulus` :398 (+2), `drawSamplable_restrict` :388 |
| A: `centeredNoise` instance | core `onesCount` :506, `signedDiff` :525, `centeredCore` :564 (each with `_eq` and polynomial-time lemma), `signedDiff_bits` :537, `count_true_ofFn_eq_sum` :584, `centeredCore_ofFn` :596; `CenteredSampleEq` :611 (+`_iff` :616, `centeredSampleEq_zero` :625); `noise_efficient_centeredNoise` :640 |
| A: non-vacuity `dyadicExample` | `LWE.dyadicExample` :743 (`n = κ+1`, `m = 2(κ+1)²`, `q = 2^{κ+1}`, `χ = centeredNoise 0`); `dyadicExample_parameters` :753, `dyadicExample_noise` :767 |
| B: `Parameters.encode (w b)` + readers | `SIS.Parameters.encode` (SIS/Efficient.lean:68), `encode_eq` :75, `encode_injective` :87, `pairFstD_encode` :110, `pairFstD_pairSndD_encode` :115, `modulus_encode` :120, `sqNormBound_encode` :125 |
| B: `EfficientFamily extends Family` | `SIS.EfficientFamily` :139 (field `params_uniform`) |
| B: `params_uniform_of_schedule` | `SIS.params_uniform_of_schedule` :171 (polynomial `n, m, β`, dyadic `q`), with `polyTimeComputable_numeralPoly` :150 |
| B: dyadic schedule + non-vacuity | `SIS.dyadicScheduleParameters` :191 (+4 readers), `SIS.dyadicScheduleFamily` :220 (+5 readers), `SIS.EfficientFamily.ofDyadic` :261 (+1), `SIS.dyadicExample` :285 (`n = κ+1`, `m = 2(κ+1)²`, `q = 2^{κ+1}`, `β = κ+1`, magnitude width `κ+1`), `dyadicExample_parameters` :295 |
| Facade | `SIS.lean`: `import TCSlib.Cryptography.SIS.Efficient` and its `## Contents` line. `LWE.lean` unchanged (maintainer adds the import after #377). |
| No assumption on `EfficientFamily` | none defined. Consumers write `DLWEAssumption F.toFamily`, `SISAssumption F.toFamily` (D1-P2). |

The new Lean comes to 1,079 lines, against the brief's 350–650 (±40% gives up to 910). That is about 170 lines
over. The excess is mostly:

* the readers of the generic constructors, which repeat their long hypotheses;
* the generic bit-seed theorems (`drawSamplable_restrict`, `noise_efficient_of_bitSeeds`);
* the explicit control-friendly readers of the instances.

## 4. Statement changes (COMMON §4.2)

1. **The noise sampler's parameter word**
   * *Old (brief):* the contract's `y κ _` is `(parameters κ).encode (residueBits.eval κ)`.
   * *New:* a field `noiseInput : ℕ → List Bool` with
     `noiseInput_uniform : ∃ f, PolyTimeComputable f ∧ ∀ κ, f (1^κ) = noiseInput κ`. `noise_efficient` uses
     `y κ _ = noiseInput κ`. For bit seeds `noiseInput κ = seedModulusWord n = ⦃2^n⦄_{n+1}`.
   * *Reason:* `DrawSamplable` needs `U.Ω (y κ π) ≃ (noise κ).Coins`. The only registered `UniformSampler`,
     `bucketSampler`, reads its whole word as a numeral (`Ω y = Fin ⟦y⟧`), so it cannot sample `n`-bit seeds at the
     LWE parameter word. A new sampler that reads a component of a pair would be a new sampler instance and its
     machine, outside this brief. The uniformity of the word the sampler reads is kept by `noiseInput_uniform`, so
     there is no advice and no κ-indexed word. Honest algorithms compose both uniform maps.
2. **The noise output form**
   * *Old (brief proposal):* the residue `natToList w ((e : ZMod q).val)`.
   * *New:* `noiseWord e = decide (e < 0) :: Nat.bits |e|`, sign-magnitude with a little-endian magnitude, the
     alternative the brief allows.
   * *Reason:* after change 1, the core reads `⟨1^κ, ⟨noiseInput κ, seed⟩⟩`, which does not contain `q`. A
     modulus-free output keeps the core a pure function of the seed. An honest algorithm reduces modulo `q` with
     `BinArith` after reading `q` from `Parameters.encode` (`Family.pairSndD_pairSndD_encode`).

     The sign convention is that of `SIS.encodeSolution` (`SIS/Encoding.lean:108`), and the magnitude format is
     `BinArith`'s (`Nat.bits`). No width is needed, because `Noise` carries no magnitude bound.
3. **`noise_efficient_of_bitNoise`, `noise_efficient_centeredNoise`, `EfficientFamily.ofDyadic`** take the sample
   equation as a hypothesis: `hs`, and `CenteredSampleEq T`. The reason is EF-D1-SR1 (§9).
   * The bit-seed theorems are stated with `n : ℕ → ℕ` and `hn : ∀ κ, n κ = t.eval κ` instead of only
     `t : PolyExpr`. That way `centeredNoise (T κ)`, with `T κ + T κ` seed bits, instantiates them without casting
     along `PolyExpr.eval_add`.
   * `hgf` is stated on `⟨1^κ, r⟩` rather than on `r` alone. The core may read `κ`, and `centeredCore T` does, to
     split the seed after `T(κ)` bits.
4. **The non-vacuity instance's noise.** The LWE instance uses `χ = centeredNoise 0`, the point law at 0, because
   `CenteredSampleEq (.const 0)` is provable from published readers (`centeredNoise_bounded`, `centeredValue_eq`).
   The brief's example noise `centeredNoise 1` needs EF-D1-SR1. With the proposed readers, `ofDyadic … (.const 1)`
   compiles unchanged (`evidence/scope/SR1-probe.lean`, rc 0, axioms standard).
5. **`encode_injective`** is stated for moduli `≤ 2^w`, matching `Family.modulus_le_pow`, and not `< 2^w`. This is
   possible because the modulus is written at width `w + 1`, as `CoinSampling.modulusWord` does. The SIS version
   also needs `β < 2^b`, which is `Family.sqNormBound_lt_pow`.
6. **Names.**
   * The SIS schedule definitions are `dyadicScheduleParameters` and `dyadicScheduleFamily`, so that they cannot be
     confused with the existing `Hashing.SIS.dyadicParameters` and `dyadicFamily`.
   * `params_uniform_of_schedule` takes the parameter function `P` and equations for its fields, so it applies to
     any family with that schedule, not only to the constructor.

## 5. Checks C1–C13 and D1-P1 to D1-P3

| Check | Result | Evidence |
|---|---|---|
| C1 Build | the 3 modules at the head: rc 0, 0 errors (both forms), 0 `sorry` warnings, each source bound to `git show HEAD:<path>` by SHA-256 | `evidence/build/summary.txt`, `build/*.log` |
| C2 Downstream | the only module that imports the changed `SIS.lean` facade is the root `TCSlib.lean`. **Not run, missing prerequisites** (addendum item 8): its closure has 21 modules (the root and 20 under `CommunicationComplexity/NewmanTheorem`) that import `PFR`/`LeanAPAP`, whose oleans the Mathlib cache does not provide. Building those packages would be a dependency build outside the allowed procedure. Of the root's remaining 1,277 modules, 65 had compiled (all rc 0) when I stopped the build, since it could not reach the root. Substitute evidence: C10 (no full-name clash in the whole tree at three revisions). `SIS.lean` itself compiles at the head. | `logs/downstream-SIS.txt`, `logs/root-blocked-pfr.txt`, `logs/rootbuild/`, `logs/pool.log` |
| C3 Statements | `decls2.py`: 94 ADDED, nothing else; the facade has no declarations. StmtDump: 119 new public constants with full names and types | `checks/C3-decls2.tsv`, `stmt/StmtDump.lean`, `stmt/stmtdump.tsv` |
| C4 Admissions | 0 `sorry`/`admit`/`native_decide`/`axiom`/`opaque` tokens in the new files; the base's `sorry` set is unchanged (no existing file's code changed) | `checks/C4-tokens.txt` |
| C5 Axioms | all 119 constants: `[propext, Classical.choice, Quot.sound]` (92), `[propext, Quot.sound]` (18), `[propext]` (7), `[]` (2); no `sorryAx` | `stmt/axioms.tsv` |
| C6 Rule 10 | canonical seals over the **full import closure** (every ordinary TCSlib definition of another module: defs, matchers and, in strict, instances; reducible abbreviations are notation), `-DmaxErrors=0`. **A-coe: LWE PASS (1,269 requests), SIS PASS (1,294); B-coe 1,271/1,296 PASS; A-strict 1,270/1,295 PASS; B-strict 1,272/1,297 PASS**: 0 failing declarations in every variant, so there are no strict-only failures. Paired controls: LWE 14 NEG + 14 POS, SIS 5 + 5; unsealed all pass, and sealed each NEG fails exactly once while each POS passes (ALL_OK True ×4). Explicit-unfold scan: 0 foreign definitions passed to `simp`/`rw`/`unfold`, and 0 generated-equation references (collector). Reader census: §6 | `seal/canon/seal-summary.txt`, `seal/canon/out-*`, `seal/canon/cand-*`, `seal/controls/ctlcheck.txt`, `seal/unfold-scan.txt`, `seal/collector/` |
| C7 Frozen files | `SIS.lean` compared at base and head: exactly the two allowed insertions, 0 other differences; control (one altered character) → exactly 1 difference. PASS | `checks/C7-facade.txt` |
| C8 Lint | `style_lint.py` on the three files: 0 findings. `campaign_style_lint.py TCSlib/Cryptography --check8b`: base **92 FAIL / 103 WARN over 542 files** (the maintainer's IO figure); head 93 / 103 over 544. The one new line is the disclosed `FAIL TCSlib/Cryptography/LWE.lean facade does not import child module TCSlib.Cryptography.LWE.Efficient`. No other new FAIL or WARN | `checks/C8-*` |
| C9 Sizes | `LWE/Efficient.lean` 771 lines, max width 99; `SIS/Efficient.lean` 308 lines, max width 99; `SIS.lean` 30 lines, max width 91 | `checks/C9-sizes.txt` |
| C10 Clashes | full-name clashes in `TCSlib/` and `audits/`: 0 at the IO base, 0 at #377's head `7563734a`, 0 at `cleanup/stage2-s2a` (`c119a3c4`). Short names declared elsewhere: `dyadicFamily`, `dyadicParameters` (`Hashing.SIS.*`), `encode`, `encode_eq`, `encode_injective` (`BoolCircuit.*`, `Complexity.QBF`, `Randomized.Alg*`, `TrapdoorFunctions.Lossy`). The only modules downstream of the new files are `SIS.lean` and the root `TCSlib.lean`, which contain no code, so no unqualified use can change its resolution. `Hashing.SIS.*` does not import the new files | `checks/C10-clashes.txt` |
| C11 Reuse and overlap | §7 | `checks/C11-searches.txt` |
| C12 Probes | §5 rows D1-P1 to D1-P3 | `probes/` |
| C13 Reproduction | `git am` of `patches/` at the base in a scratch worktree, under `COMMITS.tsv`'s committer data, reproduces all 4 hashes and the head; `src/` equals the head's files byte for byte | `checks/C13-repro.txt` |
| D1-P1 | `LWE.dyadicExample` and `SIS.dyadicExample` elaborate. `#eval` of the parameter words at `κ = 0..3` matches `⟨1^{κ+1}, ⟨1^{2(κ+1)²}, 1 0^{κ+1}⟩⟩` (LWE) and `⟨…, ⟨1 0^{κ+1}, ⦃κ+1⦄_{κ+1}⟩⟩` (SIS), plus a kernel `decide` check for LWE at `κ < 4`. `noiseWord` and `centeredCore` sample outputs printed | `probes/D1P1.lean`, `.out` |
| D1-P2 | `fun F h D => h D` for `LWE.DLWEAssumption F.toFamily` and for `SIS.SISAssumption F.toFamily`; an `LWE.EfficientFamily` passes to a #377-style `F : LWE.Family` statement as `F.toFamily` | `probes/D1P2.lean`, `.out` |
| D1-P3 | `dyadicExample.noise_efficient` (and `params_uniform`, `noiseInput_uniform`, SIS `params_uniform`) are proof terms with axioms `[propext, Classical.choice, Quot.sound]` | `probes/D1P3.lean`, `.out` |

## 6. Reader census (Rule 10)

Every foreign definition the new files read (the collector's candidates, `seal/collector/*.txt`), with its reader:

| Foreign definition | Reader(s) used |
|---|---|
| `Turing.pairEncode`, `Complexity.pairFstD`, `pairSndD` | `pairFstD_pairEncode` (ClassNP/PolyTimePairing.lean:233), `pairSndD_pairEncode` (:237) |
| `Complexity.BinArith.countLoop` | `countLoop_eq` (ClassP/BinaryArith/PrimeFind.lean:172) |
| `Complexity.BinArith.le`, `sub` | `le_pairEncode` (ClassP/BinaryArith/AddSub.lean:202), `sub_pairEncode` (:152) |
| `Randomized.onesW` | `length_onesW` (Randomized/BiasedCoinHalting.lean:452), `polyTimeComputable_onesW_snd` (:538) |
| `Complexity.NUPPT.advInput` | `advInput_eq` (Randomized/PPT.lean:214) |
| `Complexity.LogProg.bitsVal` | `bitsVal_bits` (SpaceComplexity/Machines/Bin.lean:67) |
| `Complexity.PolyTimeComputable` | its composition lemmas only (`comp'`, `congr`, `pairEncode`, `polyTimeComputable_ite`, …) |
| `TCSlib.Cryptography.bitsEquiv`, `bitsToNat` | `bitsEquiv_val` (Asymptotic/Sampling.lean:457), `bitsToNat_eq_listToNat` (NumberTheory/Primality.lean:663) |
| `Candidates.natToList`, `NumberTheory.listToNat` | `natToList_length_listToNat` (Candidates/Arithmetic.lean:173), `natToList_injOn` (:161), `listToNat_natToList` (:143), `length_natToList` (:107), `listToNat_replicate_false` (:230), `listToNat_cons` (Primality.lean:672) |
| `Encoding.BinaryArith.fromLEPoly` | `fromLEPoly_pairEncode` (Encoding/BinaryArith.lean:216) |
| `CoinSampling.DrawSamplable`, `CoreComputable`, `SamplesEfficiently` | `drawSamplable_iff` (CoinSampling/Contract.lean:96), `coreComputable_iff` (:113), `SamplesEfficiently.intro` (:176), `DrawSamplable.congr` (:246), `drawSamplable_residue` (:348) |
| `CoinSampling.modulusWord`, `residueEnc` | `modulusWord_eq` (Contract.lean:317), `residueEnc_eq` (:335) |
| `CoinSampling.CoinSampler.fail` | only inside `drawSamplable_iff`'s statement (not read) |
| `LWE.bitNoise` | `bitNoise_Coins` (LWE/BitNoise.lean:45). **MISSING:** a sample reader at `Coins`-typed seeds, proposed `bitNoise_sample_cast` (EF-D1-SR1) |
| `LWE.centeredNoise` | `centeredNoise_Coins` (:85), `centeredNoise_bounded` (:96). **MISSING:** `centeredNoise_sample_cast` (EF-D1-SR1) |
| `LWE.centeredValue` | `centeredValue_eq` (BitNoise.lean:73) |
| `LWE.Noise.Bounded` | `Noise.bounded_iff` (LWE/Noise.lean:61) |
| `Complexity.PolyExpr.eval` (notation; sealed in variant B) | `eval_const`, `eval_var`, `eval_add`, `eval_mul`, `eval_pow` |

## 7. Overlap and reuse (C11)

**Searches.** `evidence/checks/C11-searches.txt` lists 17 `git grep` queries at the IO base, with hit counts and the
first hits. Further checks:

* the clash scan (`checks/C10-clashes.txt`), which found the `onesW` and `count_true_ofFn` near-duplicates below;
* `#check` probes for `List.count_ofFn`, `Finset.card_filter` and `Finset.sum_boole` in Mathlib, and searches of
  core/Batteries for `count_ofFn`.

**Removed before delivery.** Both were exact or near restatements, found by my own sweep:

* a local `onesW` transducer identical to `Randomized.onesW` (`Complexity/Randomized/BiasedCoinHalting.lean:448`),
  removed in commit 3;
* a local induction for `count true (ofFn g)`, replaced by `List.count_ofFn` (`Programs/Util/List.lean:396`) in
  commit 4;
* also removed: a second copy of `natToList_two_pow` that the SIS file had in an early draft (never committed);
  SIS imports the LWE one.

**Must-reuse items of the brief, and where they are used:**

* `CoinSampling.SamplesEfficiently` / `SamplesEfficiently.intro`: `EfficientFamily.noise_efficient`,
  `noise_efficient_of_bitSeeds`.
* `samplesEfficiently_iff_exists`: not needed; the halves' readers are used instead.
* `DrawSamplable`, `drawSamplable_residue`, `DrawSamplable.congr`: `drawSamplable_bitSeeds`, which is
  `drawSamplable_residue` restricted to `q = 2^n` and transported to the seed type. It needs no new sampler.
* `CoreComputable` / `coreComputable_iff`: `noise_efficient_of_bitSeeds`.
* `CoreComputable.map`: not used; the core is built directly by `coreComputable_iff`, a composition of the
  polynomial-time `g`.
* `bucketSampler`: through `drawSamplable_residue`.
* `samplesEfficiently_residue`: through `drawSamplable_residue`; uniform residues for the honest algorithms come
  through `Family.pairSndD_pairSndD_encode`.
* `BoundedModulus`, `modulusWord`, `residueEnc`: `Family.boundedModulus`, `seedModulus`, `modulusWord_seedModulus`,
  `Family.pairSndD_pairSndD_encode`.
* `CoinSampler.noiseSeeds`, `lweSeeds`: not used. They are seed-level samplers of a `Noise` and of LWE samples (no
  machine), and this job states no seed-level law. No restatement: `drawSamplable_bitSeeds` is the efficiency of
  bit seeds, which `noiseSeeds` does not provide.
* `LWE.bitNoise`, `bitNoise_Coins`: `noise_efficient_of_bitNoise`. `bitNoise_sample` cannot be read at `Coins` seeds
  under the seal (EF-D1-SR1).
* `centeredNoise`, `centeredValue_eq`: `noise_efficient_centeredNoise`, `centeredCore_ofFn`.
* `Candidates.natToList`, `listToNat_natToList`: encodings and their injectivity.
* `EnsembleLemmas.polyTimeComputable_zeros`: `polyTimeComputable_twoPowWord`.
* `polyTimeComputable_polyUnary`: not used. `polyTimeComputable_unaryPoly` (`Randomized/Primitives.lean:155`), the
  `PolyExpr` form, is used instead. `polyTimeComputable_zerosPoly` is likewise replaced by `_zeros`.
* `BinArith` with the `Encoding/BinaryArith` adapters: `countLoop`, `le`, `sub` (`onesCount`, `signedDiff`) and
  `fromLEPoly` (`SIS.polyTimeComputable_numeralPoly`).

**Near-relatives, disclosed:**

* `signedDiff` vs `Hashing/SIS/CollisionOutput.lean:245`. That file has a local `block` that writes the signed
  difference of two *bits* inside a proof. `signedDiff` writes the sign-magnitude difference of two *binary
  numbers*, polynomial-time. Not a restatement.
* `noiseWord` vs `SIS.encodeSolution` (`SIS/Encoding.lean:108`). Same sign convention; `encodeSolution` writes the
  magnitude MSB-first at a fixed width per coordinate, while `noiseWord` writes one integer with a variable-width
  `Nat.bits` magnitude, so that it matches `BinArith` and needs no bound.
* `count_true_ofFn_eq_sum` vs `TCSlib.Cryptography.count_true_ofFn` (`Asymptotic/HardCoreGL.lean:76`) and
  `List.count_ofFn` (`Programs/Util/List.lean:396`). The same left side; mine has the `Σ toNat` right side that
  `centeredValue` uses. It is derived from `List.count_ofFn` by `Finset.card_filter`, with no re-derivation.
* `onesCount` (binary count of ones) vs `ZeroKnowledge/ThreeColoring/Machines.lean:347` `countTrue` /
  `countTrue_poly` (unary prefix count). `onesCount` instead composes the existing `Randomized.onesW` with
  `BinArith.countLoop`, which keeps the ZK course file out of the LWE layer.
* `natToList_two_pow` (`⦃2^w⦄_{w+1} = 1 0^w`) vs `CoinSampling.bitsVal_replicate_false_append_true`
  (`Efficiency.lean:227`, the little-endian `0^w 1`) and a `private` relative in `Candidates/Factoring.lean:189`.
  No public statement of the MSB form exists.
* `drawSamplable_restrict` (restriction of `DrawSamplable` to a section of the public input) is a general contract
  lemma. Its natural home is `CoinSampling/Contract.lean`, which is frozen; it is stated once, public, here
  (question EF-D1-W2).
* `Hashing.SIS.dyadicParameters` / `dyadicFamily` (`Hashing/SIS/Profiles.lean:65`, `:79`): not used, per the brief.
  The SIS schedule here is local and differently named. EF-H4 builds the efficient hashing instance.

**Imports.** `SIS/Efficient.lean` imports `LWE/Efficient.lean` only for `LWE.natToList_two_pow` and
`LWE.polyTimeComputable_twoPowWord`, which are stated once. This adds no hardness dependency, but it does make the
SIS facade pull in the LWE efficiency layer (question EF-D1-W2).

## 8. Scope requests

**EF-D1-SR1 (E-SCOPE, readers only, `TCSlib/Cryptography/LWE/BitNoise.lean`).**

* *The problem.* `bitNoise_sample` and `centeredNoise_sample` are stated at seeds of type `Fin _ → Bool`, relying on
  `(bitNoise t f).Coins ≡ (Fin t → Bool)` by definition. Under the canonical seal (`bitNoise` and `centeredNoise`
  irreducible), neither can be used at a seed of type `(bitNoise t f).Coins`, which is the type `EfficientFamily`'s
  `noise_efficient` quantifies over. `evidence/scope/SR1-sealdemo.lean` shows both fail exactly once sealed.
* *The fix.* Two one-line readers, proved by `rfl` in their owner file. The exact text is in
  `evidence/scope/EF-D1-SR1-BitNoise.patch.txt`:
  * `bitNoise_sample_cast : (bitNoise t f).sample c = f (cast (bitNoise_Coins t f) c)`;
  * `centeredNoise_sample_cast : (centeredNoise t).sample c = centeredValue t (cast (centeredNoise_Coins t) c)`.
* *What stays blocked until then:* the unconditional forms of `noise_efficient_of_bitNoise` and
  `noise_efficient_centeredNoise`, and a `centeredNoise 1` example. The head carries the hypotheses `hs` and
  `CenteredSampleEq T` instead.
* *Landing edits once the readers land* (one line each): drop `hs` and use `bitNoise_sample_cast`; add
  `centeredSampleEq (T) := (centeredSampleEq_iff T).2 fun κ c => centeredNoise_sample_cast _ c`; optionally switch
  `dyadicExample` to `(.const 1)`. `evidence/scope/SR1-probe.lean` (rc 0) builds exactly that instance with the
  readers stated locally.

No other scope request. A related observation for the maintainer, outside my files:
`CoinSampling.drawSamplable_residue` (`Contract.lean:348`) reads `bucketSampler.Ω y` as `Fin ⟦y⟧` by definition
across files. `Efficiency.lean` publishes no `bucketSampler_Ω` reader. My files avoid this by consuming
`drawSamplable_residue` itself.

## 9. Questions for Seyoon

* **EF-D1-W1 (SR1).** Should the two sample readers be added to `LWE/BitNoise.lean`?
  * **(A, recommended)** Add them at landing and apply the three one-line edits, which makes the bit-noise and
    centered theorems unconditional and the example `centeredNoise 1`.
  * (B) Keep the hypothesis forms as delivered.
* **EF-D1-W2 (shared helpers).**
  * **(A, recommended)** Promote `natToList_two_pow`, `polyTimeComputable_twoPowWord` and `drawSamplable_restrict`
    at the next shared-file window: the first two to `Encoding/BinaryArith.lean` (or `CoinSampling/Contract.lean`
    beside `modulusWord`), the third to `CoinSampling/Contract.lean`. Then drop `SIS/Efficient.lean`'s import of
    `LWE/Efficient.lean`.
  * (B) Keep them where they are.
* **EF-D1-W3 (noise output).**
  * **(A, recommended)** Accept the sign-magnitude `noiseWord`, with residue reduction in the honest algorithms
    (EF-H4 and later).
  * (B) Require the residue form. That would mean a `UniformSampler` reading a pair component (new sampler machine),
    or a core that recomputes `q` from `1^κ`.

## 10. Evidence manifest

`evidence/SHA256SUMS` covers every evidence file. The top-level `SHA256SUMS` covers every delivered file except
itself.

* `logs/`:
  * `preflight.log`, `cache-store.log`, `cache-get*.log`, `packages-check.log`;
  * `mathlib-roots*.txt`, `order-*.txt`, `pool.log`;
  * `bootstrap/` and `bootstrap-attempt1/`, `closure2/`, `closure3/` (per-module logs, `pool-run.tsv`);
  * `rootbuild/` (partial; see C2), `root-blocked-pfr.txt`, `downstream-SIS.txt`;
  * `dev/` (development compile logs at earlier states), `finalchecks.out`.
* `build/`: C1 logs and `summary.txt` at the head.
* `checks/`: C3, C4, C7, C8 (lint outputs and diff), C9, C10, C11 searches, C13 reproduction, merge-tree.
* `stmt/`: `StmtDump.lean`, `stmtdump.tsv`, `axioms.tsv`.
* `seal/`:
  * `canon/`: candidate lists per variant, `AllDefs-*.lean` generator, seal outputs and `seal-summary.txt`;
  * `controls/`: control bodies and files, outputs, `ctlcheck.txt`;
  * `collector/`: the gate-04 collector output at the head;
  * `unfold-scan.txt`;
  * `cand-dev/`, `out-dev/`: the referenced-candidate seal at an earlier development state, kept.
* `probes/`: D1-P1 to D1-P3 (`.lean`, `.out`, `.rc`).
* `scope/`: EF-D1-SR1 patch text, seal demonstration and probe.
* `tools/`: my scripts (`closure.py`, `pool.py`, `mkpayload.sh`, `finalchecks.sh`, `AllDefs.lean.tmpl`,
  `ctlcheck.py`, `unfoldscan.py`, `c7facade.py`, `c10clash.py`, `c13repro.sh`, `decls2_lib.py`).
  * Copies of the gate-04 tools used: `seal_canon.py` (one change, `-DmaxErrors=0`, noted in its header),
    `run_collect.sh` (one change: `MODS` may override `mods.txt`), `collect_body.lean`, `gen_collect.py`,
    `unsealable.py`, `declx.py`.
