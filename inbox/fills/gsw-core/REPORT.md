# Fill `gsw-core` — final (F1 Gadget, F2 Noise, F3 Scheme, F7 Symmetric, F4 Eval)

**Result: all 29 targets proved**, standard axioms only (`propext`, `Classical.choice`,
`Quot.sound`); no target reaches `sorryAx`. No statement weakened, no hypothesis or definition
changed, no frozen file touched, no scope request.

**Worker** Claude, a lead with two sub-agents (A, B). **Issue base**
`486f44f8414c20a2d21e452c44de8b8c8d8513a0` (head of draft PR #333, `stmt/gsw`), verified to contain
#332's `94eae71b779c4ca0f76c138d699f4d737dbd6cee` (`git merge-base --is-ancestor`). The pack was read
at exchange commit `523d4e97302606b0301ecbcff13882abb917ec1f`; `shasum -a 256 -c SHA256SUMS` in
`outbox/fills/gsw-core/` reported all 7 files OK. Local branch `fill/gsw-core` (never pushed), final
head `d4ebb0be088e5985337ccb4e0a61cb3a662e8b73`. Lean 4.25.0; Mathlib and packages at the base's
`lake-manifest.json`. Checkpoint 1 was delivered as exchange commit `5b72e346b`.

## Status of the 29 targets

| Unit | File | Targets | Status | Prover |
|---|---|---|---|---|
| F1 | `Gadget.lean` | `digits_decomposeVec`, `gadget_mulVec_decomposeVec`, `gadget_mul_decompose`, `decomposeVec_block_eq_false`, `errorSum_decomposeVec_le` | proved | sub-agent A |
| F2 | `Noise.lean` | `encrypts_gadget`, `encrypts_zero`, `Encrypts.mono`, `.add`, `.neg`, `.sub`, `.sum`, `.mul`, `.mul_bit`, `.mul_le`, `.nand`, `encrypts_chain` | proved | sub-agent A |
| F3 | `Scheme.lean` | `vecMul_secretVector_augmented`, `encrypts_encrypt`, `encrypts_keygen_encrypt`, `decrypt_of_encrypts`, `decrypt_of_encrypts_dyadic`, `decrypt_keygen_encrypt` | proved | sub-agent B |
| F7 | `Symmetric.lean` | `encrypts_symEncrypt`, `distAdv_symEncrypt_le` | proved | sub-agent B |
| F4 | `Eval.lean` | `homAnd_encrypts`, `homGate_encrypts`, `eval_encrypts`, `decrypt_keygen_eval` | proved | lead |

Admissions: 35 at the base → **6**, exactly the `gsw-security` ones (`Hashing/SIS/Columns`:
`hashColumns_eq_mul`, `distAdv_hashColumns_uniform_le`; `GSW/Security`: `real_uniformKey_advantage`,
`uniformKey_uniform_advantage_le`, `distAdv_encrypt_le`, `distAdv_encrypt_le_of_width`). Removed: the
29 targets; added: none (`evidence/sorries/final.txt`).

## Commits (`patches/`, `patches/COMMITS.tsv`)

1. `243a44cdb` — F1, F2 (Gadget.lean, Noise.lean; sub-agent A's files, integrated by the lead).
2. `a1bc6aacd` — F4 (Eval.lean; lead). At this commit `decrypt_keygen_eval` was proved modulo F3.
3. `d4ebb0be0` — F3, F7 (Scheme.lean, Symmetric.lean; sub-agent B's files, integrated by the lead).

Every commit was made with `git -c commit.gpgsign=false` and none is signed (`signing` = `none`).
**Reproduction checked before the push:** a scratch clone at the base applies the series with
`git am` under the recorded committer identity and date, reproduces all three hashes, and its files
equal `src/` (`evidence/logs/patch-reproduction.log`).

## Changed files

| File | Lines base → final | Edits |
|---|---|---|
| `TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Gadget.lean` | 204 → 236 | 5 bodies; sketches rewritten for `gadget_mulVec_decomposeVec`, `gadget_mul_decompose`, `decomposeVec_block_eq_false` (last sentence), `errorSum_decomposeVec_le` |
| `…/GSW/Noise.lean` | 235 → 321 | 12 bodies; sketches rewritten for `encrypts_gadget`, `encrypts_zero`, `.add`, `.neg`, `.mul`, `.mul_bit`, `.mul_le`, `.nand`, `encrypts_chain` |
| `…/GSW/Scheme.lean` | 215 → 364 | 6 bodies; 2 private helpers; sketches rewritten for the first five targets (`decrypt_keygen_encrypt`'s already matched) |
| `…/GSW/Symmetric.lean` | 111 → 185 | 2 bodies; 1 private helper; both sketches rewritten |
| `…/GSW/Eval.lean` | 209 → 321 | 4 bodies; `homGate_encrypts` sketch rewritten (the other three already described the delivered proofs) |

Statement prose before every sketch, every header, definition, reader, `variable`, `section`, `open`,
`set_option` line, import and module docstring is byte-identical (`evidence/headers/final/`). No
import was added, so no new Mathlib root and no extra cache fetch. Every proof of 15 lines or more
has a sketch and step comments.

## New declarations

All three are `private` glue with a docstring and no source tag. None is public, so `## Main
results` is unchanged and lint check 8 is not engaged.

- `Scheme.lean:201` `halfVector_eq_zero_of_ne_last (P) (j) (hj : j ≠ Fin.last _) : halfVector P j = 0`.
- `Scheme.lean:213` `decrypt_eq_decode_errorSum`: from `Encrypts P (secretVector P s) b.toNat β C`,
  there is a `β`-bounded `e` with `decrypt P s C = decode (codepoint b + ↑(∑ i, e i *
  (decomposeVec P (halfVector P) i).toNat))`. It is shared by `decrypt_of_encrypts` and `_dyadic`.
- `Symmetric.lean:110` `exists_equiv_symEncrypt (P hN μ)`: there is
  `E : (A, b) ≃ (Fin k → Ciphertext P)` with `E c = symEncrypt P hN c μ`.

Name-clash scan: none of these names is declared anywhere in `TCSlib/` at the base
(`evidence/clash/final.txt`).

## Routes (as delivered; Gate 41's routes worked as written)

- **F1.** `digits_eq`, `decomposeVec_eq`, `Equiv.apply_symm_apply`. `gadget_mulVec_decomposeVec`
  casts `Lossy.gadget_mulVec` through `Int.cast_sum`/`Int.cast_mul`. `errorSum_decomposeVec_le`
  reindexes through `finProdFinEquiv`, zeroes blocks `j ≠ j₀` with `decomposeVec_block_eq_false`,
  and applies `LWE.binaryErrorSum_bound` with `m := ℓ`.
- **F2.** `Encrypts.mul` keeps the exact `x₁.natAbs * β₂` term, with witness
  `j ↦ (∑ᵢ e₁ i · X i j) + x₁ · e₂ j`, using `Matrix.vecMul_vecMul`, `Matrix.add_vecMul`,
  `Matrix.smul_vecMul`, `gadget_mul_decompose`, `LWE.binaryErrorSum_bound` and `Int.natAbs_mul`.
  `encrypts_chain` inducts on the `Forall₂` with the head on the left.
- **F3.**
  - `vecMul_secretVector_augmented`: `Fin.sum_univ_castSucc`, `Fin.snoc_*`, `augmented_eq`,
    `noisyValues_apply`.
  - `encrypts_encrypt`: witness `j ↦ ∑ᵢ eᵢ·R i j` with bound `m·B`.
  - `decrypt_of_encrypts`: through `decrypt_eq_decode_errorSum`, then `errorSum_decomposeVec_le`
    at `j₀ = Fin.last _` and `decode_codepoint_add` with `B := ℓ·β`.
  - `_dyadic`: the decomposition of `⌊q/2⌋ e_last` is the indicator of `(last, ℓ−1)`
    (`Lossy.digits_injective`, `digits_decomposeVec`, `Lossy.digits_val`), so the error sum is
    `e i₀`.
- **F7.**
  - `encrypts_symEncrypt`: `Matrix.submatrix_apply` and `vecMul_secretVector_augmented`.
  - `distAdv_symEncrypt_le`: `acceptProb_def` on the real side. On the ideal side,
    `acceptProb_comp_equiv` with `exists_equiv_symEncrypt` (`Equiv.ofBijective` of
    `Regev.augmented_bijective`, column reindexing by `rowEquiv`, then `Equiv.addRight` by
    `μG`). The bound follows from `LWE.decisionAdvantage_eq`, `distAdv_def` and `abs_sub_le`.
- **F4.**
  - `homAnd_encrypts`: induction on the `Forall₂`, following `homAnd`'s three equations.
  - `homGate_encrypts`: `List.forall₂_map_*_iff`, `List.forall₂_same`, `List.all_map` and the
    `length ≤ 2` bound. `¬` is `G − ·`; `∨` is De Morgan via `List.any_eq_not_all_not`.
  - `eval_encrypts`: `runWith_rel` with
    `R v b C := Encrypts P t b.toNat ((N+1)^{Cc.depthAt v}·β) C`, using `depthAt_input`,
    `depthAt_gate`, `depthAt_eq`, `DAGGate.depth_eq`, `DAGGate.getD_lt_depth`, `.mono` and
    `homGate_encrypts`. The output is read with `Cc.eval_eq`, `values_eq`, `depth_eq`,
    `eval_eq` and `evalValues_eq`. `IsFaninTwo` is not used and no reader was added.
  - `decrypt_keygen_eval`: `encrypts_keygen_encrypt`, `eval_encrypts`, then `.mono` with
    `Nat.pow_le_pow_right`, then `decrypt_of_encrypts` with `hsep` verbatim. No extra factor,
    no `L+1`.

## Overlap and reuse

The new declarations and the inline `have`s that restate, specialize or re-prove existing material:

1. **`decrypt_eq_decode_errorSum`** (private, Scheme).
   - Nearest relative: `Regev.encrypt_residual`
     (`TCSlib/Cryptography/Encryption/PublicKey/Regev/Basic.lean:105`), which has the same
     shape, "residual = codepoint + integer error sum".
   - Not reusable: the GSW decryption column is not a `Regev.encrypt` output. Its residual
     comes from the GSW invariant and `G·G⁻¹(w) = w`.
   - `decode_codepoint_add`, `errorSum_decomposeVec_le` and `gadget_mulVec_decomposeVec` are
     reused.
2. **`exists_equiv_symEncrypt`** (private, Symmetric). Its relatives are inline `let`s inside
   other proofs, so they cannot be reused:
   - the translation equivalence in `Symmetric.Regev.acceptProb_uniform_shift`
     (`TCSlib/Cryptography/Encryption/Symmetric/Regev/Experiments.lean:77`);
   - `keyEquiv := Equiv.ofBijective (augmented P) …`
     (`TCSlib/Cryptography/Encryption/PublicKey/Regev/Experiments.lean:260`).

   It composes the published `Regev.augmented_bijective`, a block reindexing through `rowEquiv`
   (no relative found; Mathlib's `Matrix.reindex` and `Equiv.curry` do not give the `Fin k`-block
   shape) and Mathlib's `Equiv.addRight`.
3. **`halfVector_eq_zero_of_ne_last`** (private, Scheme): no relative (searched `halfVector`).
4. **Inline `hX`** in `Encrypts.mul` states that `e₁ᵗ · lift X` is the residue of the integer
   binary sum. The inline **`herr`** in `decrypt_eq_decode_errorSum` and the last step of
   `encrypts_encrypt` repeat the same cast pattern.
   - Relatives: the inline `herr` of `Regev.encrypt_residual` (`Regev/Basic.lean:119`) and the last
     step of `Lossy.residual_conceal` (`TCSlib/Cryptography/TrapdoorFunctions/Lossy/Matrix.lean:128`).
   - These are 2–3 lines of `Int.cast_sum`/`Int.cast_mul`/`Int.cast_natCast` glue. No stated
     lemma exists to reuse.
5. **Bool-message identities.** `((a && c).toNat : ℤ) = a.toNat * c.toNat` and
   `((!c).toNat : ℤ) = 1 − c.toNat` are proved inline by `cases … <;> rfl`:
   - in Noise: `Encrypts.mul_le`, `.nand`, `encrypts_chain`;
   - in Eval: `homAnd_encrypts`, `homGate_encrypts`;
   - in Scheme: `hb` in `decrypt_eq_decode_errorSum` is the codepoint analogue.

   No core, Mathlib or batteries lemma states them over `ℤ`. A shared public lemma would change
   Noise's interface, so they are kept inline (disclosed).
6. **Inline `hs`** in `encrypts_keygen_encrypt` (`Prod.ext (sample_fst) (sample_snd)`) repeats the
   inline `hsample` of `Regev.decrypt_keygen_encrypt` (`Regev/Basic.lean:168`). It is two lines,
   and that relative is not exported.
7. **Inline `hz`/`hsum`** in `decrypt_of_encrypts_dyadic` (the indicator decomposition): no
   existing statement. It is proved from `Lossy.digits_injective`, `Lossy.digits_val`,
   `digits_decomposeVec`, `digit_val` and Mathlib's `Fintype.sum_eq_single`.
8. **Inline `hlen`** in `homGate_encrypts`: arithmetic glue, no relative.
9. **Reused, not re-proved:**
   - `LWE.binaryErrorSum_bound` (`TCSlib/Cryptography/LWE/Basic.lean:79`; its specializations
     `Regev.subsetError_bound` and `Lossy.error_sum_bound` are not used);
   - `Lossy.gadget_mulVec`, `digits_val`, `digits_eq`, `digits_injective`;
   - `Regev.augmented_eq`, `augmented_bijective`, `decrypt_eq`, `keygen_fst`/`_snd`;
   - `LWE.sample_fst`/`_snd`, `noisyValues_apply`, `Noise.bounded_iff`, `decisionAdvantage_eq`;
   - `BitEncoding.codepoint_eq`, `decode_codepoint_add`;
   - `acceptProb_def`, `distAdv_def`, `acceptProb_comp_equiv`;
   - `runWith_rel`, `DAGGate.getD_lt_depth`, `depthAt_input`, `depthAt_gate`, `depthAt_eq`;
   - Mathlib's `List.getD_eq_getElem`/`List.getElem_ofFn` for `getD` of `List.ofFn` (no new
     copy of the DL-47 family).

Searches (details in `evidence/subagents/{A,B}/REPORT.md`):
- `grep -rn` over `TCSlib/` for `Int.cast_sum`, `error_sum_bound|subsetError_bound`, `toNat`,
  `halfVector`, `exists_equiv`, `decode_errorSum`, `sample_eq`, `ofBijective`, `encrypt_residual`,
  `digits_injective`, `blocksEquiv`, `runWith_rel|runWith_sim|runWith_remap_rel` and
  `getD_eq_getElem|getElem_ofFn`;
- core, Mathlib and batteries for `toNat_and|toNat_not|toNat_mul`;
- `#check` probes for every Mathlib name used (`evidence/lead/probes/LeadNames.lean`,
  `evidence/subagents/A/probes/NamesA.lean`, `evidence/subagents/B/probes/B_names1.lean`).

## Scope requests and promotion requests

None. The two inline Bool identities (item 5) could become a small public helper if the maintainer
wants one; no promotion is requested.

## Who proved what

- **Sub-agent A** (worktree `/home/user/gsw-A`, own TCSlib olean tree) proved F1 and F2, 17
  targets. Its evidence is in `evidence/subagents/A/`. The harness refused a sub-agent-written
  `.md` report there, so the lead saved A's returned report as `REPORT.md`.
- **Sub-agent B** (worktree `/home/user/gsw-B`, own TCSlib olean tree) proved F3 and F7, 8 targets,
  with the three private helpers. Its evidence is in `evidence/subagents/B/`. B's `scheme-004.log`
  is a stale run: a patch command of B's hung on stdin for about 30 minutes before writing, which
  B disclosed in its WORKLOG. `scheme-005` had 2 errors, fixed in `scheme-006`.
- **The lead** proved F4 (4 targets). It also integrated each sub-agent's files unchanged (SHA-256
  checked against their `final/` copies and reports), made every commit, ran all final checks and
  delivered.
- All Lean runs, by the lead and both sub-agents, went one at a time through one `flock` on
  `/home/user/gsw/.lean.lock` (`evidence/tools/runlean.py`, `chk.sh`, `seal.py`). Only the lead ran
  `lake`. There was no `lake build` and no unfiltered cache fetch. The sub-agent rules are in
  `evidence/tools/SUBAGENT-RULES.md`.

## Environment (addendum Part 1)

- **Preflight** (`evidence/logs/preflight.log`):
  - `nproc` 4;
  - cgroup v1, limit 14,338,772,992 B;
  - memory in use (usage − total_cache + total_shmem) 470,822,912 B, so the **headroom is
    12.92 GiB**;
  - the clone is on ext4 (`/dev/vda`) with **15.65 GiB free**; no tmpfs is used.
  - Re-check before the cache fetch (after the elan toolchain install): 13.2 GiB free.
- **Cache store** (`evidence/logs/cache-store.log`): `/root/.cache/mathlib` was absent before the
  fetch, so 0 archives were pre-existing.
- **Narrowed fetch** for the **38** roots. These were recomputed from `order.txt` and are identical
  to `roots.txt` (`evidence/logs/mathlib-roots.txt`). The log shows "Attempting to download 2060",
  "Decompressing 2060" and "Completed successfully" (`evidence/logs/cache-get.log`).
- **Packages** (`evidence/logs/packages-check.log`), last line: "RESULT: PASS: present packages
  match the manifest; absent: «doc-gen4», UnicodeBasic, BibtexQuery, MD4Lean".
  - Zero-size oleans: 0.
  - The root probe elaborated (`evidence/logs/cache-probe.log`).
- **Bootstrap**: the whole `order.txt` (31 modules), in order, with 0 errors, before any check
  (`evidence/logs/bootstrap.log`, `evidence/logs/bootstrap/`).
  - `/usr/bin/time` is absent on this host, so peak RSS comes from `getrusage` in `runlean.py`.
  - The highest recorded was 3,141,504 KiB (about 3.0 GiB, the lead's Mathlib name probe); the
    library modules stayed at or below about 2.6 GiB. No shortage and no OOM occurred.
- **Base runs**: a detached worktree `/home/user/gsw-base` (own TCSlib olean tree, with Eval and
  the facades re-checked at the base) ran the base seals and the base lint.

## Final checks (`evidence/`)

| Check | Result | Evidence |
|---|---|---|
| Owned modules | 5/5 exit 0, 0 errors (both forms), 0 sorry warnings | `logs/final/modules/`, `logs/final/modules.txt` |
| Sweep of `order.txt` | 31/31 exit 0, 0 errors | `logs/final/sweep/`, `logs/final/sweep.txt` |
| Admissions | 35 → 6; removed exactly the 29 targets; added 0 | `sorries/final.txt` |
| Axioms + dependency trace | 114 stored constants of the five modules (targets, helpers, readers, definitions, auxiliary); every one uses only `propext`, `Classical.choice`, `Quot.sound`; **0 reach `sorryAx`**; the trace lists no sorried constant | `axioms/final/` |
| Frozen statements | 0 unexpected differences; controls PASS in all 5 files (one-character header change → exactly 1 difference; deleted reader → exactly 1 removal) | `headers/final/` |
| Width / size | max width ≤ 100 (Python `len`), all files ≤ 364 lines, no `µ` | `width/final.txt` |
| Name clash | 0 clashes (3 new private names) | `clash/final.txt` |
| Explicit-unfold scan | Every `simp`/`rw`/`dsimp`/`unfold` selector token resolved by Lean. 0 foreign TCSlib definitions, **and 0 core/Mathlib definitions** | `unfold/final/` |
| Seals at base | 5 files × A/B × strict/coe, `-DmaxErrors=0`: 20/20 exit 0, 0 errors, harness valid | `seals/base/` |
| Seals at final | the same 20: 20/20 exit 0, 0 errors, harness valid. **Canonical coe-A: 0 failing declarations.** Strict differs from coe only by one extra sealed instance (FinDist's projection coercion), with no error difference; B = A | `seals/final/` |
| Paired controls | unsealed 0 errors; 6 POS pass in all four seals; 8 NEG (`gadget`, `mul`, `Encrypts`, `Regev.augmented`, `LWE.sample`, `Lossy.gadget`, `Randomized.blocksEquiv`, `BitEncoding.codepoint`) fail **exactly once** in each variant; COE passes coe, fails once strict. **ALL_OK** | `seals/controls-final/` |
| Lint `--check8b` | base 92 FAIL / 101 WARN / 364 files; final identical line sets (0 new, 0 removed) | `lint/lint-base.log`, `lint/lint-final.log`, `lint/diff-final.txt` |

**Seal notes.**
- Seals A and B install the same set: `Complexity.PolyExpr` is outside the import closure of every
  owned file and of the control probe, so there is no `PolyExpr.eval` control.
- Errors are counted with `^\S+\.lean:\d+:\d+: error[:(]` (both forms) in every seal, control,
  sweep and probe log.
- The harness (`evidence/tools/seal.py`, `seal_install.lean.txt`) copies verbatim the install block
  of the derand fill's harness (exchange `inbox/fills/derand/evidence/verification/tools/
  make_seals.py`, after Gate 10's), changing only its log prefix.
- The type-level Rule 10 seal covers `Regev.augmented`, `LWE.sample`, `Lossy.gadget`,
  `Randomized.blocksEquiv` and `BitEncoding.codepoint`; each is sealed and has a NEG control.

**Rule 10 reading.**
- Each file reads its own definitions directly and other files' definitions only through their
  readers.
- Mathlib definitions (`vecMul`, `mulVec`, `dotProduct`, `submatrix`, `Fin.init`, `Bool.toNat`)
  are reached only by `change` or `cases … <;> rfl`, or through their lemmas. They are never named
  in a selector.

**Tool corrections at checkpoint 1** (disclosed then, kept here). The first `ctlcheck.py` keyed
controls by name only, and the first `axioms_report.py` missed the summary line. Both were fixed and
re-run on the same raw logs; the first outputs are in `logs/cp1/evidence-run.out`. The final run
used the fixed tools throughout (`logs/final/evidence-run.out`).

## Evidence manifest

- `evidence/SHA256SUMS` lists every file under `evidence/` except itself.
- The top-level `SHA256SUMS` lists every delivered file under `inbox/fills/gsw-core/` except itself.
- The delivered paths equal the manifest's exactly: nothing missing, nothing extra, no leading `./`.
- The lead's development logs are in `evidence/lead/`, the checkpoint-1 checks in `*/cp1/`, the
  sub-agents' material in `evidence/subagents/`, and every tool used in `evidence/tools/`.
