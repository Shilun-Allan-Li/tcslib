# S1, the shared-lemma PR, with the S2 host contract: implementation report

- **Branch:** `wip/shared-s1` (local, not pushed), worktree `$SP/wt-shared-s1`.
- **Base:** `8dcdc8a56382289b5739e13fd18c4d5bd9b67c47`, the last base commit touching `TCSlib/`.
- **Head:** `c6affb3a92535d3f1de2e0a52c205a84c0cff551` (tree `80f4e6fc09e2746958f05cf3130036c28aa87284`), 14 commits. Patch series in `patches/`.
- **Design followed:** `fills/shared-lemmas/design.md`, with rulings Q1–Q8 (A, A, A, B, A, A, A, A).
- `$SP` = `/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`.

## 1. Results in short

| Check | Result | Evidence |
|---|---|---|
| Replay: the 97 modules downstream of the 15 changed files, then `audits/pass-shelat/Checks` | 98/98 rc=0, **0 errors** | `replay.log`, `tools/order.txt` |
| `sorry` census (corrected lexical code tokens at the original pinned base/head) | 506 → 507, **exactly +1**: the host in `Candidates/Concrete.lean`; the old 507 → 508 included one diagnostic string | `../evidence-r2/sorry-census-{base,head}.txt`; G08-04 |
| Statement diff (`decls2.py` against the base) | 25 ADDED (18 tier 1, 4 tier 2, 1 host, 2 visibility changes), 2 REMOVED, **0 CHANGED** | `statement-diff.txt` |
| Axioms | All 146 touched declarations and all 25 new or visibility-changed ones use the standard axioms or fewer; only the host has `sorryAx`. `Checks` has the same 4 `sorryAx` records as the post-landing base (`decides_of_decidesWithAdviceInTime`, `lemma_64_3`, `theorem_63_1`, `exists_canonizerExp`) | `axioms-touched.tsv`, `axioms-new.log`, `checks-axioms-head.log` |
| Rule 10 seal | 15 whole-file seals, collected from the elaborated terms. No touched declaration fails. The 6 failures are in untouched base declarations and fail the same way in the base control. Controls pass 13/13 | `seal/` |
| Explicit-unfold scan | 0 `unfold`, `delta` or `.eq_N` added; no foreign definition used as a rewrite or simp rule | `seal/unfold-scan.txt` |
| `style_lint.py` | Only the 6 size lines of the fill-owned files, as at the base; all 6 files shrink | `style-lint-{base,head}.log` |
| `campaign_style_lint.py --check8b` | No FAIL/WARN category change on `TCSlib/Cryptography` or `TCSlib/Complexity/Randomized` after normalizing changing line/size counts; INFO declaration counts also move | `campaign-lint-*.log` |
| Lines | +572 / −906 over 15 files (net −334, host contract included) | `line-counts.tsv` |

## 2. Per design group

| Group | Done | Deviations |
|---|---|---|
| **G1** trial loop (S2) | The **host contract** `polyTimeComputable_rejectBlocksL` (Q3 (A), Q4 (B)) is in `Concrete.lean` after `rejectBlocksL_spec`. The statement is design §4.1 verbatim; the proof is `sorry`. The docstring has the formula, the tag `[PS10, Theorems 52.3, 53.2, 61.7 and 63.10]` and a deviation note (truncation to `T` trials, register #15). Its **Proof sketch.** has three parts (the loop, polynomial time, correctness), harvested from rabin's `rabin_rb*`/`rabin_rbFind_eq` and dl-a's `split` step. It names the published lemmas a fill worker needs: `IterateFind.find?_range_and_lt`, `rejectBlocksL_eq_find?`, `StateLoop.length_pairFstD_add_pairSndD_le` and `polyTimeComputable_iterateFind`. The four loops are **not** retired; that is S2's landing. The module docstring gets a main-results entry, and its References get the four theorem numbers | none |
| **G2** search | `IterateFind.find?_range_and_lt`, proved through `find?_congr_of_mem`. `rejectBlocksL_eq_find?`, proved from core `List.findSome?_guard`, `List.map_findSome?` and `Option.guard_apply` (the design's proof correction; no `simp [Option.guard]`). Re-pointed: the four `*_find?_range_lt` copies (dla, dlc, rsa via E4, rabin) and the three `*_findSome?_ite` copies (dla, dlc, rsa via E4). The `ColZK` searches are left | `rabin_rbFind_eq` now reads `rejectBlocksL` through `rejectBlocksL_eq_find?`, as E4 does for rsa. That also removes its `simp only [Function.comp_apply, Option.guard]`, which passed a core definition to `simp` |
| **G3** `listToNat` equations | `listToNat_nil`, `_cons` (in the `(if b then 1 else 0)` form), `_append` and `_singleton_true` in `Primality.lean` (922 → 944 lines); `foldl_bits_eq` made public. All copies re-pointed: the four `*_listToNat_append`, the `_nil` and `_one`/`_true` copies, `dlb_foldl_bits` with `dlb_listToNat_cons`, and fac's inline `hone` | none |
| **G4** widths | The 7 lemmas in `Arithmetic.lean` (385 → 482 lines). Re-pointed: `dlc_natToList_mod`; `fac_natToList_mod` (reversed, `← natToList_mod_two_pow`); the zeros-append, drop-zeros, `subStr_self` and `mulStr` copies, including the inline one in `dlc_numPoly_mul`; `rsa_listToNat_ones` (E4); `fac_foldl_replicate_false`, whose 3 uses now go through `listToNat_append`/`listToNat_replicate_false` | `fac_natToList_lead` is kept (a different statement); only its proof is re-pointed |
| **G5** constants | Left (Q8) | — |
| **G6** `comp'`/`congr` | `PolyTimeComputable.comp'` and `.congr` in `Closure.lean`. Re-pointed: `rsa_comp` and `rsa_ptc_congr` (E4), `rabin_comp` (64 occurrences), `dlb_ptc` (56), and ElGamal's `polyTimeComputable_of_forall_eq`. `Closure`'s own `ptc_comp` and the base copies are deferred to clean-up part 2 | The inline `(congrArg PolyTimeComputable …).mp` uses are left; they are not in the design's re-point list |
| **G7** `2^{size}` | `two_pow_size_le_two_mul` in `Sampling.lean`; `dlb_two_pow_size_le` and dl-a's `hk2` re-pointed | `Sampling.lean` needed `import Mathlib.Data.Nat.Size`, which it could not reach before |
| **G8** `statClose_one` | In `Sampling.lean`; `dla_statClose_one` and `rabin_statClose_one` re-pointed | — |
| **G9** `abs_uexp_sub_le` | `Sampling`'s copy made public, with `rw [uexp_def]` in place of `unfold uexp`. The `PublicKeyLemmas` copy is deleted; its user `PublicKey.lean` resolves unchanged, and docstring lines 41 and 67 are updated. `dlc_abs_uexp_sub_le` re-pointed as `abs_uexp_sub_le (by positivity)` | none |
| **G10** restrictions | `HardcoreBit.pushesUniform_restrict` in `HardcoreBit/Basic.lean`; no new import was needed. `dla_pushesUniform_restrict` deleted. Q6 (A): `ColZK.pushesUniform_restrict` deleted, its 2 uses re-pointed, and the module docstring and the two sketches that named it updated | — |
| **G11** casts | Mathlib's `Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)` and `List.ofFn_congr` replace `dlc_castEquiv`/`_ofFn` and `fac_arrowCongr`/`_ofFn` | Factoring needs a 2-line local `hofn` to rewrite with |
| **G12–G14, G18–G26** | As ruled: left or deferred | — |
| **G15** (tier 2) | `sampleUnitL_getD_spec` made public in `RSA.lean`. `rsa_getD_spec` and `rabin_getD_spec` re-pointed; `rabin_one_mod_spec` deleted | **`rsa_one_mod_spec` stays private**, because `statClose_sampleUnitL` also uses it directly. The design counted it as deleted (−19), so the actual saving is smaller |
| **G16** (tier 2) | `ArithmeticFP.le_poly` and `ArithmeticFP.prime_poly`. `rsa_`/`rabin_le_poly` and `rsa_`/`rabin_prime_poly` re-pointed | `rabin_prime_poly` (the case `a = id`) becomes `H.prime_poly polyTimeComputable_id` |
| **G17** (tier 2) | `val_inv_natCast_zmod_zero_le` beside `xgcdStr_pairEncode`; both copies re-pointed | — |
| **E4** | rsa's `conditional-harvest-edits.diff` (SHA-256 `445928bd6fa469e1db486ab12dff17f831d2101eac73589292ce03d974f3976e`) applied **unchanged** (`git apply --check` clean), in its own commit. The tier-2 commit after it changes what E4 left (`rsa_le_poly`, `rsa_prime_poly` → the bundle lemmas). Under rsa's 50-name review seal, RSA has 0 errors (`seal/SealedRSA-review50.out`) | none |

**Q7.** The six S2 sketch refreshes were not done. Docstrings changed only where a re-point made a name false:
- `rsaSampler_spec` (public): `rsa_getD_spec` → `sampleUnitL_getD_spec`.
- `polyTimeComputable_egDecStr` (public): `polyTimeComputable_of_forall_eq` → `PolyTimeComputable.congr`.
- `ColZK.pushesUniform_offsetTable` and `_blockFields`: the restriction lemma's new name.
- Private sketches: `dla_ssFind_eq`, `dlc_ssLoop_eq`, `rabin_rbFind_eq`, `dlc_hyb3`, and E4's own.

No statement changed.

## 3. Statement surface (`statement-diff.txt`)

- **ADDED, tier 1 (18):**
  - `Complexity.PolyTimeComputable.comp'`, `.congr`;
  - `Complexity.IterateFind.find?_range_and_lt`;
  - `NumberTheory.listToNat_nil`, `_cons`, `_append`, `_singleton_true`;
  - `Candidates.natToList_mod_two_pow`, `listToNat_natToList_zero_append`, `natToList_zero_append_drop`, `subStr_self`, `listToNat_mulStr`, `listToNat_replicate_true`, `listToNat_replicate_false`;
  - `Candidates.rejectBlocksL_eq_find?`;
  - `statClose_one`, `two_pow_size_le_two_mul`;
  - `HardcoreBit.pushesUniform_restrict`.
- **ADDED, tier 2 (4):** `Candidates.sampleUnitL_getD_spec`, `ArithmeticFP.le_poly`, `ArithmeticFP.prime_poly`, `val_inv_natCast_zmod_zero_le`.
- **ADDED, host (1, sorried):** `Candidates.polyTimeComputable_rejectBlocksL`.
- **Visibility changes (2):** `foldl_bits_eq` and `abs_uexp_sub_le`, shown as ADDED in `Sampling.lean`; their statements are unchanged.
- **REMOVED (2):**
  - `ColZK.pushesUniform_restrict` (Q6);
  - the `PublicKeyLemmas` copy of `TCSlib.Cryptography.abs_uexp_sub_le`, whose full name survives in `Sampling.lean` (G9).
- **CHANGED:** none.
- No new definition and no `@[simp]`. Every new lemma has a docstring with its formula. `natToList_zero_append_drop`, `find?_range_and_lt`, `pushesUniform_restrict` and the host also carry a **Proof sketch.**

## 4. Rule 10 (`seal/`)

- **Touched declarations** (`touched-*.txt`, `tools/touched.py`): every head declaration whose text contains an added line or a deletion point of `git diff -U0` against the base, over all 15 files. That is 146 declarations. It over-includes neighbours of deleted blocks, which only makes the seal stricter.
- **Collection** (`Collect.lean`, `collect.log`, `tools/collect_body.lean`):
  - **G08-N2 correction:** the original collector starts from elaborated types/values of the touched constants and auxiliaries, but traverses the types and definition bodies of subsequently reached constants only when they belong to the audited module. It did not traverse every referenced constant's type. The auditor's expanded traversal adds `(DiscreteLog, bitsToNat)` and `(RSA, primeStr)`, giving a 90-name union, without a new touched failure. The repair in #227 moves type traversal outside that own-module condition; fresh round-2 evidence records its actual output.
  - Kept: TCSlib definitions from other modules that are not instances; non-reducible ones, plus matchers whatever their status.
  - `PolyExpr.eval` and `glNeed` are left unsealed.
  - Result: 89 names in all (`names-*.txt`). The only foreign matcher reached is `polyTimeComputable_iterateFind.match_1` (DiscreteLog, ElGamal). IterateFind and Primality reach no foreign definition.
- **Whole-file seals** (`Sealed*.lean/.out`, `seal-summary.tsv`): 9 files are clean. There are 6 failures, all in **untouched** declarations. Each fails the same way when the **base** file gets the same seal (`base-control/`):
  - `primesPairEquiv_apply_val` (Concrete), `ExpGroupGen.FullLength.exists_fullLengthExcept` (DiscreteLog), `rabinCollection_index` and `rabinBlumTrapdoor_index` (Rabin), and `uexp_mono` (HardcoreBit/Basic). All five are rows of `gates/07-eqlemmas/evidence-r2/r6c/cleanup-b.tsv` (clean-up part 2).
  - `exists_plantFactorer` (Factoring): the `NUPPT.coinLen` defeq reading recorded in the fac delivery review, finding 1 (forced by `ans_layout`'s published coin type). It is not in the `cleanup-b` rows, which predate the fac landing.
- **Controls** (`Controls.lean/.out`): C1–C13 read each of these by its body:
  - `natToList`, `listToNat`, `rejectBlocksL`, `StatClose`, `uexp`, `PushesUniform`, `PolyTimeComputable`;
  - `sampleUnitL`, `subStr`, the matcher `polyTimeComputable_iterateFind.match_1`, `sampleBelowL`, `bitsToNat`, `mulStr`.

  All 13 close unsealed and fail sealed (13 errors, all "Type mismatch").
- **Explicit-unfold scan** (`unfold-scan.txt`):
  - 70 rewrite and simp lists in the added code, and no `unfold`, `delta` or `.eq_N`.
  - The one lexical hit is `show listToNat [false] = 0 by rw [listToNat_eq]`, a G5 constant whose rule is the published `listToNat_eq`.
  - Core and Mathlib definitions reduce only in `rfl`, `show` or `exact` steps: `Option.guard_apply`, the `show` through `ZMod 0 = ℤ` in `val_inv_natCast_zmod_zero_le`, and the `arrowCongr`/`finCongr` casts.

## 5. Lines per file (`line-counts.tsv`)

| File | + | − | base → head |
|---|---|---|---|
| `Complexity/Randomized/Build/IterateFind.lean` | 23 | 0 | 531 → 554 |
| `Complexity/Randomized/Closure.lean` | 18 | 0 | 456 → 474 |
| `Asymptotic/PublicKeyLemmas.lean` | 5 | 20 | 856 → 841 |
| `Asymptotic/Sampling.lean` | 30 | 6 | 856 → 880 |
| `Candidates/Arithmetic.lean` | 97 | 0 | 385 → 482 |
| `Candidates/Concrete.lean` | 81 | 21 | 691 → 751 (the host contract is about 57 of the +81) |
| `Candidates/DiscreteLog.lean` | 11 | 109 | 1446 → 1348 |
| `Candidates/DiscreteLogHardcore.lean` | 50 | 83 | 3091 → 3058 |
| `Candidates/ElGamal.lean` | 21 | 143 | 2391 → 2269 |
| `Candidates/Factoring.lean` | 12 | 35 | 1851 → 1828 |
| `Candidates/RSA.lean` | 88 | 240 | 2762 → 2610 |
| `Candidates/Rabin.lean` | 80 | 215 | 3813 → 3678 |
| `HardcoreBit/Basic.lean` | 26 | 0 | 266 → 292 |
| `NumberTheory/Primality.lean` | 22 | 0 | 922 → 944 |
| `ZeroKnowledge/ThreeColoring/ColZKLemmas.lean` | 8 | 34 | 328 → 302 |
| **Total** | **572** | **906** | net −334 |

The homes stay under 1000 lines (`Primality` 944, `Concrete` 751). The six files over 1000 lines are fill-owned under the standing size rule, and each one shrinks.

## 6. Deviations and notes (no ruling needed)

1. `Sampling.lean` gains `import Mathlib.Data.Nat.Size`, for `two_pow_size_le_two_mul`.
2. `rsa_one_mod_spec` stays private in `RSA.lean`, because it has a second direct user.
3. `rabin_rbFind_eq` was re-pointed to `rejectBlocksL_eq_find?` rather than only swapping `rabin_find?_range_lt`. It loses a `simp only [Option.guard]`; S2 deletes the lemma anyway.
4. Two candidates for clean-up part 2 were kept out of S1, as they are outside the design's lists:
   - the inline `StatClose … 1` proof in `factoringCollection_sampleClose` (the `n < 2` branch);
   - the inline `congrArg PolyTimeComputable` transports.
5. `audits/pass-shelat/run2-census.md` (records) still names the deleted `polyTimeComputable_of_forall_eq`. It is a historical census and was not edited.
6. Every check ran directly on `$SP/postland-oleans`, one Lean process at a time. That tree now holds the head's oleans for the 97 replayed modules plus `Checks`. No `lake build`, no cache fetch.

## 7. Evidence index

- `replay.log`; `sorry-census-{base,head}.txt`; `statement-diff.txt`.
- Axioms: `axioms-touched.tsv`, `Axioms.lean`/`axioms-new.log`, `checks-axioms-head.log`.
- `seal/`: touched lists, `Collect.lean`, `collect.log`, `names-*.txt`, `Sealed*.lean/.out`, `base-control/`, `Controls.lean/.out`, `seal-summary.tsv`, `unfold-scan.txt`, `SealedRSA-review50.*`.
- Lints: `style-lint-{base,head}.log`, `campaign-lint-{base,head}-*.log`.
- `line-counts.tsv`; `logs/` (the per-module checks run during the work); `tools/`; `patches/`; `BASE.txt`, `HEAD.txt`.

**Not yet clear to merge — S1 is not yet a PR, and gate 08 (Q1 (A)) must audit the 22 new statements, the 2 visibility changes and the host contract first.**
