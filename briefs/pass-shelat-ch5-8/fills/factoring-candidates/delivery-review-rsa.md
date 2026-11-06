# Delivery review: fill unit rsa (the RSA candidate)

- **Delivery:** `inbox/fills/rsa/` on `exchange/pass-shelat-ch5-8` at
  `165dcc7d89fba0d5c8b4fe8e4e9c660a23f3d2d7` (REPORT.md, 10 patches, `src/`, `evidence/`).
- **Worker branch:** `fill/rsa`, head `35c1abee23ef6a677af2e55313f7477594589587`, base
  `16a7d02d69cae1a700c131e3cc3dd918a7b3d6e1` (the issue commit and the merge base), 10 commits.
- **Brief:** `brief-issued.md`, unit rsa (D3 for the permitted `sorryAx` sources), with `review.md`.
  **Policy:** `policy.md`.
- **Integration partners:** fac's `fill/fac` head `e932cd15eb564917ca7bc091df0c17d41cc6c046`;
  dl-a's reviewed head `b62c34ee813eeccbaa8a7cbf9964d2356fedbf14`.
- **Reviewed:** 2026-11-06. This was an independent run:
  - the patches were replayed in a fresh scratch worktree;
  - Lean was re-run one file at a time against a copy of the worker's olean tree, never with
    `lake build`;
  - the seal names were collected from the elaborated terms, not taken from the worker's list;
  - the integration replay was rebuilt in a second scratch worktree with a second olean copy.

## Verdict: **land after edits**

All ten targets are filled with no `sorry`, including S3 `statClose_sampleUnitL`. Four targets
print the standard triple at the base. The other six reach `sorryAx` only through S1, S2 and
`statClose_rejectBlocksL`, all permitted by D3. With fac's head integrated, six targets are
standard; the four that remain reach only dl-a's `statClose_rejectBlocksL`. With dl-a's
`Concrete.lean` added as well, **all ten targets and all 158 public constants of `RSA.lean` print
the standard triple**.

The other checks pass:
- every base statement is byte-identical;
- the three docstring changes are authorized and accurate;
- the 101 new declarations are all `private` `rsa_`;
- the owned file, `Rabin`, the facade and `audits/pass-shelat/Checks` elaborate;
- the rule-10 seal holds under this review's 50-name list (with `PolyExpr.eval` unsealed under
  ruling Q1). The only sealed failure is the base proof `rsaCollection_index`, and its re-point
  is checked below;
- the four route departures are sound.

There are **no blockers and no majors**. The edits are minor:
- **E1** replaces `rsa_appendEquiv`, an undisclosed copy of Mathlib's `Fin.appendEquiv`, by a
  citation;
- **E2** makes `rsa_neZero_N` a local instance. A `private instance` is still exported to every
  importer;
- **E3** refreshes five proof sketches that no longer describe their proofs. These are docstring
  changes only, under the user's standing ruling.

**E4** is conditional on the harvest PR. It deletes the 12 copied numeral, list and
applied-form helpers and cites the proposed public lemmas. It was checked against stubs
(finding 5). The dl-a loop family stays until the block-loop host is gated. The disclosure
ledger is amended (**D1**).

## Checks

| # | Check | Result |
|---|---|---|
| 1 | Integrity | Worktree `$SP/wt-rev-rsa` (detached at `16a7d02d`, `.lake/packages` linked); `git am` of the 10 patches is clean (`am.log` empty). The result's tree `40ccc72c752cf7ca182df6d21e83fa9fe84afdcf` is the tree of `35c1abee`. The owned file matches `src/` and the branch head byte for byte (`cmp`), and `src/` holds only that file. `git diff --stat`: 1 file, 1672 insertions, 37 deletions. The 37 removed lines are the ten `  sorry` and 27 lines of the three rewritten **Proof sketch** paragraphs: `polyTimeComputable_rsaGenRaw` 13, `polyTimeComputable_unitSampleStr` 6, `rsaCollection_invProbAt_le` 8. |
| 2 | Statement freeze | Own declaration-level comparison (`tools/declfreeze_rev.py`, `declfreeze-rev.log`). All 117 base declarations are present, in base order, with byte-identical headers. Docstrings changed only for `polyTimeComputable_unitSampleStr` (brief step 4, **Correction**), `polyTimeComputable_rsaGenRaw` (step 5, "from S1") and `rsaCollection_invProbAt_le` (step 7, **Correction**), each inside its **Proof sketch** paragraph. No non-target body changed. The tool flags `rsaGenRaw`, `rsaBreaker_runAt` and `rsaFromFactorRaw` only because a new `/-! … -/` section header follows each one; the chunk diffs confirm this. All 101 new declarations are `private` with the prefix `rsa_`. The diff adds no `set_option`, `attribute`, `open`, `section`, `@[simp]`, `sorry` or `native_decide`. Base sorries: 10; at the head: 0. |
| 2 | `polyTimeComputable_unitSampleStr` | Header byte-identical. Its position is unchanged: after `polyTimeComputable_rsaGenRaw` and before `polyTimeComputable_rsaSampleRaw`, as at the base (base line 594, head 1443). Its body is `by exact rsa_ptc_unitSampleStr H hf`. The private proof sits at line 998, before the generator helpers, because the base order puts the generator (which needs it) first. Rabin cites the public name, and it prints the standard triple. |
| 3 | Elaboration | `scripts/lean_check_tree.sh` with `TCSLIB_OLEANS` set to a copy (`$SP/rev-rsa-oleans`), one process at a time (`module-checks.log`): `RSA` 25 s, 0 errors, 0 warnings; `Rabin` 7 s, 19 sorry warnings (exactly its own targets); the facade `Candidates` 2 s. `audits/pass-shelat/Checks` needed 33 unchanged base modules that the provided tree lacks: the `NumberTheory` facade and 32 `ZeroKnowledge` modules (`checks-missing.txt`). They were built into the copy first, all rc 0 (`zk-build.log`). Then `Checks` ran in 132 s with 0 errors. |
| 3 | The three worker-built modules | `DiscreteLog`, `DiscreteLogHardcore` and `ElGamal` have sources equal to the base. Rebuilt here from the base sources into a side directory, each `.olean` is **byte-identical** to the worker's (sha256 `ebd16ec3…`, `678a7c21…`, `134fd800…`; `olean-cmp.log`). Their sorry warnings (6, 7, 7) are the dl-a, dl-b and ElGamal base targets. |
| 3 | Axioms (base tree) | `probe/Axioms.lean`, `axioms.log`. Standard triple: `polyTimeComputable_unitSampleStr`, `polyTimeComputable_rsaFromFactorRaw`, `factorProb_le_rsaProb`, `rsa_imp_factoring`. Plus `sorryAx`, with the reached sorried declarations listed by this review's sorry-source probe: S3 → `statClose_rejectBlocksL` (Concrete); `polyTimeComputable_rsaGenRaw`, `rsaSampler_spec` → S1 (Factoring); `rsaCollection_sampleClose` → S1, `statClose_rejectBlocksL`; `rsaCollection_invProbAt_le`, `rsaCollection_oneWay` → S1, `statClose_rejectBlocksL`, S2. **D3: pass.** All three sources are on rsa's list, and `statClose_rejectBlocksL` is the entry "(dl-a, `Candidates/Concrete.lean`)", the module the probe reports. No machine-layer declaration is reached. A sweep of the 158 public constants finds 32 with `sorryAx`, all through these three (S1 enters through `rsaGen`, which carries `polyTimeComputable_rsaGenRaw`). This reproduces the REPORT's table. |
| 3 | Integration A (fac) | Second worktree `$SP/wt-rev-rsa-int` at `35c1abee` with `Factoring.lean` from `e932cd15`, against a second olean copy. `Factoring`, `RSA` and `Rabin` were recompiled, all rc 0 (`integration-A.log`). Standard triple: `polyTimeComputable_rsaGenRaw`, `polyTimeComputable_unitSampleStr`, `rsaSampler_spec`, `polyTimeComputable_rsaFromFactorRaw`, `factorProb_le_rsaProb`, `rsa_imp_factoring`. **Still `sorryAx`:** `statClose_sampleUnitL`, `rsaCollection_sampleClose`, `rsaCollection_invProbAt_le`, `rsaCollection_oneWay` (and `rsaTrapdoor_oneWay`), each inheriting it **only** from dl-a's `statClose_rejectBlocksL` (`Concrete.lean`). Sweep: 5 of 158 (`integration-A-axioms.log`). |
| 3 | Integration B (fac + dl-a) | Additionally `Concrete.lean` from `b62c34ee`. The 11 modules of `order.txt` lines 62–72 (`Concrete` to `Rabin`) were recompiled, all rc 0 (`integration-B.log`). **All ten targets print `[propext, Classical.choice, Quot.sound]`, and the sweep finds 0 of 158 constants with `sorryAx`** (`integration-B-axioms.log`). |
| 4 | Rule 10, own seal | See finding 7. Collector `probe/Collect.lean` (`collect.log`): 187 own constants; 48 names in the narrow pass and 51 in the wide pass. Seal: the 51 minus `PolyExpr.eval` (Q1), so 50 names, including the matcher `polyTimeComputable_iterateFind.match_1` (`seal/rev-sealed-names.txt`). The whole-file sealed copy has exactly 1 error, the base `rsaCollection_index` (`seal/RevSealedRSA.out`). Controls C1–C8 close unsealed and fail sealed; C9 shows the need for Q1 (`seal/RevControl.out`). Grep (`tools/grepforeign.py`, `grep-foreign.txt`): 215 rewrite/simp lists and 24 `unfold`s in the added code. No foreign definition is used as a rule, and every `unfold` names an own-file definition. |
| 5 | Duplication | See findings 1, 4 and 5. |
| 6 | Routes and sketches | See findings 3 and 6. |
| 7 | Lint | `scripts/style_lint.py`: exactly 1 finding at the head, the size line (2758 > 1000), the approved exception (`style-lint-head.log`). Every private proof over the lint's threshold has a **Proof sketch.**, and all 101 new declarations have docstrings. `campaign_style_lint.py --check8b`: no FAIL row for RSA; the size WARN; the check-8 WARN lists the same 18 base names, so no new public `def` (`campaign-lint-head.log`). Size: 2757 lines (1122 at the base); approved, noted only. |

## Findings

1. **minor: `rsa_appendEquiv` is an undisclosed copy of Mathlib's `Fin.appendEquiv`.**
   - The private definition (10 lines with its docstring) is field for field Mathlib's
     `Fin.appendEquiv` (`Mathlib/Logic/Equiv/Fin/Basic.lean:406`) at `α = Bool`:
     `toFun := Fin.append s.1 s.2`, and the inverse by `castAdd`/`natAdd`.
   - It is in the closure: `#check @Fin.appendEquiv` resolves in a file importing only `RSA`
     (`probe/InstProbe.out`), and `Asymptotic/HardCore.lean` already uses it.
   - The brief's "Mathlib first" makes this a reuse finding. The REPORT's "Mathlib first" list
     does not mention it.
   - **E1** deletes the copy and cites `Fin.appendEquiv` in `rsa_genCoinsEquiv` and
     `rsa_genCoinsEquiv_ofFn`. The `show … from rfl` step still holds, since a Mathlib definition
     may reduce in `rfl`.

2. **minor: the `private instance rsa_neZero_N` is exported.**
   - A `private` modifier mangles the name but does not scope the instance. Every module that
     imports `RSA` (`Rabin`, the facade, `Checks`) resolves `NeZero P.N` for any
     `P : RSAParams m` through it. This was checked by a probe outside the file, where
     `inferInstance` succeeds with trace `apply @…rsa_neZero_N✝` (`probe/InstProbe.out`).
   - This is a hidden addition to the file's public surface that the freeze comparison does not
     see. It is harmless today, because Rabin compiled without it at the base.
   - **E2** makes it `private local instance`. After E2 the same probe fails to synthesize
     (`edits/InstProbe2.out`), and `RSA`, `Rabin` and the facade recompile with 0 errors.

3. **minor: five frozen sketches no longer describe their proofs** (policy §3,
   "Synchronization"). **E3** refreshes each **Proof sketch** paragraph. This is docstring only,
   under the user's standing ruling; no statement changes.
   - **`polyTimeComputable_rsaFromFactorRaw`** (not a marked target, so the worker left it; the
     REPORT asks for the refresh). The frozen text tests `p'q' = N` with
     `polyTimeComputable_pairEq` and pads with `unaryPoly`/`blockMap`. The proof instead:
     - tests with two `H.le` comparisons;
     - puts one leading zero before `Φ` and `|y| + 1` leading zeros before `N`;
     - truncates with `(⟦0⟧_{2n} ++ v).drop |v|`;
     - and proves the word computation equal to `rsaFromFactorRaw A` (`rsa_fOut_eq`).
   - **`rsaCollection_sampleClose`.** The frozen text re-derives S3 inline (acceptance rate,
     `statClose_rejectBlocksL` with "default `1`", "`decodeFin`-style injectivity"). The proof
     instead:
     - cites S3 at every `n` (`Nat.size N ≤ 2·max(n, 2) ≤ B(n)`);
     - maps it through `v ↦ rsaDec i ⟦v⟧_{2m}` (`rsa_statClose_dec`);
     - transports it along the coin and domain equivalences;
     - and weakens it by `StatClose.mono`.
   - **`rsaSampler_spec`.** The frozen ending computes the decoded unit's value
     (`ZMod.coe_unitOfCoprime`, …). The proof uses `rsaEnc_of_rsaDec` instead.
   - **`statClose_sampleUnitL` (S3).** Step (3) cites `uprob_eq_card_filter`. The proof uses
     `uprob_def`, `Nat.card_congr` and `ZMod.card_units_eq_totient` (`rsa_uprob_units`). The rest
     of the sketch matches.
   - **`rsaCollection_invProbAt_le`.** The worker re-pointed clauses (i) and (ii) accurately, but
     the unrewritten first paragraph still cites `PermCollection.f_injective`, and
     `pushesUniform_rsaPerm`/`PushesUniform.uprob_eq` for an *equality*. The proof uses
     `rsa_rsaF_injective` and bounds the inner probability by the bijection
     `(x, ω) ↦ (x^e, φ⁻¹ ω)` (`uprob_comp_equiv`, `uprob_mono`; `rsa_inner_le`). E3 also reflows
     the two lines over 100 characters that the rewrite introduced.

   The other target sketches match their proofs, including the two worker rewrites
   (`polyTimeComputable_unitSampleStr`, `polyTimeComputable_rsaGenRaw`), which were checked line
   by line against `rsa_ptc_unitSampleStr`, `rsa_usFind_eq`, `rsa_genCore` and
   `rsa_genCore_spec`.

4. **minor: the duplication disclosure is incomplete.** The REPORT's rows are confirmed (finding 5
   for the dl-a copies). Not disclosed:
   - **`rsa_appendEquiv`**: Mathlib `Fin.appendEquiv` (finding 1).
   - **`rsa_ptc_congr` and `rsa_comp`.**
     - Besides the private `ptc_comp` copies the REPORT names, there are public copies:
       `ColMachines.ptc_comp`/`ptc_congr` (`ZeroKnowledge/ThreeColoring/Machines.lean:84,93`),
       `GI.ptc_congr` (`GraphIsomorphism/Efficiency.lean:71`) and the public `ptc_congr` of
       `ThreeColoring/SimulatorMachine.lean:58`.
     - There is also a private `ptc_congr` in `GraphIsomorphismZK/Simulator.lean:121`.
     - All of these are outside the closure, so the copy is forced.
     - The private `ptc_comp` copies are five, not four: `Randomized/Closure.lean`,
       `Asymptotic/Collections.lean`, `UniversalLemmas.lean`, `Universal.lean` and
       `EnsemblesLemmas.lean`.
   - **`rsa_length_usStep_*`.** These are third-generation copies: dl-a's
     `dla_length_ssStep_*` are themselves near-verbatim copies of Primality's private
     `length_spStep_*` (dl-a review, finding 5). The source of record is `NumberTheory/Primality.lean`.
   - **`rsa_findSome?_ite` and `rsa_find?_range_lt`.** Both have near-duplicates in the
     closure. The first follows in four lines from core `List.findSome?_guard` and
     `List.map_findSome?`; `OneWay.findSome?_eq_bind_find?` is the general form. The second is
     close to `OneWay.find?_range_eq_map_find?_finRange` (`Asymptotic/OneWayLemmas.lean`). The
     dl-a review recorded both for the `dla_` originals, and the REPORT does not carry them over.
   - **The inner `hnum` of `rsa_drop_zeros_append`** (`natToList W N = natToList W (N % 2^W)`).
     It is fac's private `fac_natToList_mod`, with the same two-line proof (cross-unit, parallel
     fills).
   - **`rsa_zsel`, `rsa_zOf` and `rsa_zOf_self`** are parallel to fac's `fac_pairDec` and
     `fac_pairDec_pq`. Both select a `DistinctPrimes` from a value pair by the validity test of
     the base `rsaGenParams`/`samplePairOut`. A published selector beside `DistinctPrimes` in
     `Concrete.lean` would serve both.
   - **The bound `2^{size N − 1} ≤ N`** (`h1` of `rsa_two_pow_size_le`) belongs to the
     `2^{size m} ≤ 2m` family: dl-a's inline `hk2`, `dlb_two_pow_size_le` and three-colouring's
     `h2` (dl-b review, finding 7). A shared `Nat.two_pow_size_le_two_mul` would serve all of
     them.
   - **`rsa_listToNat_one`** is fac's `hone` (the fac review's cross-unit list). With
     `rsa_listToNat_ones`, `rsa_listToNat_mulStr` and `rsa_subStr_self`, it belongs to the shared
     numeral set of finding 5.

   Number theory is Mathlib's or TCSlib's throughout: `Nat.size_le`, `Nat.lt_size_self`,
   `Nat.pow_log_le_self`, `ZMod.unitOfCoprime`, `ZMod.card_units_eq_totient` and
   `le_totient_mul_log_succ`. `rsa_uprob_pi_eval` has no TCSlib or Mathlib form; the nearest is
   `uprob_pi_forall_dep` (`Asymptotic/Permutations.lean`, outside the closure, a different
   statement). **D1** lists all of these.

5. **minor (disclosed debt): the copies of dl-a's helpers, and the clean landing.**
   - **Confirmed** against `DiscreteLog.lean` at `b62c34ee`:
     - `rsa_findSome?_ite`, `rsa_find?_range_lt` and `rsa_listToNat_nil` are verbatim
       `dla_findSome?_ite`, `dla_find?_range_lt` and `dla_listToNat_nil`;
     - `rsa_listToNat_append` is verbatim `dla_listToNat_append`, which is the private
       `foldl_bits_eq` of `Asymptotic/Sampling.lean` plus a `rw`;
     - `rsa_drop_zeros_append` with `rsa_listToNat_zeros_append` is `dla_drop_natToList_zero_append`
       with one step factored out;
     - `rsa_usStep`, `_usBlock`, `_usOut`, `_usStep_poly`, `_usBlock_poly`, `_usOut_poly`,
       `_usStep_iterate` and the three `rsa_length_usStep_*` are verbatim the `dla_ss*` family,
       renamed.
   - **Size.** That is 80 + 71 = 151 lines (the REPORT says "about 140"). `rsa_comp` and
     `rsa_ptc_congr` add 10 more, and the other numeral helpers 22. New, as disclosed:
     `rsa_usStart` (stride `1^B` and counter `1^T` in the header), `rsa_usAcc`/`rsa_unitTest_eq`,
     `rsa_usLoop` (the matcher as `Option.elim`, read once by `split`, which passes sealed) and
     `rsa_usFind_eq`.
   - **The clean landing.** These are the proposed public homes and the order of the PRs.
     - **H1, the shared-lemma PR** (a shared-file window; proved lemmas only, no `sorry`; the new
       public names need a statement check). It publishes:
       - `Complexity/ClassNP/PolyTime.lean`, beside `PolyTimeComputable.comp`:
         - `PolyTimeComputable.comp'` (`x ↦ g (f x)`);
         - `PolyTimeComputable.congr (h : PolyTimeComputable f) (e : ∀ x, f x = g x)`, in
           Mathlib's `Continuous.congr` orientation.

         They retire `rsa_comp`, `rsa_ptc_congr`, the five private `ptc_comp`, dl-b's `dlb_ptc`
         and the ZK copies above.
       - `Randomized/Build/IterateFind.lean`, beside `find?_congr_of_mem`:
         `IterateFind.find?_range_and_lt`. It retires `rsa_`/`dla_find?_range_lt`.
       - `Candidates/Arithmetic.lean`, beside the `listToNat`/`natToList` family:
         - `listToNat_nil`;
         - `listToNat_singleton_true`;
         - `listToNat_append`;
         - `listToNat_replicate_true` (`= 2^k − 1`);
         - `listToNat_natToList_zero_append`;
         - `natToList_zero_append_drop` (the truncation lemma);
         - `subStr_self`;
         - `listToNat_mulStr`;
         - fac's `natToList_mod`.

         They retire the rsa, dl-a and fac numeral copies.
       - `Candidates/Concrete.lean`, beside `rejectBlocksL_eq`:
         `rejectBlocksL_eq_find? : rejectBlocksL E k B T r = ((range T).find? (E ∘ val)).map val`.
         It retires `rsa_`/`dla_findSome?_ite`. Its proof is the four core lines.
     - **Order:**
       1. dl-a lands as reviewed. It is the source of the copies; its D1 rows stand.
       2. H1 lands. It deletes the five `dla_` list and numeral helpers in `DiscreteLog.lean`
          and, optionally, fac's `fac_natToList_mod` and `hone`.
       3. rsa lands with **E1–E3 and E4**. E4 deletes the 12 copies and cites H1, so rsa copies
          nothing but the loop data.
       4. **H2, the host PR**, is statement-gated (policy §1, "Hosts come first"; registry
          row in `machine-library-design.md` §14). It adds a public
          `polyTimeComputable_rejectBlocksL` in `Concrete.lean`, beside `rejectBlocksL`:
          - for polynomial-time words `w`, `1^k`, `1^B`, `1^T`, the coins, and a
            polynomial-time test `t` with `t ⟨w, b⟩ = decide (E ⟦w⟧ ⟦b⟧)`, some
            polynomial-time `g` outputs `[]` iff `rejectBlocksL (E ⟦w⟧) k B T c = none`, and
            `true :: b` with `⟦b⟧ = v` when it is `some v`;
          - this is the REPORT's request 1 and the brief's rabin request.
       5. One re-point PR then retires `dla_ss*`, `rsa_us*` (keeping `rsa_usAcc` and
          `rsa_unitTest_eq`) and rabin's generic loop, and optionally Primality's private
          `spStep` family.
     - **If rsa must land before H1:** land E1–E3 only, and H1 applies E4 to `RSA.lean` as part
       of its re-point set. The diff is ready either way.
   - **E4** (`edits/conditional-harvest-edits.diff`, on top of E1–E3) was checked against stubs
     of exactly the H1 statements:
     - the stubs carry the proofs moved from the copies, inserted before the namespace in a test
       copy (`edits/harvest-stubs.lean`, `edits/RSAHarvestStub.lean`);
     - unsealed: 0 errors, 0 warnings (`RSAHarvestStub.out`);
     - sealed with the 50 names: only the base `rsaCollection_index` (`RSAHarvestStubSealed.out`);
     - `RSA.lean` goes from 2758 to 2633 lines, and `style_lint.py` still reports only the size
       line.
     - If H1 lands under other names, only the renaming table in `edits/mk_harvest.py` changes.

6. **note: the route departures are sound.**
   - **`rsaFromFactorRaw`: truncation and zero padding.**
     - `rsaFromFactorStep` outputs `⟦y^d mod N⟧_{2n}`, and `natToList` keeps the low `2n` bits.
       The word `v` from `H.modExp` has width `|y| + 1 + |N|`, which may be shorter or longer
       than `2n`. `(⟦0⟧_{2n} ++ v).drop |v| = ⟦⟦v⟧⟧_{2n}` (`rsa_drop_zeros_append`) covers both,
       so the output equals the definition exactly.
     - The prefixes are needed for exactness, not for typing. `xgcdStr`/`modExpStr` return
       numerals of the modulus width (`xgcdStr_pairEncode`, `modExpStr_pairEncode`). At `Φ = 0`
       the inverse in `ZMod 0 = ℤ` is a sign, so `d ≤ 1` (`rsa_val_inv_zero_le`), which needs
       width ≥ 1: the one zero before `Φ` gives it. At `N = 0`, `y^d mod 0 = y^d ≤ max(1, y)`,
       which needs `|y| + 1` bits.
     - The test `p'q' = N` by two `H.le` is exact across widths, and `q' = N / p'` uses Lean's
       `/` (with `x / 0 = 0`), as the definition does.
   - **`unitSampleStr`: the `divMod` width and the counter.**
     - The output is the remainder of `H.divMod ⟨b, w⟩`, which has the width `|w|`
       (`divModStr_pairEncode`), exactly `unitSampleStr`'s width.
     - An accepted `v < N` is its own remainder (`sampleUnitL_spec`). The fallback `b = [true]`
       gives `1 mod N`, also at `N = 0`. No padding is needed.
     - The host searches `|x| + 1` rounds, and `|x| ≥ T(n)` because the start state contains
       `1^{T(n)}` (`hrange`). The counter makes trial `i` accept only for `i < T(n)`
       (`rsa_usAcc`), so `find?_range_lt` cuts the search to exactly `sampleUnitL`'s `T(n)`
       trials.
     - The gcd test reads the `|w|`-bit numeral of `gcd(v, N)` as `≤ 1` and `≥ 1`. This is exact
       for `v < N`, because then `gcd ≤ N < 2^{|w|}` (`rsa_unitTest_eq`); for `v ≥ N` the first
       conjunct is already false. This is the brief's step-4 correction.
   - **`sampleClose` without P3.** `δ n = if n < 2 then 1 else e^{-n}` is the sketch's δ. The proof
     shows closeness `e^{-n}` at every `n`, since `Nat.size N ≤ 2·max(n, 2) ≤ 2(n + 2) = B(n)`
     holds also at `n ∈ {0, 1}` (`rsa_size_N_le`). `e^{-n} ≤ δ n` everywhere (`StatClose.mono`),
     so P3 is not needed. δ is negligible (`exp_neg_le_half_pow`, `Negligible.mono` from 2).
   - **`rsaGenRaw`: normalization by `1^{2m}`.**
     - `rsa_gNorm` is the remainder modulo `⟦1^{2m}⟧ = 2^{2m} − 1` (`rsa_listToNat_ones`).
     - It is the identity on `N, e, d`: `N ≤ (2^m − 1)² < 2^{2m} − 1`, and `e, d < Φ ≤ N`.
     - The validity test against `⟦1^m⟧ = 2^m − 1` with `≤` is `< 2^m`.
     - `p ≠ q` is `¬(p ≤ q ∧ q ≤ p)`.
     - `1 % Φ = 1` because `Φ ≥ 2` (`one_lt_totient`).
     - The exponent runs on the `Φ` word at its own width (the `mulStr` width), not at `2m` as
       the brief's step 5 says. That is equivalent, because `sampleUnitL` reads `⟦w⟧` and
       `Nat.size ⟦w⟧` only, and the result is normalized afterwards.
   - **S3** follows the brief's route: `statClose_rejectBlocksL`, `rsa_unitsEquiv`,
     `2^k ≤ Φ(N)(4n + 8)` and `one_sub_one_div_pow_le_exp_neg`.

7. **note: rule 10 holds under this review's seal.**
   - **Collection** (`probe/Collect.lean`, `collect.log`). The probe ran over the 187 constants
     of the ten targets and the `rsa_` family, auxiliaries included. It collected the
     other-module, non-reducible, non-instance TCSlib definitions in the elaborated types and
     values (48 names, narrow pass). Matchers are kept whatever their reducibility. The wide
     pass adds the statements of every constant used and the bodies of the own-file definitions
     used, transitively: 51 names (`NUPPT.Uniform`, `coinsCongr` and `ofPolyTime` are added).
     The foreign matchers are `polyTimeComputable_iterateFind.match_1` (read by the fill, by
     `split`) and `PolyExpr.eval.match_1` (left with `eval`). None of the 51 is a `@[simp]`
     definition.
   - **The worker's list** has 50 names, not the REPORT's "49". It equals this review's 51
     minus `NUPPT.Uniform`. The whole-file sealed copy passes with `Uniform` sealed, so the fill
     does not read it. The worker sealed `PolyExpr.eval`, which is stricter than Q1, and that
     produced its three `eval_*` failures.
   - **Not sealable** (reducible, notation under policy §1):
     - `NUPPT.Coins`, `.coins`, `.adv`, `.advice`;
     - `DistinctPrimes`, `Primes`;
     - the `Collection` projections, `PermCollection.toCollection` and
       `TrapdoorCollection.toPermCollection`.
   - **Result** (`seal/RevSealedRSA.out`). With 50 names, all 101 helpers and all ten targets
     elaborate. The only error is the base `rsaCollection_index`.
   - **Ruling Q1 confirmed.** With `PolyExpr.eval` unsealed, the frozen `eval_rsaBlock`,
     `eval_rsaTrials` and `eval_rsaSampleCoins` pass. Control C9 shows `eval_rsaBlock`'s `rfl`
     closing under the 50-name seal and failing once `eval` is added.
   - **Controls** (`seal/RevControl.lean`/`.out`). Each closes unsealed and fails sealed
     ("Type mismatch"):
     - C1: `natToList` by its body;
     - C2: `NUPPT.inParam` by `rfl`;
     - C3: `rejectBlocksL` by its body;
     - C4: `StatClose` by `Iff.rfl`;
     - C5: `Collection.index` by `rfl`;
     - C6: `polyTimeComputable_iterateFind.match_1` against a local `match` on the same
       discriminant;
     - C7: `NUPPT.Uniform` by `Iff.rfl`;
     - C8: `NUPPT.coinLen` by `rfl`.

     C6 was first tried against `Option.casesOn` and `Option.elim`. Those do not close even
     unsealed: Lean does not delta-unfold a matcher there (`seal/MatchProbe*.out`).
   - **Grep.** 215 rewrite lists and 24 `unfold`s in the added code. Every `unfold` names an
     own-file definition: `rsaGenParams`, `rsaGen`, `rsaSampler`, `rsaProb`, `rsaGenErr`,
     `rsaFromFactorStep`, `rsaFromFactorRaw` and `rsa_*`. The 10 lexical hits are terms inside
     `show … from` (`rsa_fOut_eq`, `rsa_usFind_eq`), not rules. Core and Mathlib reductions occur
     only in `rfl`/`show`, for example `rsa_val_inv_zero_le`'s `show` through `ZMod 0 = ℤ`.
   - **The base proof `rsaCollection_index` fails sealed through its `show`**, as fac's
     `factoringCollection_index` did. It is not rsa's to edit; it goes on the base re-point list.
     The re-point is
     `rw [Collection.index_eq]` followed by
     `exact (congrArg pairFstD (rsaGen_runAt H n r)).trans (pairFstD_pairEncode _ _)`. It was
     checked sealed with all 50 names (`seal/BaseRepoint.lean`, `base-repoint.log`: only the
     control copy of the old proof errs). The coin type passes through the own-file
     `rsaCollection` and the reducible projections, so no `show` is needed.

8. **nit: REPORT accuracy.** Besides finding 4 and the seal count of finding 7, the REPORT is
   accurate:
   - the targets and routes;
   - the 101 helpers by role;
   - D11 (fields `size`, `le`, `xgcd`, `divMod`, `prime`, `mul`, `sub`, `modExp`; no missing
     operation);
   - the sweep tail (RSA 0 / Rabin 19 / facade 0);
   - the axiom table;
   - the lint lines;
   - the freeze result;
   - the elaboration-cost note (finding 1 of the REPORT; the applied-form pattern is worth
     prescribing in later briefs).

   Two records for the maintainer:
   - `preship/probes/SorrySources.lean`, a before-issue item of the brief, is absent from the
     records folder, so the worker used the review's `#review_sorry` command;
   - the provided olean tree also lacks the 33 modules `Checks` needs, not only the four the
     REPORT names.

9. **nit: style.**
   - `polyTimeComputable_unitSampleStr`'s body `by exact rsa_ptc_unitSampleStr H hf` could be the
     term itself.
   - `rsa_find?_range_lt` (18 proof lines) and `rsa_drop_zeros_append` (17) have no sketch. They
     are under the lint threshold and are deleted by E4.
   - The head has 60 lines over 100 characters (the base has 25). Policy sets no limit, and E3
     reflows the docstring ones it touches.

10. **note: file size.** `RSA.lean` is 2757 lines (1122 at the base). It is 2758 with E1–E3 and
    2633 with E4. Approved exception (D2), noted only.

## Landing edits (exact)

All diffs are under `$SP/review-rsa/edits/`:
- **`landing-edits.diff`** (E1–E3). `git apply --check` is clean on the head, and applying it
  reproduces `RSAEdited.lean` byte for byte.
- **`conditional-harvest-edits.diff`** (E4). It applies on top of E1–E3 and reproduces
  `RSAEditedHarvest.lean`.

The generators are `apply_code_edits.py` (E1, E2), `apply_doc_edits.py` (E3) and `mk_harvest.py`
with `harvest-stubs.lean` (E4). Every diff touches only `TCSlib/Cryptography/Candidates/RSA.lean`,
and none changes a statement. The freeze comparison of the edited file (`declfreeze-edited.log`)
shows identical headers and no new public name. Docstring changes against the base are confined
to the **Proof sketch** paragraphs of seven public docstrings: the worker's three, and E3's
`statClose_sampleUnitL`, `rsaSampler_spec`, `rsaCollection_sampleClose` and
`polyTimeComputable_rsaFromFactorRaw`. E3 also edits `rsaCollection_invProbAt_le`, one of the
worker's three. E1 edits the docstring of the private `rsa_genCoinsEquiv`.

The edits were checked to elaborate:
- **E1–E3 unsealed** (`RSAEdited.out`): `RSA` 0 errors, 0 warnings; `Rabin` 19 own sorries; the
  facade rc 0.
- **E1–E3 sealed** with the 50 names (`RSAEditedSealed.out`): only the base
  `rsaCollection_index`.
- **Axioms** of E1–E3 (`axioms-edited.log`): the same sorry sources as the head.
- **Lint:** `style_lint.py` reports only the size line (`style-lint-edited.log`).
- **E4** against the stubs: see finding 5.

**E1** (finding 1). Delete `rsa_appendEquiv` with its docstring. In `rsa_genCoinsEquiv` replace
`(rsa_appendEquiv _ _).trans` by `(Fin.appendEquiv _ _).trans`. In `rsa_genCoinsEquiv_ofFn`
replace both `(rsa_appendEquiv _ _)` by `(Fin.appendEquiv _ _)`. In `rsa_genCoinsEquiv`'s
docstring, end the sentence with "(Mathlib's `Fin.appendEquiv`, then the length cast)".

**E2** (finding 2). Replace

```lean
/-- The modulus of generated parameters is nonzero. -/
private instance rsa_neZero_N
```
by
```lean
/-- The modulus of generated parameters is nonzero (a local instance: it is not exported). -/
private local instance rsa_neZero_N
```

**E3** (finding 3; docstring only). It replaces five **Proof sketch** passages. The exact text is
in the diff. For example, the new sketch of `polyTimeComputable_rsaFromFactorRaw`:

```
**Proof sketch.** Compute `A'` word by word (`rsa_fOut_poly`), each word one bundle field:
`p'` is `A.output` on the re-paired layout (`NUPPT.polyTimeComputable_layout`,
`A.polyTimeComputable_output`); `q'` is the quotient of `H.divMod ⟨N, p'⟩`; the test `p' q' = N`
is `H.mul` and two `H.le` comparisons, since the widths of `p' q'` and `N` differ
(`polyTimeComputable_and`); `Φ = (p' − 1)(q' − 1)` is two decrements `H.sub` with `[true]`
(run-3 audit P7-1) and `H.mul`, behind one leading zero; `d` is the second component of
`xgcdStr ⟨e, Φ⟩` (`H.xgcd`); `y^d mod N` is `H.modExp` with `|y| + 1` leading zeros before
`N` (the zeros are `H.sub ⟨1y, 1y⟩`). The two zero prefixes make every word read exactly, also on
the degenerate inputs `Φ = 0` (where `d ≤ 1`) and `N = 0` (where `y^d mod N = y^d`). The
`2n`-bit output is the truncation `(⟦0⟧_{2n} ++ v).drop |v|` of the value word `v`
(`H.sub ⟨1^{2n}, 1^{2n}⟩`, `polyTimeComputable_pairDropPoly var`), and `polyTimeComputable_ite`
selects it or `[]` by the test. The word computation equals `rsaFromFactorRaw A`
(`rsa_fOut_eq`: `divModStr_pairEncode`, `xgcdStr_pairEncode`, `modExpStr_pairEncode`,
`listToNat_subStr`, `rsa_drop_zeros_append`). -/
```

The other four:
- **`rsaCollection_sampleClose`:** δ and its negligibility; S3 at every `n`
  (`Nat.size N ≤ 2m ≤ B(n)`); `rsa_statClose_dec`; the coin and domain transports; and
  `StatClose.mono`.
- **`rsaSampler_spec`:** the last clause becomes `rsa_getD_spec`, `rsa_dec_unitSampleStr` and
  `rsaEnc_of_rsaDec`.
- **S3, step (3):** `uprob_def`, `Nat.card_congr`, `ZMod.card_units_eq_totient`
  (`rsa_uprob_units`).
- **`rsaCollection_invProbAt_le`, first paragraph:** `rsa_rsaF_injective`, and the bijection
  `(x, ω) ↦ (x^e, φ⁻¹ ω)` with `uprob_comp_equiv`, `uprob_mono` and `rsa_inner_le`. Two overlong
  lines are reflowed.

If the standing ruling is not applied to S3 (a gate-07 shared statement), drop that one hunk; the
others are independent.

**E4** (finding 5; **conditional on H1 landing with these names**). `conditional-harvest-edits.diff`:
- **Delete:** `rsa_listToNat_one`, `_nil`, `_append`, `_ones`, `_mulStr`, `_zeros_append`,
  `rsa_drop_zeros_append`, `rsa_subStr_self`, `rsa_findSome?_ite`, `rsa_find?_range_lt`,
  `rsa_comp` and `rsa_ptc_congr`.
- **Cite instead:**
  - `listToNat_singleton_true`, `listToNat_nil`, `listToNat_append`, `listToNat_replicate_true`,
    `listToNat_mulStr`, `listToNat_natToList_zero_append`, `natToList_zero_append_drop` and
    `subStr_self`;
  - `rejectBlocksL_eq_find?`, which replaces the `rejectBlocksL_eq` / `rsa_findSome?_ite` pair
    in `rsa_usFind_eq`;
  - `IterateFind.find?_range_and_lt`, `PolyTimeComputable.comp'` and `PolyTimeComputable.congr`.
- **Recheck against the real lemmas when H1 lands.** If H1 lands after rsa, H1 applies this diff
  itself.

**D1** (findings 4 and 5; ledger, no code). Add to the integration ledger for `RSA.lean`:
- **The dl-a copies** (151 lines; source `DiscreteLog.lean` at `b62c34ee`):
  - the numeral and list helpers (80 lines);
  - the loop family (71 lines).

  The loop's origin is Primality's private `spStep`/`length_spStep_*`.
- **The applied-form copies:**
  - `rsa_comp`: the five private `ptc_comp`, and the public `ColMachines.ptc_comp`;
  - `rsa_ptc_congr`: `ColMachines`/`GI`/`SimulatorMachine.ptc_congr` and the private
    `GIZK.ptc_congr`.
- **The near-duplicates in the closure:**
  - `rsa_findSome?_ite`: core `findSome?_guard` + `map_findSome?`, and
    `OneWay.findSome?_eq_bind_find?`;
  - `rsa_find?_range_lt`: `OneWay.find?_range_eq_map_find?_finRange`.
- **`rsa_appendEquiv`** (Mathlib `Fin.appendEquiv`), unless E1 lands.
- **The cross-unit parallels:**
  - `hnum` / `fac_natToList_mod`;
  - `rsa_zsel`/`rsa_zOf`/`rsa_zOf_self` / `fac_pairDec`/`fac_pairDec_pq`;
  - `rsa_listToNat_one` / fac's `hone`;
  - the `2^{size m} ≤ 2m` family.
- **The base re-point list:** `rsaCollection_index` (finding 7), beside fac's
  `factoringCollection_index` and `samplePairOut_eq_encode`.
- **The REPORT's requests, endorsed:**
  - `polyTimeComputable_rejectBlocksL`, as H2;
  - `listToNat_append`, `listToNat_replicate_true` and the truncation lemma, in H1;
  - `PolyTimeComputable.comp'`, in H1;
  - `uprob_pi_eval` in `Foundations/Probability.lean`, a separate small request.

## Not verified

- **The full 94-module sweep was not rerun.** This review checked the owned module, `Rabin`, the
  facade and `Checks` at the head, and the 11-module integration chain.
- **The 33 modules built for `Checks` are unchanged base modules.** They were compiled only to
  make `Checks` loadable.
- **Bare `simp` calls were not run through `simp?`.** No foreign definition is `@[simp]`
  (collector: `simpUnfold=false` for all 51), so they cannot unfold one.
- **E4 was checked against stubs, not against H1 itself.**

## Logs (`$SP/review-rsa/`, `SP=/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`)

- **Delivery and replay:**
  - `deliv/`: the exported delivery (`git archive` of `165dcc7d`);
  - `am.log` (empty: the replay is clean);
  - `rsa.diff`: the reviewed diff;
  - `RSA.base.lean`, `RSA.head.lean`;
  - `DiscreteLog.dla.lean` and `Factoring.fac.lean`: the comparison sources at `b62c34ee` and
    `e932cd15`.
- **Freeze:** `tools/declfreeze_rev.py`, `declfreeze-rev.log`, `declfreeze-edited.log`.
- **Elaboration:**
  - `run-checks.sh` (the driver);
  - `module-checks.log` (RSA, Rabin, the facade, then the 33 base modules and `Checks`, with
    times; also `zk-build.log`);
  - `checks-missing.txt`, `tools/missing.py`;
  - `olean-cmp.log`, `tools/olean-cmp.sh`: the three worker-built modules rebuilt and compared.
- **Axioms:**
  - `probe/Axioms.lean` (prints, sorry sources, module sweep), `axioms.log`;
  - `integration-A.log`, `integration-A-axioms.log` (fac);
  - `integration-B.log`, `integration-B-axioms.log` (fac + dl-a).
- **Rule 10:**
  - `probe/Collect.lean`, `collect.log`;
  - `seal/wide-all.txt` (51 names) and `seal/rev-sealed-names.txt` (50);
  - `seal/mkseal.py`;
  - `seal/RevSealedRSA.lean`/`.out`;
  - `seal/RevControl.lean`/`.out` (C1–C9);
  - `seal/MatchProbe{,2}.lean`/`.out` (the matcher signature and the C6 form);
  - `seal/BaseRepoint.lean`, `base-repoint.log`;
  - `tools/grepforeign.py`, `grep-foreign.txt`;
  - `probe/InstProbe.lean`/`.out` (the exported instance; `Fin.appendEquiv` in the closure).
- **Lint:** `style-lint-head.log`, `style-lint-edited.log`, `style-lint-edited-harvest.log`,
  `campaign-lint-head.log`, `campaign-lint-edited.log`.
- **`edits/`:**
  - `landing-edits.diff`, `conditional-harvest-edits.diff`;
  - the generators `apply_code_edits.py`, `apply_doc_edits.py`, `mk_harvest.py`,
    `harvest-stubs.lean`;
  - `RSAEdited.lean`/`.out`, `RSAEditedSealed.lean`/`.out`, `axioms-edited.log`;
  - `InstProbe2.lean`/`.out`;
  - `RSAEditedHarvest.lean`, `RSAHarvestStub{,Sealed}.lean`/`.out`.

The scratch worktrees `$SP/wt-rev-rsa` and `$SP/wt-rev-rsa-int` and the olean copies
`$SP/rev-rsa-oleans` and `$SP/rev-rsa-int-oleans` were removed after the runs. To replay,
recreate them from `$SP/fill-rsa-oleans`, which was only read. The exchange checkout
`$SP/wt-exchange` was only fetched; its branch did not move. No TCSlib source was changed and
nothing was committed.
