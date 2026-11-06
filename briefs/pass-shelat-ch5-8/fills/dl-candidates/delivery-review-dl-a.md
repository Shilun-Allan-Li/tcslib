# Delivery review: fill unit dl-a (the discrete-log candidates)

- **Delivery:** `inbox/fills/dl-a/` on `exchange/pass-shelat-ch5-8` at
  `c02469425a17e1b6cba294400687a4ae9b161b0f` (REPORT.md, 8 patches, `src/`, `evidence/`).
- **Worker branch:** `fill/dl-a`, head `70a70a8c235032d6d46da6d7f5078d7de36d2b2e`, base
  `16a7d02d69cae1a700c131e3cc3dd918a7b3d6e1` (the issue commit).
- **Brief:** `brief-issued.md`, unit dl-a. **Policy:** `policy.md`.
- **Reviewed:** 2026-11-06. Independent run: the patches were replayed in a fresh scratch worktree,
  Lean was re-run against a copy of the worker's olean tree (one process at a time, never
  `lake build`), and the seal names were collected from the elaborated terms and from the source,
  not from the worker's list.

## Verdict: **land after edits**

All seven targets are filled, sorry-free and axiom-clean. The statements are frozen, the
downstream modules elaborate, and the rule-10 seal holds under this review's own name list. The
one exception is a definitional match against an auxiliary matcher of `Repetition.lean`, which
the REPORT disclosed and which edit E1 removes. There are **no blockers and no majors**.

The edits are minor. Two code edits are proof-only:
- E1 removes the matcher defeq;
- E2 replaces a copied inequality block with a citation.

Two edits add proof sketches to private helpers that `scripts/style_lint.py` flags. One adds a
section header. One refreshes a frozen sketch, and it needs the maintainer's authorization. The
reuse disclosure is also amended (D1). All the code and docstring edits are in one patch, checked
unsealed and sealed (below).

## Checks

| # | Check | Result |
|---|---|---|
| 1 | Integrity | `git am` of the 8 patches onto `16a7d02d` in a fresh worktree: clean (empty `am.log`). The result's tree is `f8ef7a34…`, identical to the tree of `70a70a8c`. Both owned files match `src/` and the `fill/dl-a` head byte for byte (`cmp`). The diff touches only the two owned files (`2 files changed, 559 insertions(+), 7 deletions(-)`), and the only removed lines are the seven `  sorry`. `src/` holds exactly the two owned files. |
| 2 | Statement freeze | Every hunk either replaces a target's `sorry` (`statClose_rejectBlocksL`, `statClose_sampleBelowL`, `polyTimeComputable_expSampleRaw`, `expSampler_spec`, `expCollection_sampleClose`, `expCollection_invProbAt_le`, `expCollection_oneWay`) or inserts whole declarations at a declaration boundary (base lines `Concrete` 563, `DiscreteLog` 623 and 793, and after the filled body of `expCollection_sampleClose`). No base statement or docstring changed. Base sorries in the owned files: 1 + 6; at the head: 0 + 0. All 27 new declarations are `private` with the prefix `dla_`. No `set_option`, `attribute` or `open` was added. |
| 3 | Elaboration | `scripts/lean_check_tree.sh` with `TCSLIB_OLEANS` set to a copy (`$SP/review-dla/oleans`), in order: `Candidates/Concrete` (8 s), `Factoring`, `RSA`, `Rabin`, `DiscreteLog` (18 s), `DiscreteLogHardcore`, `ElGamal`, the facade `Candidates`, and `audits/pass-shelat/Checks` (129 s). All exit 0, with 0 errors. The owned files have 0 warnings. Sorry warnings per module: Factoring 10, RSA 10, Rabin 19, DiscreteLogHardcore 7, ElGamal 7, which is exactly `inputs/dl-a/base-sorries.txt` minus this unit's 7. `Checks` prints no `sorryAx` for any dl-a name. |
| 3 | Axioms | `#print axioms` for the 7 targets and `dlCollection_oneWay`: each is `[propext, Classical.choice, Quot.sound]` (`axioms.log`; the same lines in the `Checks` output). |
| 4 | Rule 10 under this review's seal | The names were collected by a meta probe over every `dla_*` and target constant: the TCSlib definitions of other modules, non-reducible and non-instance, that occur in the elaborated types and values. A wide pass adds the statements of every constant used and the bodies of the own-file definitions unfolded. The union also contains every lexical hit in the added source. **Concrete (7):** `HardcoreBit.PushesUniform`, `NumberTheory.listToNat`, `StatClose`, `bitsEquiv`, `bitsToNat`, `firstHit`, `uprob`. **DiscreteLog (31):** `NUPPT.coinLen`, `.coinsCongr`, `.coinsEquivPoly`, `.inArg`, `.inCoins`, `.inParam`, `.ofPolyTimeUniform`, `.runAt`, `PolyExpr.eval`, `PolyTimeComputable`, `pairFstD`, `pairSndD`, `polyTimeComputable_iterateFind.match_1`, `leStr`, `modExpStr`, `natToList`, `rejectBlocksL`, `sizeStr`, `subStr`, `Collection.SampleClose`, `Collection.index`, `Collection.invProbAt`, `Negligible`, `NumberTheory.listToNat`, `StatClose`, `bitsEquiv`, `bitsToNat`, `decodeFin`, `uexp`, `uprob`, `Turing.pairEncode`. None is a `@[simp]` definition. The sealed copies wrap each new region (target plus helpers) in `section revSeal … attribute [local irreducible] …`. Results: **Concrete compiles sealed** with 0 errors and 0 warnings. **DiscreteLog compiles sealed** with 0 errors and 0 warnings once `match_1` is left out. With `match_1` sealed, it fails exactly once (finding 3). With edit E1 it compiles with **all 31 names plus `rejectionSample` sealed**. The `#print axioms` inside the sealed copies are standard. **Controls** close unsealed and fail sealed ("Type mismatch: rfl"): `firstHit` by its body and `listToNat` by its body (Concrete scope); `rejectBlocksL (· < m) … = sampleBelowL m …`, `A.coinLen n = A.coins.eval n` and `listToNat` by its body (DiscreteLog scope). **Explicit unfolds:** a grep of the added code over 16 + 92 `simp`/`simp only`/`rw`/`unfold`/`dsimp`/`delta` lists finds no foreign definition used as a rewrite or unfold rule. The only hit, `bitsEquiv`, is an argument of `uprob_comp_equiv`. Every `unfold`/`rw [def]` names an own-file definition (`sampleBelowL`, `expSampleRaw`, `dlW`, `expSampler`, `expDec`, `dla_*`). The `show` steps that mention `listToNat` or `natToList` pass sealed. The seven bare `simp` calls, run through `simp?`, use core and Mathlib lemmas only (`simpq.log`). |
| 5 | Duplication | See findings 4 and 5. |
| 6 | Routes and sketches | See findings 1, 2 and 7. |
| 7 | Docstrings and policy | All 27 new declarations have docstrings. `scripts/style_lint.py` (policy checklist 4–5): at the base, 0 findings in the two files; at the head, 3: the size of `DiscreteLog`, plus `dla_ssFind_eq` (50 lines) and `dla_statClose_expDec` (39 lines) with no **Proof sketch.** (finding 6). `campaign_style_lint.py` reproduces the REPORT's line (8 FAIL, 9 WARN, none in the owned rows). Size: `DiscreteLog.lean` has 1426 lines (973 at the base) and `Concrete.lean` 689 (590). Noted only (finding 9). |

## Findings

1. **minor: the frozen sketch of `polyTimeComputable_expSampleRaw` no longer describes the
   proof.** The proof differs from the sketch in two ways:
   - the loop carries a trial counter;
   - the output is width-normalized as the last `|p|` bits of `⟦p − p⟧_{|p|} ++ block` (`H.sub`,
     `polyTimeComputable_pairDropPoly`, `PolyTimeComputable.append`), not padded by
     `polyTimeComputable_unaryPoly`/`polyTimeComputable_blockMap`.

   Policy §3 ("Synchronization") requires the sketch to change with the proof. The brief freezes
   docstrings, so the REPORT disclosed the deviations instead, which was correct. Edit E6 is the
   refresh, and it needs the maintainer's authorization of a docstring rewrite on a target.

2. **note: the two documented deviations.** Both proofs are machine-checked, so the question is
   necessity and rationale.
   - **Trial counter: necessary, but the stated reason is imprecise.** `expSampleRaw` must agree
     with `sampleBelowL m k n n` on every raw input. The repetition lemma searches
     `R|x| + 1 ≥ n` rounds with `R` a polynomial in the state length, so it cannot stop at
     exactly `n`.
     - With exactly `n·n` coins, the extra rounds read the empty block. It reads `0`, which the
       loop accepts (or rejects when `m = 0`), and `0` coincides with the fallback `getD 0`. A
       counterless loop would be correct there.
     - It is wrong when the raw coin string is longer than `n·n`: trial `n` then reads real coins
       and can accept a nonzero value.

     The counter, or an equivalent truncation of the coins to `n·n` bits, is therefore needed.
     The REPORT's reason ("a block read past the end … is `0 < m` and would be accepted") points
     at the harmless case. E6 states the real reason.
   - **Width normalization: correct, not forced.** The `drop |block|` of `⟦0⟧_W ++ block` is
     needed in any route, because `v` can reach `2^W` on raw inputs and `natToList W` keeps the
     low `W` bits. `dla_drop_natToList_zero_append` proves exactly that. The zeros could also have
     come from the sketch's ingredients: `polyTimeComputable_unaryPoly` gives `1^{|p|}` on
     `pairFstD ∘ inArg`, and `polyTimeComputable_blockMap` with block size `const 1` and
     `g = const [false]` gives `0^{|p|}`. "No pad-with-zeros primitive is in scope" is true, but
     it is not why the sketch's route fails, because that route does not fail. Using `H.sub` adds
     no assumption, since `H` is already a hypothesis. Acceptable as is.

3. **minor: a defeq read of a foreign auxiliary matcher.** `polyTimeComputable_expSampleRaw`
   closes its last step with
   `(congrArg (natToList …) (dla_ssFind_eq z)).trans ?_; unfold expSampleRaw dlW; rfl`. This
   identifies the `match` in the statement of `Complexity.polyTimeComputable_iterateFind`
   (`Repetition.lean`, matcher `polyTimeComputable_iterateFind.match_1`) with the own-file
   matcher of `dla_ssFind_eq` by definitional unfolding. Sealing `match_1` makes this exact step
   fail (`seal/RevSealedDiscreteLog.out`, line 946). The REPORT disclosed the pattern (§4,
   third note).
   - The matcher is compiler-generated from a theorem's statement, not a TCSlib-authored
     definition, so this is not a rule-10 violation in substance.
   - It is avoidable. **E1** splits the foreign `match` with `split` (which uses the matcher's
     equation lemmas) and closes each branch from `dla_ssFind_eq` after rewriting its own
     `find?`. With E1, the file compiles unsealed (0 errors, 0 warnings) and sealed with all
     31 names, `match_1` included, plus `rejectionSample` (0 errors, 0 warnings, axioms
     standard).

4. **minor: an undisclosed verbatim copy.** The `hpow` block of `statClose_sampleBelowL`
   (12 lines) proves `(1 − m/2^k)^n ≤ (1/2)^n` from `m ≤ 2^k ≤ 2m`. It repeats, line for line, the
   real-arithmetic tail of the public
   `TCSlib.Cryptography.uprob_rejectionSample_none_le_half_pow` (`Asymptotic/Sampling.lean`, in
   scope). **E2** replaces it by citing that lemma through `uprob_rejectionSample_none`, which
   adds no new foreign read: `rejectionSample` occurs only in the cited statements, and the edited
   file compiles sealed with `rejectionSample` added.

5. **minor: the reuse screen is incomplete.** The four helpers the REPORT lists are confirmed:
   - `dla_pushesUniform_restrict` has the architecture of the public
     `TCSlib.Cryptography.pushesUniform_comp_injective` (`Asymptotic/MultiMessage.lean`, outside
     the closure): the same `e₁`/`e`/`he` construction through `Equiv.ofInjective`,
     `Equiv.Set.sumCompl` and `Equiv.sumArrowEquivProdArrow`. It is generalized to any finite
     domain, with the codomain fixed to `Bool`. Related outside the closure: three copies of
     `pushesUniform_castLE` (`ZeroKnowledge/GraphIsomorphism/Proofs.lean`,
     `GraphIsomorphismZK/Closeness.lean`, `ThreeColoring/ProtocolProofs.lean`).
   - The inner `key` of `dla_listToNat_append` is the private `foldl_bits_eq` of
     `Asymptotic/Sampling.lean`: the same statement, induction and `rw` list (+`ring`). Mathlib's
     `Nat.ofDigits_append` is least-significant-digit first over `ℕ` digits, so it is not a
     drop-in. No `listToNat_append` exists in the library.
   - `dla_take_drop_ofFn` generalizes the private `NumberTheory.ofFn_chunk` (`Primality.lean`)
     from `k = B` to `k ≤ B`.
   - The `dla_ss*` loop family follows Primality's private `spStep`/`spAcc`/`spOut`.
     `dla_length_ssStep_le`, `dla_length_ssStep_ssStep_le` and `dla_length_ssStep_iterate_le` are
     near-verbatim copies of `length_spStep_le`, `length_spStep_spStep_le` and
     `length_spStep_iterate_le`: the same proofs, with the constant 2 changed to 4. That is copied
     material, not only a pattern.

   **Not disclosed:** the REPORT says "no lemma of this form found in the closure" for
   `dla_findSome?_ite` and `dla_find?_range_lt`. The closure has the following:
   - `dla_findSome?_ite` follows in four lines from core `List.findSome?_guard` and
     `List.map_findSome?` (probe `neardup.log`). `TCSlib.Cryptography.OneWay.findSome?_eq_bind_find?`
     (`Asymptotic/OneWayLemmas.lean`, in scope) is the general form.
   - `dla_find?_range_lt` is close to `OneWay.find?_range_eq_map_find?_finRange` (same file).
   - `dla_take_drop_ofFn` at `k = B` is the public `OneWay.ofFn_block_eq_take_drop`, which is in
     scope in `Concrete` through `open … TCSlib.Cryptography.OneWay`.

   None of these is a verbatim copy. They belong in the disclosure ledger (**D1**). Replacing them
   is optional.

6. **minor: missing proof sketches on two long private proofs.** `scripts/style_lint.py` reports
   `dla_ssFind_eq` (50 lines) and `dla_statClose_expDec` (39 lines) with no **Proof sketch.**
   (policy §3; the base had 0 findings in these files). The worker ran only
   `campaign_style_lint.py`, which does not check private declarations. **E3** and **E4** add the
   sketches. With them, `style_lint.py` reports only the size line.

7. **nit: the sketch of `expCollection_sampleClose`.** Its sketch still describes the internals
   of `statClose_sampleBelowL` (`NumberTheory.chunk`, `uprob_comp_equiv`, `statClose_firstHit`).
   The brief sanctions this reading. The proof also reads the decoder through
   `expEnc_eq`/`expDec_expEnc`, not `listToNat_natToList`/`ZMod.natCast_zmod_val`. No edit is
   proposed: the sketch is frozen and still true at the level it describes. Refresh it at the
   next docstring window if wanted. The other five target sketches match their proofs. (In
   `statClose_rejectBlocksL`, the restriction along the injective block layout is the splitting
   equivalence of its sketch in general form.)

8. **nit: section structure.** The new `/-! ### The domain sampler as a trial loop (helpers of …) -/`
   now heads everything up to `## Safe primes`, about 640 lines, including the public
   `expSampler`, `expCollection` and its field lemmas and three targets. **E5** inserts
   `/-! ### The domain sampler and the collection -/` after the helper group. It is a header
   line, not a declaration.

9. **note: file size.** `DiscreteLog.lean` is 1426 lines (1446 with the edits) and over the
   1000-line split threshold (`style_lint.py`: "must split"). `Concrete.lean` is 689 lines. The
   REPORT asks for a size exception or a post-fill split, for example the trial-loop section into
   `Candidates/DiscreteLogSampler.lean`. That is the maintainer's decision; it is not a landing
   condition.

10. **note: REPORT claims verified.** All targets are filled and none is partial. There are no
    re-points (the brief has none for dl-a) and no E-API or name corrections. The sweep census
    (71 in 13 modules) agrees with the downstream counts above. The axiom prints, the "seal found
    one real issue" fix (commit `70a70a8c`), the unification notes (`leStr` through
    `polyTimeComputable_not`; `le_of_le_of_eq` for the coin-average rewrite) and the
    whole-file-seal caveat for two non-target base proofs are all consistent with this review's
    runs. The worker's DiscreteLog seal list did not contain `match_1` or `modExpStr`. With
    `modExpStr` added, the seal still holds; `match_1` is finding 3.

## Landing edits (exact)

The patch is `$SP/review-dla/edits/landing-edits.diff` (`git apply --check` clean on the head). It
touches only `TCSlib/Cryptography/Candidates/DiscreteLog.lean`, and it changes no statement. E6
needs the maintainer's authorization because it rewrites a frozen docstring.
- **Unsealed:** the file with E1–E6 applied (`edits/DiscreteLogEdited2.lean`) elaborates with 0
  errors and 0 warnings.
- **Sealed:** its sealed copy (`edits/DiscreteLogEdited2Sealed.lean`: 31 names plus
  `rejectionSample`) also elaborates with 0 errors and 0 warnings, and its axiom prints are
  standard (`*.Ax.out`).
- **Downstream:** the edits are proof- and docstring-only, so downstream modules are unaffected
  (they read statements only). They were not rebuilt against the edited file.

**E1** (finding 3), in `polyTimeComputable_expSampleRaw`, replace

```lean
  rw [dla_drop_natToList_zero_append]
  refine (congrArg (natToList (pairFstD (NUPPT.inArg z)).length) (dla_ssFind_eq z)).trans ?_
  unfold expSampleRaw dlW
  rfl
```
by
```lean
  rw [dla_drop_natToList_zero_append]
  unfold expSampleRaw dlW
  congr 1
  have hF := dla_ssFind_eq z
  split
  next i hi => rw [hi] at hF; exact hF
  next hn => rw [hn] at hF; exact hF
```

**E2** (finding 4), in `statClose_sampleBelowL`, replace the body of `hpow`

```lean
    have h2k : (0 : ℝ) < 2 ^ Nat.size m := by positivity
    have hm' : (m : ℝ) ≤ 2 ^ Nat.size m := by exact_mod_cast hmk.le
    have h2' : (2 : ℝ) ^ Nat.size m ≤ 2 * m := by exact_mod_cast hk2
    apply pow_le_pow_left₀
    · rw [sub_nonneg, div_le_one h2k]
      exact hm'
    · have : (1 / 2 : ℝ) ≤ m / 2 ^ Nat.size m := by
        rw [div_le_div_iff₀ (by norm_num) h2k]
        linarith
      linarith
```
by
```lean
    rw [← uprob_rejectionSample_none m (Nat.size m) n hm hmk.le]
    exact uprob_rejectionSample_none_le_half_pow m (Nat.size m) n hm hmk.le hk2
```

**E3** (finding 6), at the end of the docstring of `dla_ssFind_eq`, replace
`` `0`, where `m` is the middle numeral of the index, `k = Nat.size m` and `n = |1^n|`. -/ `` by

```
`0`, where `m` is the middle numeral of the index, `k = Nat.size m` and `n = |1^n|`.

**Proof sketch.** After `i` steps the header is unchanged, the counter `1^n` has lost `i` bits
and the coins have lost `i` blocks of `n` bits (`dla_ssStep_iterate`): the trial value is the
`k`-bit prefix of block `i`, and the test accepts iff `i < n` and that value is below `m`. The
search over the first `|start| + 1 ≥ n` rounds is therefore the search over `[0, n)`
(`dla_find?_range_lt`), which is `sampleBelowL`'s `findSome?` read as a `find?` followed by the
value (`dla_findSome?_ite`). In the `some i` case the payload with its marker dropped is the
prefix of block `i`; in the `none` case both sides read `0` (`dla_listToNat_nil`). -/
```

**E4** (finding 6), at the end of the docstring of `dla_statClose_expDec`, replace
`` `NUPPT.coinsEquivPoly`), mapped through the decoder, which reads the numeral back exactly. -/ ``
by

```
`NUPPT.coinsEquivPoly`), mapped through the decoder, which reads the numeral back exactly.

**Proof sketch.** At a valid index of width `n`, `0 < m` and `m < p < 2^n`. Identify the
sampler's coins with `Fin (n · n) → Bool` (`NUPPT.coinsEquivPoly`, `finCongr`; the coin list is
unchanged, `NUPPT.coinsEquivPoly_ofFn`) and `Z_m` with `Fin m` by the value map. Then
`statClose_sampleBelowL`, moved along the coin identification (`StatClose.comp_equiv_left`),
mapped through `v ↦ expDec i ⟦v⟧_n` (`StatClose.map`) and moved along `Z_m ≃ Fin m`
(`StatClose.comp_equiv_right`), is the claim: its left side is the decoded sampler output
(`expSampler_runAt`), and on its right side `expDec i ⟦y.val⟧_n = some y` (`expEnc_eq`,
`expDec_expEnc`). -/
```

**E5** (finding 8), immediately before `/-- **The domain sampler is polynomial-time** [PS10, Theorem 52.3`,
insert

```
/-! ### The domain sampler and the collection -/

```

**E6** (finding 1; **needs docstring authorization**), in the docstring of
`polyTimeComputable_expSampleRaw`, replace the paragraph from `**Proof sketch.** The bit length`
to `` `polyTimeComputable_blockMap`). -/ `` by

```
**Proof sketch.** The bit length `Nat.size m` is the length of the numeral of `m` with its
leading zeros stripped (`H.size`). The trial loop is `Complexity.polyTimeComputable_iterateFind`
on the state `⟨⟨1^n, ⟨1^k, ⟦m⟧⟩⟩, ⟨c, r⟩⟩` with a trial counter `c = 1^n`: each step drops one
bit of the counter and one block of `n` coins (`polyTimeComputable_tail`,
`polyTimeComputable_pairDropPoly`), and a trial accepts iff the counter is nonempty and the first
`k` remaining coins read below `m` (`polyTimeComputable_pairTakePoly`, `polyTimeComputable_isNil`,
`H.le`). The counter is needed because the loop runs `|state| + 1 ≥ n` rounds while
`sampleBelowL` makes exactly `n` trials, and the raw coin string may be longer than `n · n`. The
payload is the accepted block; the `none` branch gives the fallback (the empty block reads `0`).
The output is the last `|p|` bits of `⟦0⟧_{|p|} ++ block`, with `⟦0⟧_{|p|} = ⟦p − p⟧_{|p|}`
(`H.sub`, `polyTimeComputable_pairDropPoly`, `PolyTimeComputable.append`): the `|p|`-bit numeral
of the value, also when it is `≥ 2^{|p|}`. -/
```

If E6 is not authorized, land without it and keep the REPORT's §1.1 note as the record (a
"sketch refresh owed" entry for the next docstring window).

**D1** (finding 5; ledger, no code). Add to the integration ledger's copied-material entries for
`DiscreteLog.lean` and `Concrete.lean`:
- the `length_spStep_*` triple (copied as `dla_length_ssStep_*`);
- the `hpow` tail of `uprob_rejectionSample_none_le_half_pow`, unless E2 lands;
- the near-duplicates `dla_findSome?_ite` (core `List.findSome?_guard` + `List.map_findSome?`;
  `OneWay.findSome?_eq_bind_find?`), `dla_find?_range_lt`
  (`OneWay.find?_range_eq_map_find?_finRange`) and `dla_take_drop_ofFn`
  (`OneWay.ofFn_block_eq_take_drop` at `k = B`; private `ofFn_chunk`).

These are in addition to the REPORT's §3 rows, whose promotion requests (`listToNat_append`,
`ofFn_chunk`, `HardcoreBit.pushesUniform_restrict`, a public block-rejection loop instance) are
endorsed.

## Logs (`$SP/review-dla/`, `SP=/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`)

- `am.log`: the `git am` replay (empty, clean).
- `module-checks.log`: the 9 module checks with start times and durations.
  `module-checks-attempt0-nolean.log` is an aborted first attempt (`lean` not on `PATH`, exit
  127; nothing was checked). `run-checks.sh` is the driver.
- `axioms.log`: the 8 axiom prints.
- `collect.log`, `collect-wide.log`, `lex-Concrete.log`, `lex-DiscreteLog.log`: the seal-name
  collection (term-based, wide, lexical). The probe sources are in `probe/`.
- `seal/`:
  - the sealed copies `RevSealedConcrete.lean`, `RevSealedDiscreteLog.lean` (with `match_1`: the
    one failure) and `RevSealedDiscreteLogNoMatcher.lean`, each with its `.out` and an `.Ax.out`
    axiom print;
  - the controls `RevControl{Concrete,DiscreteLog}{Sealed,Unsealed}.lean` with their `.out`;
  - the name lists `*-sealed-names.txt` and the generator `mkseal.py`.
- `grep-foreign.txt`: foreign names inside rewrite and unfold lists (none as a rule).
  `simpq.log`: `simp?` on the seven bare `simp` calls.
- `neardup.log`: `#check`s of the near-duplicates and a four-line reproof of `dla_findSome?_ite`
  from core lemmas.
- `style-lint-base.log`, `style-lint-head.log`, `style-lint-edited.log`, `lint-head.log`,
  `campaign-lint-edited.log`: the lint runs.
- `edits/`: `landing-edits.diff`, and `DiscreteLogEdited2{,Sealed}.lean` with their `.out` and
  `.Ax.out`. `DiscreteLogEdited{,Sealed}.lean` carry E1+E2 only.
- `dl.diff`: the reviewed DiscreteLog diff.

The olean copy `$SP/review-dla/oleans` was deleted after the runs; recreate it from
`$SP/fill-dl-a-oleans` to replay. The scratch worktree `$SP/wt-rev-dla` was removed.
