# Fill dl-c: REPORT (final)

Unit **dl-c** of `outbox/fills/dl-candidates/brief.md` (the discrete-log candidates), read with
`fill-environment-addendum.md` (v1) and `outbox/fills/NOTES-2026-11-07.md`. Owned file:
`TCSlib/Cryptography/Candidates/ElGamal.lean`. External fill worker, one host, one session.

- **Base:** `16a7d02d69cae1a700c131e3cc3dd918a7b3d6e1` (the issue commit, head of #210, fetched from
  `cryptography/pass-shelat-ch2-4-eqlemmas`). Local branch `fill/dl-c` created from the base;
  never rebased, never pushed.
- **Head of `fill/dl-c`:** `e1952eb98e9328fa6bce08784a47d24504333f19` (6 commits; `patches/` is
  `git format-patch 16a7d02d..fill/dl-c`, the whole series).
- **Diff scope:** only `TCSlib/Cryptography/Candidates/ElGamal.lean`. The diff removes exactly the
  seven `sorry` lines and adds proofs and `private` helpers (prefix `dlc_`). No statement,
  definition, docstring or import changed (no import added: the optional `DiscreteLogHardcore`
  import was not needed).
- **Final length** of the owned file: 2283 lines (base 900). Not split (notes, item 3).

## 1. Targets

All seven are **filled**. None partial, none blocked, none escalated.

| # | Target | Status | Route |
|---|---|---|---|
| 1 | `statClose_sq_generator` | filled | the sketch: `PushesUniform.uprob_eq` with `pushesUniform_sqTo_safe`, then counting (`uprob_eq_card_filter`, `Fintype.card_subtype_compl`, `card_QR_safe`): `t/N` and `s/(N−1)` with `s ≤ t ≤ s+1`, `s ≤ N−1` are within `1/N` (helper `dlc_abs_uprob_sub_uprob_ne_le`) |
| 2 | `polyTimeComputable_egGenRaw` | filled | coin cuts (`polyTimeComputable_pairTakePoly`/`_pairDropPoly`), `G.gen.polyTimeComputable_output` on `NUPPT.polyTimeComputable_layout`; the two rejection loops are one generic trial loop on `Complexity.polyTimeComputable_iterateFind` (`H.le`, `H.size`, `H.sub`); `g² mod p` by `H.mul`/`H.divMod`, `h^x mod p` by `H.modExp`; width-`n` numerals (see §1.1) |
| 3 | `polyTimeComputable_egEncRaw` | filled | the same calculus: the exponent by the loop, `h^b`, `A^b · m' mod p` by `H.modExp`, `H.mul`, `H.divMod`; the canonicalisation test `0 < m < p ∧ m^q mod p = 1` by `H.le` comparisons and `polyTimeComputable_and`, the choice by `polyTimeComputable_ite` |
| 4 | `egDecStr_apply` | filled | the sketch: `modExpStr_pairEncode`, `xgcdStr_pairEncode`, `mulStr_pairEncode`, `divModStr_pairEncode`, `listToNat_natToList` (`ZMod.val_lt`, `mul_lt_two_pow_add`-style bound via `Nat.mul_lt_mul''`) |
| 5 | `elGamal_correct` | filled | the sketch: a typed coin string of `G.gen` from the first segment (`NUPPT.coinLen_eq`, `coins_ofPolyTimeUniform`), `G.valid`/`G.wellFormed` (`wellFormedIndex_iff`, `safePrimeValid_iff`, `expValid_iff`, `dlP_eq`, `dlM_eq`); `egGen_runAt`, `egEnc_runAt`, `egDecStr_apply`; in `Z_p` `(h^a)^b · m · ((h^b)^a)⁻¹ = m` (`pow_mul`, `mul_inv_cancel₀`, `h = g² ≠ 0` from `egUnit_pos`/`egUnit_lt`); `decodeFin_ofFn` |
| 6 | `polyTimeComputable_egGroupGenRaw` | filled | as target 2, plus the test `g² mod p = 1` (two `H.le`) and the constant `4` on `polyTimeComputable_ite` |
| 7 | `elGamal_secure` | filled | the sketch's three hybrids (§1.2) |

`#print axioms` (`evidence/logs/axioms.log`): targets 1–6 depend on exactly
`[propext, Classical.choice, Quot.sound]`. `elGamal_secure` depends on
`[propext, sorryAx, Classical.choice, Quot.sound]`; the dependency-closure scan
(`evidence/logs/axioms-sorry-source.log`, probe `evidence/probes/DlcSorrySrc.lean`) finds a single
declaration with its own `sorry`: **`statClose_sampleBelowL`**, a dl-a target, used as stated
(directly in `dlc_uprob_egUnit_sq_le`, and through the base lemma `ddhExpo_statClose`). This is the
cross-unit statement dependency the brief allows ("the integration replay closes the chain");
dl-a's delivery fills it. Nothing of dl-c's own is sorried.

### 1.1 Where a proof departs from its frozen sketch (polynomial time)

- **The trial loop** (targets 2, 3, 6; helpers `dlc_ss*`, `dlc_ssLoop_eq`, `dlc_numPoly_sample`).
  The loop state carries a trial counter, as dl-a found for `polyTimeComputable_expSampleRaw`: the
  repetition lemma searches `|x| + 1 ≥ n` rounds, and without the counter a block read past the
  coins (`0 < m`) would be accepted, while `sampleBelowL` makes exactly `n` trials. The loop is
  matched against `sampleBelowL` through the published `sampleBelowL_eq_rejectBlocksL` and
  `rejectBlocksL_eq` (never by unfolding `sampleBelowL`).
- **A numeral calculus** (`dlc_NumPoly F`: `F z` is read from a polynomial-time string function).
  It is closed under the bundle's `add`, `sub`, `mul`, `divMod` (remainder against the modulus
  padded by leading zeros, so it is lossless also for the modulus `0`), `modExp` (for a positive
  modulus), `le`/equality tests and `polyTimeComputable_ite`. Numerals of width `n` are written as
  the last `|b|` bits of `⟦0⟧_n ++ b` (`⟦0⟧_n = subStr ⟨1^n, 1^n⟩`, `polyTimeComputable_pairDropPoly`),
  not by `polyTimeComputable_unaryPoly`/`_blockMap` as the sketches suggest (no pad-with-zeros
  primitive is in scope). No bundle field is missing.
- **The safe modulus.** The raw string functions are total, so `p` may read as `0`, where
  `x^e mod 0 = x^e` is exponentially long. Every `⟦V mod p⟧_n` is computed as `⟦V mod p'⟧_n` with
  `p' = p` for `p ≠ 0` and `p' = 2^n` for `p = 0` (`dlc_safeMod`, `dlc_natToList_mod_safeMod`): the
  two `n`-bit numerals agree. The canonicalisation test `m^q mod p = 1` uses `p'` too (it is only
  read when `m < p`, so `p ≠ 0`).
- **Equality of numbers** is two `H.le` comparisons, not `polyTimeComputable_pairEq` (the sketch of
  target 3): numerals of different widths can read as the same number.

### 1.2 `elGamal_secure` (Theorem 107.3)

The sketch's route, with these concrete choices.
- **`D_b`** (`dlc_exists_ddhDist`): `NUPPT.exists_comp` (the selector `M` on `pk = ⟨i, X⟩`, read
  from the tuple), `NUPPT.exists_compParam` (`D` on `⟨⟨i, X⟩, ⟨Y, ⟦Z · m'_b mod p⟧_n⟩⟩`, the
  pre-processing polynomial-time by the calculus above, `dlc_poly_ddhInput`) and `NUPPT.exists_seq`.
  The bit `b` is fixed at construction, so the advice is `M`'s and `D`'s (no `[b]` slot); its coins
  are `M`'s then `D`'s, identified with `M.Coins n × D.Coins n` by an explicit equivalence. The
  tuple is parsed by value (`listToNat`), so no cut of the last numeral is needed (the padding to
  `15n + 14` is lossless for `n ≥ n₀`, `length_ddhTuple`).
- **Hybrid 1** (`dlc_hyb1_point`, `dlc_hyb1`): the coins of the challenge and of `D_b` on
  `ddhReal (egGroupGen H G)` are both relabelled from `(G-coins × g-coins) × (a-coins × (b-coins ×
  (M-coins × D-coins)))` (`dlc_genEquiv`, `dlc_encEquiv`, `dlc_grpEquiv`, built on
  `TCSlib.Cryptography.splitCoins`; `uprob_comp_equiv`). Outside `g² ≡ 1 (mod p)` the two runs give
  `D` the same string and coins: the exponents are the same samplers (`expOrd_of_valid`,
  `ZMod.val_natCast`), `h^{(ab mod q)} = h^{ab}` (`pow_mod_orderOf`, `egSquareGen_valid`), and
  `egSquareGen p g = g² mod p`. The bad event: `Pr ≤ δ n + 9 · (1/2)^n` for `n ≥ n₀`
  (`dlc_uprob_bad_le`: the short-prime coins cost `δ n` by `hbig`; otherwise
  `Pr[(v+1)² ≡ 1] ≤ 2/(p−1) + (1/2)^n` by `statClose_sampleBelowL` with `m = p − 1` and a direct
  count of the roots `v ∈ {0, p − 2}` in `Fin (p − 1)` (`dlc_card_sq_eq_one_le`), and
  `2/(p−1) ≤ 8 · (1/2)^n` from `2^{n−1} ≤ p`).
- **Hybrid 2:** `hDDH` read through `ddhAssumption_iff` and `Ensemble.indist_iff_exists_negligible`
  gives `ε_b` for `D_b`.
- **Hybrid 3** (`dlc_rand_term`, `dlc_hyb3_point`, `dlc_hyb3`): with all coins but those of `z`
  fixed, replacing `ddhExpo n i` by a uniform `z ∈ Z_q` costs `(1/2)^n` (`ddhExpo_statClose`), and
  `z ↦ h^z · m'_b` has the law of `z ↦ h^z` because `m'_b = h^k` (`dlc_exists_pow_eq`:
  `zpowers_eq_QR`, `mem_powers_iff_mem_zpowers`) and `z ↦ z + k` is a bijection of `Z_q`
  (`Equiv.addRight`, `dlc_uprob_shift`). This is the sketch's `Equiv.mulRight` route expressed on the
  exponent; no `dlog`, no import. Averaging over the other coins (`uprob_prod`) gives
  `|Pr[D_0(random)] − Pr[D_1(random)]| ≤ 2 · (1/2)^n`.
- **Conclusion:** `ε n = 2(|δ n| + 9 · (1/2)^n) + ε_0 n + ε_1 n + 2 · (1/2)^n + [n < n₀]`, negligible
  by `Negligible.add`, `.const_mul`, `.mono`, `negligible_two_pow_neg`, `negligible_zero`. `|δ n|`
  replaces `δ n` because `δ` is only known to be nonnegative from `n₀` on; the indicator covers
  `n < n₀`, where the advantage is at most `1`. `hbig` is used as the sketch says (ruling
  R-03f1-1 (A)).

## 2. New private declarations (all `private`, prefix `dlc_`)

93 private declarations in the file (4 at the base). By role:

| Group | Names | Role |
|---|---|---|
| target 1 | `dlc_abs_uprob_sub_uprob_ne_le` | removing one point moves every probability by at most `1/|α|` |
| numerals | `dlc_listToNat_nil`, `dlc_listToNat_append`, `dlc_listToNat_true`, `dlc_natToList_mod`, `dlc_listToNat_zeros_append`, `dlc_drop_natToList_zero_append`, `dlc_subStr_self` | `listToNat`/`natToList` identities; width normalization |
| calculus | `dlc_NumPoly`, `dlc_numPoly_of_poly`, `_congr`, `_const`, `_add`, `_sub`, `_mul`, `_mod`, `_powMod`, `_two_pow`, `_ite`, `_safeMod`, `_sample`, `_egUnit`, `_egUnit_sq`, `_egCanon`; `dlc_poly_le`, `dlc_poly_eq`, `dlc_poly_natToList`, `dlc_poly_natToList_powMod`, `dlc_poly_natToList_powMulMod`; `dlc_safeMod`, `dlc_safeMod_pos`, `dlc_natToList_mod_safeMod` | polynomial-time numbers over the bundle (§1.1) |
| trial loop | `dlc_ssStep`, `dlc_ssBlock`, `dlc_ssAcc`, `dlc_ssOut`, `dlc_ssLoop` and their `_poly`; `dlc_ssStep_iterate`, `dlc_length_ssStep_le`, `dlc_length_ssStep_ssStep_le`, `dlc_length_ssStep_iterate_le`, `dlc_ssLoop_poly`, `dlc_findSome?_ite`, `dlc_find?_range_lt`, `dlc_ssLoop_eq` | the rejection sampler as an instance of `polyTimeComputable_iterateFind` |
| assembly | `dlc_poly_take`, `dlc_poly_drop`, `dlc_poly_genOut`, `dlc_poly_egGenParts`, `dlc_poly_egEncParts`, `dlc_poly_egGroupParts` | targets 2, 3, 6 |
| coins | `dlc_castEquiv`(`_ofFn`), `dlc_splitEquiv`(`_symm_ofFn`), `dlc_egGen_coinLen`, `dlc_egEnc_coinLen`, `dlc_egGroupGen_coinLen`, `dlc_genEquiv`(`_ofFn`), `dlc_encEquiv`(`_ofFn`), `dlc_grpEquiv`, `dlc_ofFn_padFin` | coin identifications for the hybrids |
| `D_b` | `dlc_tuplePk`, `dlc_ddhInput`, `dlc_poly_ddhInput`, `dlc_exists_ddhDist` | the DDH distinguisher |
| hybrid 1 | `dlc_challenge_eq`, `dlc_grp_runAt`, `dlc_hyb1_point`, `dlc_hyb1`, `dlc_abs_uprob_sub_le_of_iff`, `dlc_card_sq_eq_one_le`, `dlc_uprob_egUnit_sq_le`, `dlc_two_div_le`, `dlc_uprob_bad_le` | coupling and the bad event |
| hybrid 3 | `dlc_exists_pow_eq`, `dlc_uprob_shift`, `dlc_abs_uexp_sub_le`, `dlc_egCanon_cases`, `dlc_rand_term`, `dlc_rand_accept`, `dlc_hyb3_point`, `dlc_hyb3` | the random worlds |

**Re-points:** none. At the base, `ddhExpo_statClose` already reads `hv` through
`(expValid_iff i).1 hv`, and `egGroupGen_valid`/`egGroupGen_wellFormed` already destructure
`(wellFormedIndex_iff n _).1 (G.wellFormed n r' hn)`.

## 3. Reuse-not-copy screen (notes, item 4)

Searched TCSlib (the order list's closure and beyond) and Mathlib before and after writing. Three
helpers were rebuilt on public lemmas in this pass: `dlc_splitEquiv` on
`TCSlib.Cryptography.splitCoins` (`ofFn_splitCoins_symm`), `dlc_ofFn_padFin` on
`Collection.ofFn_padFin_of_le`, and `dlc_abs_uprob_sub_le_of_iff` on `statClose_of_uprob_ne`.
Helpers close to an existing lemma:

| Helper | Close to | Note |
|---|---|---|
| `dlc_castEquiv`, `_ofFn` | `TCSlib.Cryptography.finCastEquiv`, `ofFn_finCastEquiv` (`Asymptotic/HardCoreLemmas`, public) | that module is not in the order list (no import authorized); a copy. **Request:** move `finCastEquiv` to a common module (e.g. beside `splitCoins` in `CollectionsHelpers`) |
| `dlc_abs_uexp_sub_le` | `abs_uexp_sub_le` (`Asymptotic/Sampling`, **private**); `TCSlib.Cryptography.abs_uexp_sub_le` (`Asymptotic/PublicKeyLemmas`, public, not imported); `MultiMsg.abs_uexp_sub_le_uprob` (not imported) | a copy (`[Nonempty α]` instead of `0 ≤ c`). **Request:** make the `Sampling` lemma public |
| `dlc_listToNat_nil`, `_append`, `_true`, `dlc_drop_natToList_zero_append` | dl-a's `dla_listToNat_nil`, `dla_listToNat_append`, `dla_drop_natToList_zero_append` (private, dl-a delivery, not at the base) | same statements, written independently from the same idea. **Request:** a public `listToNat_append` beside `listToNat_eq` (`NumberTheory/Primality`) |
| `dlc_ss*`, `dlc_ssLoop_eq`, `dlc_findSome?_ite`, `dlc_find?_range_lt` | dl-a's `dla_ss*`, `dla_ssFind_eq`, `dla_findSome?_ite`, `dla_find?_range_lt` (private, dl-a delivery) | modelled on dl-a's loop (read as a template), generalised to any polynomial-time `1^n`, modulus and coins, and read through `sampleBelowL_eq_rejectBlocksL`/`rejectBlocksL_eq` instead of unfolding `sampleBelowL`. **Suggestion:** one public "rejection sampler is polynomial-time" lemma for dl-a, dl-b (the headline's samplers) and dl-c |
| `dlc_findSome?_ite` | `OneWay.findSome?_eq_bind_find?` (`Asymptotic/OneWayLemmas`, public) | a special case; the conversion is not shorter |
| `dlc_card_sq_eq_one_le` | `NumberTheory.card_sqrt_eq_two`, `card_sqrt_safe`, `uprob_sq_eq_one` (units of `Z_p`) | the count is on `Fin (p − 1)` (the sampler's range); going through an equivalence with the units is longer |
| `dlc_abs_uprob_sub_uprob_ne_le` | `Candidates.uprob_le_uprob_subtype_add`, `one_sub_div_le_uprob_subtype` (`Concrete`) | different statements (conditioning, not puncturing) |

No other near-duplicate found (`dlc_exists_pow_eq` uses `zpowers_eq_QR`; `dlc_uprob_shift`,
`dlc_NumPoly` and the hybrid lemmas are new).

## 4. Missing equations, name corrections

- **E-API:** none. Every foreign definition is read through a published equation or lemma.
- **Name corrections beyond the brief's table:** `HardcoreBit.uexp_mono`, `HardcoreBit.uexp_add`,
  `HardcoreBit.uexp_const`, `HardcoreBit.uexp_sub` and `OneWay.uprob_congr` need their namespace
  (the file opens neither); `PushesUniform.uprob_eq` was used by dot notation on
  `pushesUniform_sqTo_safe hpq`.
- **A base proof reads a foreign definition by defeq** (found by the whole-file seal,
  `evidence/logs/seal-wholefile.log`): `statClose_of_uprob_ne` (not a target) opens with
  `intro T` on `StatClose X Y _`. It is outside this unit's authorized re-points, so it is left as
  is; the re-point would be `rw [statClose_iff]` before `intro T`. With the seal placed after it,
  every other declaration of the file compiles sealed.

## 5. Verification

- **Owned file** (`evidence/logs/owned-check.log`): `scripts/lean_check_tree.sh
  TCSlib/Cryptography/Candidates/ElGamal`, exit 0, no error, no `sorry` warning (the only
  warnings are the three pre-existing unused-section-variable notes on `safe_ne_two`,
  `five_le_safe`, `safe_half`).
- **Sweep** of the whole order list (`inputs/dl-c/order.txt`, 94 modules) at the head
  (`evidence/logs/sweep.log`): 94 modules, every one exit 0 with a fresh olean. Tail:
  `=== TCSlib/Cryptography/Candidates end … exit=0`, `SWEEP DONE`. `sorry` warnings per module
  against the base (`evidence/logs/sweep-sorry-compare.log`): base 78 in 15 modules, head 71 in 14;
  the only change is `Candidates/ElGamal` 7 → 0. (The committed `inputs/dl-c/base-sorries.txt` is
  still the pre-ship list, 75 — review F3; the 78 counted here at `16a7d02d` match the brief.)
- **Axioms:** §1.
- **Rule-10 seal** (`evidence/probes/ElGamalSealed.lean`, `evidence/logs/seal.log`):
  - *names from the elaborated terms:* the probe `evidence/probes/DlcForeign.lean`
    (`evidence/logs/foreign-scan.log`) collects every constant in the types and values of the 141
    declarations of the fill (the 7 targets, the `dlc_` helpers and their auxiliary declarations),
    keeping definitions of other TCSlib modules (projections excluded; matchers would be included:
    none occur). 55 found; none is `@[simp]`, so no `attribute [-simp]` was needed. Sealed: the 52
    semireducible ones (`evidence/logs/seal-names.txt`). Left unsealed: `Complexity.PolyExpr.eval`
    (ruling Q1, notes item 2) and the reducible abbreviations `Complexity.NUPPT.Coins` and
    `Candidates.SafePrimeGen` (notation).
  - *sealed names:* `Complexity.NUPPT.advInput`, `.coinLen`, `.distinguisher`, `.distinguisherL`,
    `.inArg`, `.inCoins`, `.inParam`, `.layout`, `.output`, `.runAt`, `.runAtL`, `.Uniform`;
    `Complexity.PolyTimeComputable`, `Complexity.pairFstD`, `Complexity.pairSndD`,
    `Turing.pairEncode`; `Candidates.addStr`, `divModStr`, `dlG`, `dlM`, `dlP`, `dlW`, `expF`,
    `ExpGroupGen.FullLengthExcept`, `expOrd`, `ExpValid`, `leStr`, `modExpStr`, `mulStr`,
    `natToBits`, `natToList`, `rejectBlocksL`, `SafePrimeValid`, `sampleBelowL`, `sizeStr`,
    `subStr`, `WellFormedIndex`, `xgcdStr`; `TCSlib.Cryptography.acceptProb`, `decodeFin`,
    `distAdv`, `Ensemble.Indist`, `Negligible`, `padFin`, `splitCoins`, `StatClose`, `uexp`,
    `uprob`; `NumberTheory.listToNat`, `QR`, `sqTo`, and the instance
    `instDecidablePredUnitsZModMemSubgroupQROfNeZeroNat`.
  - *placement:* `attribute [local irreducible] …` right after the base lemma
    `statClose_of_uprob_ne` (all of the fill's code is after it; see §4 for why not before).
  - *result:* the sealed copy has exactly one error, the sealed control
    `example (i : List Bool) : dlP i = listToNat (pairFstD i) := rfl` at its end; the same
    `example` placed before the seal closes. 0 `sorry` warnings. Every fill proof compiles sealed.
  - *grep* (`evidence/logs/seal-grep.log`): the added lines contain 212 `simp`/`rw`/`dsimp`/
    `push_cast` lists (592 items) and `unfold` targets `GroupPKScheme.challenge`, `ddhExpo`,
    `ddhTuple`, `egCanon`, `egDecStr`, `egEncParts`, `egGenParts`, `egSquareGen`, `egUnit` and
    `dlc_` definitions (all in the owned file). Foreign definitions among the items or targets:
    **0** (empty result). Own-file definitions passed to `simp only`/`dsimp only`: `egGen`,
    `egEnc`, `egGroupGenMachine`, `egGenCoins`, `elGamal`, `ddhReal`, `ddhRandom`,
    `egGroupParts` (allowed: "own file").
- **Lint** (`python3 scripts/campaign_style_lint.py TCSlib/Cryptography/Candidates`,
  `evidence/logs/lint.log`): `style_lint: 7 FAIL, 9 WARN over 8 files`; **no FAIL in the
  `ElGamal.lean` rows**. The base run (`evidence/logs/lint-base.log`, 8 FAIL) had the expected FAIL
  "sorry without a proof sketch" at `polyTimeComputable_egGroupGenRaw`; it cleared. The 7 FAILs
  left are Rabin's (not this unit's). `ElGamal.lean` rows: WARN 2283 lines > 1000 (notes item 3:
  no split; recorded here) and the pre-existing check-8 WARN (the same 15 public definitions as at
  the base; no public declaration added).

## 6. Environment (addendum Part 1)

- **Preflight** (`evidence/logs/preflight.log`): `nproc` 4; cgroup v1 `memory.limit_in_bytes`
  14,337,302,528; headroom = limit − (`usage_in_bytes` − `total_cache` + `total_shmem`) =
  14,309,601,280 B (≈13.3 GiB ≥ 4 GiB); `df` on `/` (ext4, the clone, the exchange checkout and the
  scratch directory) 31,607,549,952 B free (≈29.4 GiB ≥ 12 GiB). Toolchain `leanprover/lean4:v4.25.0`
  installed by `elan` after the preflight; re-check before the cache 29,022,015,488 B free
  (`precache-disk.log`, ≥ 8 GiB).
- **Cache store** (`cache-store.log`): `/root/.cache/mathlib` absent before the first fetch (0
  archives from earlier sessions).
- **Narrowed cache** (`mathlib-roots.txt`, `cache-get.log`): 75 roots, identical to
  `inputs/dl-c/roots.txt`; "Attempting to download 2344 file(s)", 2344 downloaded, "Decompressing
  2344", `Completed successfully!`, exit 0, no failed download. Never the unfiltered command.
- **Packages** (`packages-check.log`): every present package matches `lake-manifest.json` (URL and
  revision); ABSENT `doc-gen4`, `UnicodeBasic`, `BibtexQuery`, `MD4Lean`; no module of the order
  list imports them. Last line: `RESULT: all present packages match manifest`.
- **Cache checks:** no zero-size olean (`zero-oleans.log`); a probe importing the first root
  (`Mathlib.Algebra.BigOperators.Field`) elaborated through `lean_check_tree.sh`
  (`cache-probe.log`, exit 0).
- **Bootstrap** (`bootstrap.log`): the whole order list except the owned module and the facade,
  92 modules in list order, all exit 0, `BOOTSTRAP DONE`; peak RSS 2.93 GB. Then the owned module
  and the facade in the sweep.
- One Lean process at a time throughout, every check through `scripts/lean_check_tree.sh`
  (wrapper `evidence/probes/chk.sh` logs start/end time, exit code and peak RSS). Never
  `lake build`. No timeouts, no E-RES condition (no OOM, no exit 135/137/139).
- Probe files lived in an untracked `Probe/` directory of the work clone (never committed); their
  sources are under `evidence/probes/`.

## Checklist

- [x] Each target: filled (7/7).
- [x] Every new `private`, with its role (§2); re-points: none needed (§2).
- [x] The reuse-not-copy screen (§3).
- [x] Missing equations: none; name corrections and the base defeq read (§4).
- [x] Sweep tail, axiom prints, seal (names, control, grep), lint (§5).
- [x] The diff touches only the owned file; base `16a7d02d69cae1a700c131e3cc3dd918a7b3d6e1`, head
      `e1952eb98e9328fa6bce08784a47d24504333f19`.
- [x] Delivered as `inbox/fills/dl-c/` (`REPORT.md`, `patches/`, `src/`, `evidence/`); final push
      `fill dl-c: final`.
