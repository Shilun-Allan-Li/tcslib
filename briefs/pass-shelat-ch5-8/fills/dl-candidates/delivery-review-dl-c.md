# Delivery review: fill unit dl-c (El Gamal and the DDH assumption)

- **Delivery:** `inbox/fills/dl-c/` on `exchange/pass-shelat-ch5-8` at
  `8d9aae12e03c09989c6fd4b22a7c373e40efbc2b` ("fill dl-c: final"; REPORT.md, 6 patches, `src/`, `evidence/`).
- **Worker branch:** `fill/dl-c`, head `e1952eb98e9328fa6bce08784a47d24504333f19` (the `From` line of
  patch 6/6), base `16a7d02d69cae1a700c131e3cc3dd918a7b3d6e1` (the issue commit), 6 commits.
- **Brief:** `brief-issued.md`, unit dl-c (with `review.md` and `../NOTES-2026-11-07.md`).
  **Policy:** `policy.md`.
- **Integration partner:** dl-a's reviewed head `b62c34ee813eeccbaa8a7cbf9964d2356fedbf14` on `fill/dl-a`.
- **Reviewed:** 2026-11-06. This was an independent run:
  - the patches were replayed in a fresh scratch worktree;
  - Lean was re-run one file at a time with `scripts/lean_check_tree.sh` against a copy of
    `$SP/fill-rsa-oleans` restored to the base (below), never with `lake build`;
  - the seal names were collected from the elaborated terms and from the statements of every
    constant they use, not taken from the worker's list;
  - the integration replay was rebuilt in a second scratch copy.

## Verdict: **land after edits**

All seven targets are filled with no `sorry`. Six print the standard axioms at the base, and
`elGamal_secure` adds `sorryAx` whose only source is dl-a's `statClose_sampleBelowL`. With dl-a's
`Concrete.lean` and `DiscreteLog.lean` at `b62c34ee` integrated, **all seven, `elGamal_secure`
included, print `[propext, Classical.choice, Quot.sound]`**. Every base statement, definition,
docstring and import is byte-identical. The 89 new declarations are all `private` `dlc_`.
`ElGamal`, the `Candidates` facade and `audits/pass-shelat/Checks` elaborate with 0 errors. The
routes, the departures included, are sound.

There are **no blockers and no majors**. The edits are minor:
- **E1** removes the one remaining definitional read: `dlc_ssLoop_poly` matches the foreign
  compiler-generated matcher `Complexity.polyTimeComputable_iterateFind.match_1` against the
  own-file matcher of `dlc_ssLoop` by defeq. The worker's seal did not contain that matcher
  (finding 3). This is the same pattern as dl-a's finding 3, and rsa's `rsa_usLoop_poly` already
  uses the `split` form E1 adopts.
- **E2** adds proof sketches to the 15 long private proofs that `scripts/style_lint.py` flags.
- **E3** refreshes four frozen target sketches. It is docstring-only and covered by the standing
  refresh ruling.
- **E4** is cosmetic: one section header and two stray blank lines.
- **E6** is optional and needs the maintainer's authorization. It re-points the base proof of
  `statClose_of_uprob_ne`, which is not a target. With it, the whole file compiles sealed.

The duplication with dl-a, rsa and dl-b is substantial, as the worker partly disclosed. The
ledger and the proposed public homes are D1 and D2 (finding 6).

## Environment and olean tree

- `$SP/rev-dlc-oleans` was copied from `$SP/fill-rsa-oleans` (base plus rsa's `RSA.lean`) at
  about 15:31. The original tree's last write is 15:15:11 (`Candidates.olean`), so the copy
  postdates the rsa worker's last write. The original was never written to.
- **Restore to base** (`base-restore.log`):
  - `Candidates/RSA` and its downstream in `inputs/dl-c/order.txt` (`Rabin`, the facade;
    `tools/downin.py`) were rebuilt at the base. Sorry counts were RSA 10 and Rabin 19.
  - The copy lacked 33 modules of `audits/pass-shelat/Checks`' closure, the `NumberTheory` facade
    and 32 `ZeroKnowledge` modules. It also had stale oleans for the `Randomized` facade,
    `ZeroKnowledge/Interaction` and `ZeroKnowledge/InteractiveProofs` (`tools/treecheck.py`). All
    of these were built from base sources, in order, with all exit 0. Afterwards treecheck
    reports 0 missing and 0 stale over the 418-module closure.
- **After the coordinator's environment note** (`env-recheck.log`):
  - every module of the dl-c order list has an olean;
  - all of `Candidates/*` (`Arithmetic`, `Concrete`, `Factoring`, `RSA`, `Rabin`, `DiscreteLog`,
    `DiscreteLogHardcore`, then `ElGamal`) was rebuilt from base sources. Each rebuilt olean is
    byte-identical (sha256) to the one the earlier checks had used;
  - `DiscreteLog`, `DiscreteLogHardcore`, `Concrete`, `Rabin` and base `ElGamal`
    (`134fd800…`) are also identical to the original tree's oleans and, for `ElGamal`, to the rsa
    review's base olean. Only `RSA` differs from the original (base vs rsa fill), as intended;
  - per-module sorry counts equal `inputs/dl-c/base-sorries.txt`.

  So every check below ran on a base tree. The head checks were then re-run
  (`module-checks2.log`), with the same results.

## Checks

| # | Check | Result |
|---|---|---|
| 1 | Integrity | Worktree `$SP/wt-rev-dlc`, detached at `16a7d02d`, with `.lake/packages` linked. `git am` of the 6 patches is clean (`am.log` empty). The result's tree is `38c809f0…`. The owned file matches `src/` byte for byte (`cmp`), and `src/` holds only that file. `git diff --stat`: 1 file, 1390 insertions, 7 deletions. The 7 removed lines are exactly the 7 `  sorry` (`dlc.diff`). |
| 2 | Statement freeze | Every hunk either replaces a target's `sorry` or inserts whole declarations at a declaration boundary (base lines 211, 511, 563, 748 and 845). No base statement, definition, docstring or import changed, and `DiscreteLogHardcore` was not imported. There are 89 new declarations, all `private dlc_` (93 private in the file, 4 at the base). No `set_option`, `attribute`, `open`, `section`, `sorry`, `native_decide` or `partial` was added. The file is 2283 lines (900 at the base); the standing user rule allows this, so it is noted only. |
| 3 | Elaboration | `ElGamal` took 13–19 s with 0 errors. Its only warnings are the three pre-existing unused-section-variable notes (`safe_ne_two`, `five_le_safe`, `safe_half`), and it has no `sorry` warning. The facade took 2 s. `audits/pass-shelat/Checks` took 122–128 s with 0 errors. ElGamal's only downstream modules are the facade and `Checks` (`downstream2.py`). Logs: `module-checks.log`, `module-checks2.log`. |
| 3 | Axioms | `axioms.log` (probe `probe/Axioms.lean`): the six targets other than the headline print `[propext, Classical.choice, Quot.sound]`; `elGamal_secure` prints `[propext, sorryAx, Classical.choice, Quot.sound]`. A dependency-closure scan (`#sorrysrc`, 22513 constants) finds exactly one declaration with its own `sorry`: **`statClose_sampleBelowL`**. The REPORT's claim is confirmed. `rsa_imp_factoring` still prints `sorryAx`, which confirms that the copy's `RSA` is the base. |
| 3 | Integration | Second worktree at the replayed head, with `Concrete.lean` and `DiscreteLog.lean` from `b62c34ee`, against a second olean copy. The 8 order-list modules downstream of `Concrete` were recompiled in order (`integration-replay.log`): `Concrete` 0 sorry, `Factoring` 10, `RSA` 10, `Rabin` 19, `DiscreteLog` 0, `DiscreteLogHardcore` 7, `ElGamal` 0, facade 0, all with exit 0. **All seven targets print the standard triple; the sorry-source scan is empty** (`integration-axioms.log`). |
| 4 | Rule 10, own seal | See findings 3 and 4. The seal has 55 names (`seal/rev-sealed-names.txt`), with `PolyExpr.eval` and its matcher left unsealed (ruling Q1). The whole-file sealed copy fails in exactly one fill proof, `dlc_ssLoop_poly` (the foreign matcher), and in the base `statClose_of_uprob_ne` (`intro T`, which the REPORT discloses). Everything else compiles sealed, base non-target proofs included. With E1 and E6, the whole file compiles sealed under all 55 names with 0 errors. Controls C1–C6 close unsealed and fail sealed. The grep of 234 tactic lists finds no foreign definition used as a rule. |
| 5 | Routes | See findings 1 and 2. |
| 6 | Duplication | See findings 5 and 6. |
| 7 | Lint | `scripts/style_lint.py` reports 0 findings at the base and 16 at the head: the size line plus 15 private proofs over 20 lines with no **Proof sketch.** After E1–E4 only the size line remains (`style-lint-{base,head,edited}.log`). `campaign_style_lint.py` reproduces the REPORT both at the head and after the edits: 7 FAIL and 9 WARN, with no FAIL in the `ElGamal` rows; the two WARNs there are the size and the pre-existing check 8. |

## Findings

1. **note: the target routes are sound, and the four polynomial-time departures (REPORT §1.1)
   are correct.** Each is machine-checked; the questions are the argument and its necessity.
   - **Trial counter: necessary, but the stated reason is imprecise**, as in dl-a's review,
     finding 2.
     - A block read past the end of the coins is empty, so it reads `0`. When accepted, it gives
       the payload `0`, which coincides with the fallback `getD 0`. That case is harmless.
     - The counter is needed for another reason. `polyTimeComputable_iterateFind` searches
       `|x| + 1 ≥ n` rounds, and here the raw segments are unbounded: `egGenRaw`'s second segment
       is the whole rest of the coins, and `egEncRaw`'s is all of them. Without the counter,
       trials `n, n+1, …` would read real coins and could accept.
     - The E3 sketch states the real reason.
   - **The `dlc_NumPoly` calculus: sound.** `F z` is the value of a polynomial-time string
     function. The closure lemmas are lossless at the widths used:
     - the product at width `|a| + |b|` (`mulStr_pairEncode`);
     - the remainder against the modulus padded with `|a|` leading zeros, so `a mod b < 2^{|a|+|b|}`
       even for `b = 0`;
     - `modExp` only for a positive modulus;
     - equality as two `H.le` comparisons, because numerals of different widths can read as the
       same number, so `polyTimeComputable_pairEq` would be wrong here.

     It uses only bundle fields, and no field is missing.
   - **Width-`n` numerals by `⟦0⟧_n ++ b`: sound.** The proof `dlc_drop_natToList_zero_append`
     is dl-a's `dla_drop_natToList_zero_append` and rsa's `rsa_drop_zeros_append`. The sketches'
     `unaryPoly`/`blockMap` route would also have worked, as dl-a's review notes, so this choice
     is not forced.
   - **`dlc_safeMod` for `p = 0`: sound and necessary.**
     - The raw functions are total, so `p` may read as `0`, and `A^b mod 0 = A^b` with an
       arbitrary `A` is exponentially long.
     - `⟦V mod 0⟧_n = ⟦V⟧_n = ⟦V mod 2^n⟧_n` (`dlc_natToList_mod_safeMod`).
     - The canonicalisation test uses the safe modulus only under `m < p`, where it equals `p`
       (`dlc_numPoly_egCanon`).
   - **`elGamal_secure`'s three hybrids (REPORT §1.2): sound.**
     - **`D_b` has advice `M`'s and `D`'s, with the bit fixed in the machine** (not the sketch's
       `[b]` slot). This is legitimate, because one distinguisher per bit is all that Hybrid 2
       needs.
     - **The tuple is parsed by value, with no cut of the last numeral.** This is correct from
       `n₀` on, where the padding is the identity (`length_ddhTuple`). Below `n₀` the advantage is
       bounded by `1` through the indicator term, so nothing is lost.
     - **Hybrid 1** couples over `((r, u_g), (u_a, (u_b, (r_M, r_D))))`. The pointwise identity
       (`dlc_hyb1_point`) uses that `ddhExpo` is literally the sampler of
       `egGenParts`/`egEncParts` at `expOrd i = q`, and that `h^{ab mod q} = h^{ab}`
       (`pow_mod_orderOf`).
     - **The bad event** is bounded by a direct count of `{0, p − 2}` in `Fin (p − 1)`
       (`dlc_card_sq_eq_one_le`), not by `uprob_sq_eq_one`. That gives `2/(p − 1) = 1/q`, the
       sketch's value, without the transport to units. The bound
       `2/(p − 1) ≤ 8 (1/2)^n` from `2^{n−1} ≤ p` is correct.
     - **Hybrid 3** uses the exponent shift `z ↦ z + k` with `m'_b = h^k` (`dlc_exists_pow_eq`
       through `zpowers_eq_QR`). This is the sketch's `Equiv.mulRight` route, read on the
       exponent; it needs no `dlog` and no import. The coins `u₃` of `z` are independent of
       everything that `m'_b` depends on (`u_a`, `r_M`), so the pointwise argument is valid.
     - **The final `ε`** uses `|δ n|` and the indicator of `n < n₀`. Both are negligible, and
       `hbig` is used as ruled (R-03f1-1 (A)).
   - **The other targets** follow their sketches: `statClose_sq_generator` (counting with
     `s ≤ t ≤ s+1`, `s ≤ N−1`), `egDecStr_apply` and `elGamal_correct`. See finding 7 for two
     nits.

2. **minor: four frozen sketches no longer describe their proofs.**
   - `polyTimeComputable_egGenRaw` and `polyTimeComputable_egEncRaw` name
     `polyTimeComputable_unaryPoly`/`_blockMap` padding, `H.modExp` for `g²`, and
     `polyTimeComputable_pairEq`. None of these is used, and the counter and the safe modulus are
     not mentioned.
   - The parenthetical sketch of `polyTimeComputable_egGroupGenRaw` names `H.modExp` and
     `pairEq`. The proof computes `g · g` by `H.mul`, then `H.divMod`, and compares by two
     `H.le`.
   - `elGamal_secure` names the advice slot `[b]`, the cut `polyTimeComputable_pairTakePoly var`,
     `uprob_sq_eq_one`/`card_sqrt_safe`, `StatClose.map`, `StatClose.abs_uprob_sub_le_prod`,
     `expF_injective`/`card_QR_safe`/`Equiv.mulRight`, and an `ε` without the `[n < n₀]` term.

   Policy §3 ("Synchronization") requires the sketch to follow the proof. The brief froze
   docstrings, so the REPORT's §1.1/§1.2 disclosure was correct behaviour. **E3** is the exact
   refresh. It changes only the sketch text, and no statement. The standing refresh ruling covers
   it.

3. **minor: a definitional read of a foreign matcher in `dlc_ssLoop_poly`.**
   - The proof is the term `polyTimeComputable_iterateFind …`, whose type has the foreign
     `match` (`Complexity.polyTimeComputable_iterateFind.match_1`, `Repetition.lean`). It is
     checked against `PolyTimeComputable dlc_ssLoop` by unfolding `dlc_ssLoop` and identifying
     the two matchers by defeq.
   - With `match_1` sealed, exactly this step fails: `seal/RevSealedElGamal.out`, line 901,
     "Type mismatch". Control C5 is the same term.
   - The REPORT's collector looked only at the types and values of the fill's own declarations
     ("matchers would be included: none occur"). The matcher sits in the *statement* of a cited
     theorem. This review's wide pass (statements of every used constant) finds it, as dl-a's
     review did for the same lemma.
   - The matcher is compiler-generated from a theorem's statement, so this is not a rule-10
     violation in substance. The NOTES (item 4) ask for such matchers to be sealed, and it is
     avoidable.
   - **E1** transports along a pointwise equation and `split`s the foreign `match` through its
     equation lemmas. This is the form of rsa's `rsa_usLoop_poly` and of dl-a's landed E1.
   - **With E1, the whole file compiles sealed under all 55 names** (with E6; without E6, only
     the base `statClose_of_uprob_ne` fails, as at the head).

4. **note: rule 10 holds otherwise, under this review's seal.**
   - **Collection** (`probe/Collect.lean`, `collect.log`). Over the 141 constants of the 7
     targets and the `dlc_` family (auxiliaries included), the collector takes the other-module,
     non-reducible, non-instance TCSlib definitions in the elaborated types and values. The
     narrow pass gives 52 names.
   - The wide pass adds the statements of every constant used and, transitively, the bodies of
     the own-file definitions used. That gives 55 names; it adds `NUPPT.ofPolyTimeUniform`,
     `HardcoreBit.PushesUniform` and `polyTimeComputable_iterateFind.match_1`.
   - The only matcher of a found definition is `PolyExpr.eval.match_1`, which is unsealed with
     `PolyExpr.eval` (Q1). No collected definition is `@[simp]` (`simpUnfold=false` for all), so
     the 24 bare `simp`/`simp_all` calls cannot unfold one.
   - **Seal:** the union with the worker's 52 names, minus `PolyExpr.eval` and its matcher, is 55
     names. It includes the worker's sealed instance
     `NumberTheory.instDecidablePredUnitsZModMemSubgroupQROfNeZeroNat`.
   - **Differences from the worker's list.** The worker left out `NUPPT.ofPolyTimeUniform`,
     `HardcoreBit.PushesUniform` and `match_1`. The first two pass sealed; `match_1` is finding 3.
     The worker correctly left `PolyExpr.eval` unsealed and said so.
   - **Placement.** This review sealed the whole file right after the `open` line, not after
     `statClose_of_uprob_ne` as the worker did, so that the base proofs are tested too. The only
     base proof that fails sealed is `statClose_of_uprob_ne`: `intro T` on `StatClose`, line 198,
     which the REPORT discloses in §4. Every other base proof passes sealed: `ddhExpo_statClose`,
     `egGroupGen_valid` and `_wellFormed`, `constSelector_unique`, the `runAt` lemmas, and so on.
     **E6** re-points it with `rw [statClose_iff]` before `intro T`, the replacement the REPORT
     names; it is checked unsealed and sealed. It is outside the brief's authorized re-points, so
     it needs the maintainer's authorization, or it can go to #210's next round.
   - **Controls** (`seal/controls.lean`, appended to the unsealed and sealed copies): each closes
     unsealed (`RevControlUnsealed.out`, 0 errors) and fails sealed (6 × "Type mismatch"):
     - C1: `dlP` by its body;
     - C2: `A.coinLen n = A.coins.eval n` by `rfl`;
     - C3: `StatClose` by its body;
     - C4: `sampleBelowL = rejectBlocksL (· < m)` by `rfl`;
     - C5: the `match_1` read of finding 3;
     - C6: `splitCoins` by its body.
   - **The loop is matched against `sampleBelowL` only through the published equations:
     verified.**
     - `dlc_ssLoop_eq` rewrites with `sampleBelowL_eq_rejectBlocksL` then `rejectBlocksL_eq`.
     - No `unfold`, `simp` or `rw` list names `sampleBelowL` or `rejectBlocksL`.
     - With both sealed (C4 shows the seal is active), `dlc_ssLoop_eq`, `dlc_numPoly_sample` and
       every consumer compile.
     - The other uses of the sampler (`dlc_uprob_egUnit_sq_le`, `dlc_hyb1_point`) only compare
       `sampleBelowL …` applications syntactically, or apply `statClose_sampleBelowL` and
       `sampleBelowL_lt`.
   - **Grep** (`tools/grepforeign.py`, `grep-foreign.txt`): 234 `simp`/`simp only`/`rw`/`rwa`/
     `dsimp`/`unfold` lists in the added code. No foreign definition is used as a rule. The three
     lexical hits are arguments: `listToNat`/`natToList` inside a `show` and inside the arguments
     of `mul_comm` and `uprob_comp_equiv`. Every `unfold` names an own-file definition (`egCanon`,
     `egUnit`, `egSquareGen`, `egGenParts`, `egEncParts`, `egDecStr`, `ddhExpo`, `ddhTuple`,
     `GroupPKScheme.challenge`, `dlc_*`).
   - **Remaining readings after E1:** none in the fill. The only other one is the base
     `statClose_of_uprob_ne` (E6). No published lemma is missing (no E-API), which confirms the
     REPORT.

5. **minor: the reuse screen understates the duplication.** The disclosed rows are confirmed:
   - `dlc_abs_uexp_sub_le` duplicates both the private lemma of `Asymptotic/Sampling.lean:204` and
     the public `TCSlib.Cryptography.abs_uexp_sub_le` (`PublicKeyLemmas.lean:823`, not
     imported). The latter is itself a copy of the former, with the same full name.
   - `dlc_castEquiv` duplicates `finCastEquiv`/`ofFn_finCastEquiv` (`HardCoreLemmas`, not
     imported).
   - The `dlc_ss*` trial loop is dl-a's `dla_ss*`, line for line (`ssStep`, `ssBlock`, `ssAcc`,
     `ssOut`, `ssStep_iterate`, the three length bounds, `findSome?_ite`, `find?_range_lt`), with
     `dla_ssFind_eq` generalized to `dlc_ssLoop_eq` (any `u`, `ks`, `ms`, `c`) and read through
     the published equations.
   - `dlc_listToNat_{nil,append}` and `dlc_drop_natToList_zero_append` duplicate dl-a's
     `dla_` versions.

   **Not disclosed** (the rsa and dl-b fills ran in parallel, so this is a ledger item, not a
   fault):
   - **rsa** (`wt-fill-rsa`, `RSA.lean`) has a third copy of almost everything:
     - `rsa_listToNat_append` (:2394), `rsa_listToNat_nil` (:655), `rsa_listToNat_one` (:650,
       which is `dlc_listToNat_true`);
     - `rsa_listToNat_zeros_append` (:2409), `rsa_drop_zeros_append` (:2415);
     - `rsa_subStr_self` (:2436), which is `dlc_subStr_self` verbatim;
     - `rsa_findSome?_ite` (:660), `rsa_find?_range_lt` (:675);
     - the trial loop `rsa_us{Step,Block,Acc,Out,Loop}` with `rsa_usStep_iterate` and the three
       length bounds (:727–:930). This is the same state machine with a gcd conjunct in the test,
       because `sampleUnitL` is `rejectBlocksL (v < N ∧ coprime)`;
     - `rsa_le_poly` (:790), which corresponds to `dlc_poly_le`.
   - **dl-b** (`wt-fill-dl-b`, `DiscreteLogHardcore.lean`) has `dlb_listToNat_one` (:1003), the
     modular numeral layer `dlb_{mulMod,powMod,invMod,quot,rem}_natToList` (:1008–:1080, a fixed
     width form of the same bundle reading as `dlc_numPoly_*`), and `dlb_ptc` (:992).
   - **The inline `hnum`** (`natToList W N = natToList W (N % 2^W)`) of dl-a's and rsa's width
     lemma is `dlc_natToList_mod`.
   - **The congruence pattern.** The base file's own private `polyTimeComputable_of_forall_eq`
     (`ElGamal.lean:602`) is exactly the `(congrArg PolyTimeComputable (funext fun z => ?_)).mp`
     pattern that the fill writes 12 times. It is the same as `rsa_ptc_congr` (RSA :1080) and
     close to `dlb_ptc` and the private `ptc_comp` of `Randomized/Closure.lean:171`.
   - **Core lemmas.** `dlc_findSome?_ite` follows from core `List.findSome?_guard` with
     `List.map_findSome?`, as dl-a's review noted. `StateLoop.find?_range_eq_some`
     (`Build/StateLoop.lean:170`) is related to `dlc_find?_range_lt`, but it is not a drop-in.

   No number-theoretic fact is re-proved. `dlc_exists_pow_eq` uses `zpowers_eq_QR` and
   `mem_powers_iff_mem_zpowers`; `dlc_card_sq_eq_one_le` counts in `Fin (p − 1)`, the sampler's
   range, where `card_sqrt_eq_two` on units would need a transport. Mathlib has no `listToNat`,
   and `Nat.ofDigits` is least-significant-digit first, so it is not a drop-in. No E-edit replaces
   a helper here: the shared homes are in files the fills do not own. **D1** is the ledger and
   **D2** the proposal.

6. **minor: 15 long private proofs have no proof sketch** (policy §3, checklist 4;
   `style_lint.py`). The 15 are:
   - `dlc_abs_uprob_sub_uprob_ne_le`, `dlc_ssLoop_eq`, `dlc_numPoly_egCanon`,
     `dlc_poly_egEncParts`, `dlc_poly_ddhInput`;
   - `dlc_card_sq_eq_one_le`, `dlc_uprob_bad_le`, `dlc_exists_pow_eq`, `dlc_challenge_eq`;
   - `dlc_hyb1_point` (75 lines), `dlc_hyb1`, `dlc_rand_term`, `dlc_rand_accept`,
     `dlc_hyb3_point`, `dlc_hyb3`.

   The worker ran only `campaign_style_lint.py`, which skips private declarations. **E2** appends
   a `**Proof sketch.**` paragraph to each existing docstring. Afterwards `style_lint.py`
   reports only the size line.

7. **nit: smaller sketch and REPORT points.** No edit is proposed for these.
   - `egDecStr_apply`'s sketch cites `mul_lt_two_pow_add`, which needs equal widths. The proof
     uses `pow_add` with `Nat.mul_lt_mul''` because `|c₂| ≠ |p|`. The REPORT says this.
   - `elGamal_correct`'s sketch works with units `h_u, m_u` and `Units.mul_inv_cancel_right`. The
     proof works in the field `ZMod p` with `mul_inv_cancel₀`. Both are still true at the level
     they describe.
   - REPORT §1.1's counter reason is finding 1; its "matchers: none occur" is finding 3.
   - The rest of the REPORT is accurate:
     - the route table;
     - "no re-points needed". At the base, `ddhExpo_statClose` reads `hv` through
       `(expValid_iff i).1 hv`, and `egGroupGen_valid`/`_wellFormed` destructure through
       `wellFormedIndex_iff`, as confirmed;
     - no E-API;
     - the namespace corrections (`HardcoreBit.uexp_*`, `OneWay.uprob_congr`);
     - the base defeq read of `statClose_of_uprob_ne`;
     - 89 new privates;
     - the lint line;
     - the axioms.
   - The REPORT's sweep (94 modules) was not rerun here (see "Not verified").

8. **nit: section structure.** The helper group `### Helpers of the polynomial-time targets`
   now heads `egGen`, `egEnc`, `egDecStr`, `elGamal` and `elGamal_correct` too. **E4** inserts
   `/-! ### El Gamal's algorithms -/` before the docstring of `polyTimeComputable_egGenRaw`, and
   removes the two double blank lines after the bodies of `polyTimeComputable_egGenRaw` and
   `_egEncRaw`.

9. **note: file size.** `ElGamal.lean` is 2283 lines; it is 2390 with E1–E4 and 2391 with E6.
   The standing user rule allows this, with no split; the REPORT records the length. A natural
   later split is the `dlc_NumPoly` calculus with the trial loop, which D2 moves out anyway.
   Noted only.

## Landing edits (exact)

The diffs are under `$SP/review-dlc/edits/`
(`SP=/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`):
- `landing-edits.diff` holds E1–E4 and applies with `git apply --check` (clean on the head);
- `landing-edits-E1-E2-E4.diff` holds the code, private-docstring and cosmetic edits;
- `landing-edits-E3-docrefresh.diff` is the target sketch refresh, on top of them;
- `landing-edits-E6-optional.diff` is the base re-point, on top of E1–E4.

The stack E1-E2-E4, then E3, then E6 was checked to apply in order and to reproduce the
generator's output. The generator is `apply_edits.py`. Every diff touches only
`TCSlib/Cryptography/Candidates/ElGamal.lean`, and none changes a statement: the removed lines
are docstring text, the 5-line body of `dlc_ssLoop_poly` and two blank lines.

The edits were checked to elaborate (each `.Ax.lean` has the axiom prints appended):
- **E1–E4** (`ElGamalEdited.Ax.out`): 0 errors, with only the three pre-existing linter warnings.
  The six concrete targets print the standard triple; `elGamal_secure` carries only dl-a's base
  `sorryAx`.
- **E1–E4 + E6** (`ElGamalEdited-E6.Ax.out`): the same results, and `statClose_of_uprob_ne` is
  standard.
- **The sealed copy of E1–E4 + E6** (`ElGamalEdited-E6-Sealed.Ax.out`, a whole-file seal of the
  same 55 names, `match_1` included): **0 errors** and the same axiom prints.
- **`style_lint.py`** on the edited file reports only the size line.

The edits are proof- and docstring-only, so the facade and `Checks`, which read statements
only, are unaffected.

**E1** (finding 3). Replace `dlc_ssLoop_poly` and its one-line docstring by

```lean
/-- The trial loop is polynomial-time (the repetition lemma with `R = var`, its `match` read by
`split`). -/
private theorem dlc_ssLoop_poly (H : ArithmeticFP) : PolyTimeComputable dlc_ssLoop := by
  refine (congrArg PolyTimeComputable (funext fun x => ?_)).mp
    (polyTimeComputable_iterateFind dlc_ssStep_poly (dlc_ssAcc_poly H) dlc_ssOut_poly
      PolyExpr.var (PolyExpr.add (.mul (.const 2) .var) (.const 4)) (fun x i _ => by
        simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
        exact dlc_length_ssStep_iterate_le x i))
  -- the repetition lemma's `match` is split by its equation lemmas, not matched by defeq
  rw [PolyExpr.eval_var]
  unfold dlc_ssLoop
  split
  next i hi => rw [hi]
  next hn => rw [hn]
```

**E2** (finding 6). Append a `**Proof sketch.**` paragraph to the docstrings of the 15 helpers
listed there. The exact text is in `landing-edits-E1-E2-E4.diff`. For example, for
`dlc_hyb1_point`:

```
**Proof sketch.** Both sides are `D` on one string (`NUPPT.distinguisher_eq`,
`NUPPT.distinguisherL_eq`, `he`, `dlc_challenge_eq`). The derived index `i` (`dlc_grp_runAt`) is
valid and well formed, `⟨p, ⟨q, h⟩⟩` with `p`, `q` from `G`'s index (`wellFormedIndex_iff`,
`safePrimeValid_iff`) and `h = egSquareGen p g = g² mod p` off the bad event, of order `q`
(`egSquareGen_valid`). The padding of the tuple is lossless (`dlc_ofFn_padFin`,
`length_ddhTuple`), so `D_b` reads `⟨i, X⟩`, `Y` and `Z` back. The exponent `ddhExpo n i u` has
the value of the sampler `sampleBelowL q (Nat.size q) n n u` of `egGenParts`/`egEncParts`
(`expOrd_of_valid`, `ZMod.val_natCast`, `sampleBelowL_lt`), `expF i z` is the numeral of
`h^z mod p` (`expF_eq`, `WellFormedIndex.dlW_eq`), and `(h^x mod p)^y · c ≡ h^{xy mod q} · c
(mod p)` since `h` has order `q` (`ZMod.val_mul`, `pow_mod_orderOf`,
`ZMod.natCast_eq_natCast_iff'`). -/
```

**E3** (finding 2; docstring only, under the standing refresh ruling). Replace:
- the `**Proof sketch.**` paragraphs of `polyTimeComputable_egGenRaw`,
  `polyTimeComputable_egEncRaw` and `elGamal_secure`;
- the parenthetical of `polyTimeComputable_egGroupGenRaw`.

The new text is in `landing-edits-E3-docrefresh.diff`. It names:
- the numeral calculus over the bundle;
- the trial counter, with its real reason (the `|x| + 1` rounds and raw segments longer than
  `n · n`);
- the reading through `sampleBelowL_eq_rejectBlocksL`/`rejectBlocksL_eq`;
- the modulus `2^n` in place of `0` and the padded remainder;
- `⟦0⟧_n ++ b` in place of `unaryPoly`/`blockMap`;
- the equality as two `H.le` instead of `pairEq`;
- for `elGamal_secure`: the advice without a bit slot, the by-value parse with no cut, the direct
  count of the roots `{0, p − 2}`, the exponent shift `z ↦ z + k` (`Equiv.addRight`) and the
  final `ε` with `|δ n|` and the indicator of `n < n₀`.

The `**Deviation:**` and `Repair` paragraphs and every statement are untouched. If E3 is not
landed, keep REPORT §1.1–§1.2 as the record ("sketch refresh owed").

**E4** (finding 8; cosmetic). Insert `/-! ### El Gamal's algorithms -/` and a blank line before
the docstring of `polyTimeComputable_egGenRaw`, and drop the second of the two blank lines after
the bodies of `polyTimeComputable_egGenRaw` and `polyTimeComputable_egEncRaw`.

**E6** (finding 4; optional, **needs the maintainer's authorization**: a base non-target proof,
outside the brief's authorized re-points). In `statClose_of_uprob_ne`, insert
`  rw [statClose_iff]` before `  intro T`. Without it, the only sealed failure left in the file is
this base proof. Alternatively, route it to #210's next round.

**D1** (finding 5; ledger, no code). Add these entries to the integration ledger for
`ElGamal.lean`:
- the trial-loop copies `dlc_ss*`, `dlc_ssLoop_eq`, `dlc_findSome?_ite`, `dlc_find?_range_lt`
  (dl-a's `dla_ss*`/`dla_ssFind_eq`; rsa's `rsa_us*`/`rsa_usFind_eq`, `rsa_findSome?_ite`,
  `rsa_find?_range_lt`);
- the numeral copies `dlc_listToNat_{nil,append,true,zeros_append}`, `dlc_natToList_mod`,
  `dlc_drop_natToList_zero_append`, `dlc_subStr_self` (dl-a's `dla_` versions; rsa's
  `rsa_listToNat_{nil,append,one,zeros_append}`, `rsa_drop_zeros_append`, `rsa_subStr_self`;
  dl-b's `dlb_listToNat_one`, `dlb_listToNat_cons`);
- the bundle readings `dlc_numPoly_*`, `dlc_poly_le`/`_eq` (`rsa_le_poly`; dl-b's
  `dlb_*_natToList` layer);
- `dlc_abs_uexp_sub_le` (Sampling's private `abs_uexp_sub_le` and its public copy in
  `PublicKeyLemmas`);
- `dlc_castEquiv` (`finCastEquiv`);
- the inline congruence pattern (`polyTimeComputable_of_forall_eq` in this file, `rsa_ptc_congr`,
  `dlb_ptc`, `ptc_comp`).

**D2** (finding 5; proposed public helpers, so that the landing PRs cite one copy). Land these
in a shared-file window before or with the dl-a/rsa/dl-c landings, and re-point the three fills
to them:
1. **`NumberTheory/Primality.lean`**, beside `listToNat_eq`: `listToNat_nil`, `listToNat_append`
   (most significant bit first), `listToNat_singleton_true`, and dl-b's `listToNat_cons`.
2. **`Candidates/Arithmetic.lean`**, beside `natToList_eq` and `subStr_pairEncode`:
   `natToList_mod_two_pow`, `listToNat_natToList_zero_append`, `drop_natToList_zero_append` (the
   width normalization) and `subStr_self`.
3. **`Candidates/Concrete.lean`**, beside `rejectBlocksL`, one public trial loop:
   - the generic state machine (step, block, acceptance, payload) with its orbit lemma and the
     length bounds;
   - `polyTimeComputable_rejectBlocksL`: for polynomial-time `u` (block length and trial count),
     `k`, the coins and an acceptance test that is polynomial-time on `⟨header, block⟩`, the value
     `(rejectBlocksL E k |u| |u| c).getD 0` is the value of a polynomial-time string function,
     proved through `rejectBlocksL_eq` with the `split` form of E1;
   - corollaries for `sampleBelowL` (in `DiscreteLog.lean`, the form of `dlc_numPoly_sample`) and
     for rsa's `sampleUnitL` (in `RSA.lean`).

   `Concrete` already imports `Arithmetic` and, transitively, `Repetition`.
4. **`Complexity/Randomized/Repetition.lean`**, beside `polyTimeComputable_iterateFind`:
   `find?_range_and_lt` (the three `find?_range_lt`). For the three `findSome?_ite`, cite core
   `List.findSome?_guard` with `List.map_findSome?`.
5. **`Complexity/ClassNP/PolyTime.lean`**, beside `PolyTimeComputable`:
   `PolyTimeComputable.congr` (pointwise) and an applied `comp'`. These replace this file's
   private `polyTimeComputable_of_forall_eq`, `rsa_ptc_congr`/`rsa_comp`, `dlb_ptc` and
   `Closure`'s `ptc_comp`.
6. **`Asymptotic/Sampling.lean`**: make `abs_uexp_sub_le` public and delete the same-named copy in
   `PublicKeyLemmas.lean`, which imports Sampling. Then `dlc_abs_uexp_sub_le` becomes
   `abs_uexp_sub_le (by positivity)`.
7. **`Asymptotic/CollectionsHelpers.lean`**: move `finCastEquiv`/`ofFn_finCastEquiv` from
   `HardCoreLemmas` beside `splitCoins`, as the worker requests. `dlc_castEquiv` then goes.
8. **Optional:** a public numeral calculus (`dlc_NumPoly` with its closure lemmas, or dl-b's
   fixed-width layer) in `Candidates/Arithmetic.lean`. Which one is a design choice for the
   maintainer. dl-c's value-level form covers rsa's and dl-b's uses.

## Not verified

- The full 94-module sweep was not rerun. This review checked `ElGamal`, its downstream (the
  facade and `Checks`), all of `Candidates/*` at the base, the 36 modules of `Checks`' closure
  that the copy lacked, and the 8-module integration chain.
- The 24 bare `simp`/`simp_all` calls were not run through `simp?`. No collected foreign
  definition is `@[simp]`-unfoldable, so they cannot read one, and the sealed copy compiles them.

## Logs (`$SP/review-dlc/`, `SP=/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`)

- `deliv/`: the exported delivery, from `git archive` of `8d9aae12`.
- `base.lean` and `head.lean`, the owned file at the base and at the head; `dlc.diff`,
  `dlc.patchdiff` and `added.txt`, the reviewed diff; `am.log`, which is empty.
- The tree:
  - `base-restore.log` (with `restore.log`, `base-ladder.log`, `restore-order.txt`,
    `base-order.txt`, `zk-order.txt`);
  - `env-recheck.log` (with `cand-ladder.log`, `cand-order.txt`, `eg-base.log`, `before.txt`);
  - `tools/downin.py` and `tools/treecheck.py`.
- `run-checks.sh`, `module-checks.log` and `module-checks2.log`, the module checks with times.
- `axioms.log` (probe `probe/Axioms.lean`, which includes `#sorrysrc`); `integ-order.txt`,
  `integration-replay.log`, `integration-axioms.log` and `integration-tree.txt`.
- `probe/`:
  - `run1.sh` and `run1int.sh`, the probe runners;
  - `Collect.lean`, the seal-name collector, with `collect.log`, `seal-rows.txt`, `narrow.txt`,
    `wide.txt`, `wide-only.txt` and `worker.txt`;
  - `MatchProbe.lean`, the matcher in `iterateFind`'s statement.
- `seal/`:
  - `rev-sealed-names.txt` (55 names) and `mkseal.py`;
  - `controls.lean` (C1–C6);
  - `RevControlUnsealed.lean` and `.out` (0 errors);
  - `RevSealedElGamal.lean` and `.out`: the whole-file seal, with errors at :198 (base
    `statClose_of_uprob_ne`), at :901 (`dlc_ssLoop_poly`) and at the 6 controls.
- `tools/grepforeign.py` and `grep-foreign.txt`.
- `style-lint-{base,head,edited}.log` and `campaign-lint-{head,edited}.log`.
- `edits/`:
  - `landing-edits.diff`, `landing-edits-E1-E2-E4.diff`, `landing-edits-E3-docrefresh.diff` and
    `landing-edits-E6-optional.diff`;
  - `apply_edits.py`, the generator;
  - `ElGamalEdited{,-nodoc,-E6}.lean`, `ElGamalEdited{,-E6,-E6-Sealed}.Ax.lean` with their
    `.out`;
  - `ProbeA/B.lean`, the E1 variants tried sealed.

The scratch worktrees `$SP/wt-rev-dlc` and `$SP/wt-rev-dlc-int` and the olean copies
`$SP/rev-dlc-oleans` and `$SP/rev-dlc-int-oleans` were removed after the runs. To replay,
recreate them from `$SP/fill-rsa-oleans` and follow `base-restore.log`. The exchange checkout
`$SP/wt-exchange` was only fetched; its branch did not move.
