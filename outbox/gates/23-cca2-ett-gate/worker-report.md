# Fill cca2-ett — final

**Unit** `cca2-ett` · **Worker** Claude · **Issue base** `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9`
(`cryptography/pass-shelat-ch2-4`, the merge of #299) · **Proof branch** `fill/cca2-ett` (local),
head `b66a81a1a` · **Lean** 4.25.0, Mathlib at the base's manifest.

**Target status: proved.** `Composability.ccaScheme_cca2` (PS10 Theorem 170.4) has a complete proof;
its statement is unchanged. `#print axioms ccaScheme_cca2`: `[propext, Classical.choice, Quot.sound]`.
The final sweep of the supplied order (with the ten helper modules inserted before the owned module)
has 0 errors, and the `sorry` census is `base-sorries.txt` minus `ccaScheme_cca2` (§5).

Commits on the proof branch (the patch series in `patches/`):
`9015e943d` checkpoint 1 (step 1), `9262d2ba6` checkpoint 2 (step 2), `3fc373bb6` step 3,
`af9fdc724` the combination, `731efd9ed` published readers only (seal fixes), docstrings, lint,
`c68fc02eb` the public width transport, `c5e21bc04` general one-entry log readers, `b66a81a1a`
`rCnt` read through its published reader (found by the explicit-unfold scan).

## 1. The proof

Fix a machine adversary `A`, a budget polynomial `q` and a bit `b`; `P_b = Pr[IND_b(A, q(n), n) = 1]`
for the CCA2 game of `π′`. Four steps, each an equality or a bound at every `n` (step 2 at `n > 0`):

1. **Tag key → random function** (checkpoint 1; `cca_tag_step`, from `ETTGame.exists_tagStep`):
   `|P_b − 𝔼_{k₁} 𝔼_R ettAcc(f_{k₁}, R, rej = false, b)| = prfAdv(F_{2n}, D_b^{q(2n)})` for a
   next-query machine `D_b` (T2 handler `dHandler` with `k₁` and nonce tapes in its seed, a budget
   cap, T4 at length `2n`, parameter halving; §7.2 below).
2. **Fresh decryption queries rejected** (checkpoint 2; `cca_rej_step`, from
   `ETTGame.abs_ettAcc_rej_sub_le`): for `n > 0`,
   `|𝔼_{k₁}𝔼_R ettAcc(…, rej = false, b) − 𝔼_{k₁}𝔼_R ettAcc(…, rej = true, b)| ≤ q(n) · 2^{-2n}`.
3. **The rejecting experiment is a CPA experiment of the §3.9 scheme** (new;
   `ETTGame.exists_cpaStep`): there is one machine `B` (independent of `b`) with, for every `b`,
   `n` and pad function `f`,
   `𝔼_R ettAcc(f, R, rej = true, b, A, q(n)) = 𝔼_{r_B} 𝔼[⟦B's output⟧₀ = 1 | simulate (PRFGame.fImpl … (atkOf false) b f) (B.toComp … (qRed q)(n) r_B) none]`.
   - *Lazy tags* (`Lazy.lean`, `expect_ettImpl_lazy`): averaged over `R`, the rejecting experiment
     is the experiment whose state is the challenge record and the table of `Enc′` answers
     `(r ‖ c₁, tag, m)`, newest first; a pair gets the table's tag, else the challenge's, else a
     fresh tape (`tagOf`); `Dec′` refuses the record and answers a well-formed word from the table
     (`lazyDec`). Proof: induction with `R` overridden by the table's tags (`ovr`, `tagTbl`); a new
     pair moves `R`'s value into the table (`expect_sample_ovr`); decryption answers agree because
     the entry's pair is `r ‖ (m ⊕ f(r))` with an `n`-bit `m` (`LInv`, `decAnsW_tagTbl`).
     With tapes in advance: `expect_ettLazyTape` (generic `expect_simulate_tapeImpl`).
   - *The handler* (`CPAHandler.lean`, `bHandler`): a `Games.InteractiveHandler` from the CCA2
     oracles (`ettDin`, `ettDout`) to the CPA oracles of the §3.9 scheme (`PRFGame.pkDin`,
     `pkDout`). Seed: `q(n)` tag tapes of `2n` bits. State: the table word (`GGMRed.tblEnc` of the
     entries, read with GGM's public `GGMRed.lookup`/`lookup_tblOf`, `lookup_tblW`), `1^j`, the
     record. `Enc′` asks the CPA encryption oracle, tags `⟨r, c₁⟩` as `tagOf` does with tape `j`,
     adds the entry; `Dec′` answers `lazyDec` with no outer query; a first challenge asks the CPA
     challenge oracle, tags and records; a repeated one repeats the record. Every word read from an
     outer answer is padded to its length (`EnsembleLemmas.padL`), so the round function is total
     and polynomial-time (`polyTimeComputable_bRun`), for every outer answer. Answer lemmas:
     `bHandler_impl_enc`, `_dec`, `_challenge_some`, `_challenge_none`.
   - *The reduction* (`CPAReduction.lean`): each call of the handler composed with
     `PRFGame.fImpl` has, from `bAbs ((o, L), j)` (handler state `bState j L o`, CPA record
     `o.map cpaRec`), the law of the call of `ettLazyTape` from `((o, L), j)` (`comp_bAbs`), under
     the invariant `bInv` (`|L| ≤ j`, `n`-bit messages; kept by `ettLazyTape_bInv`) and `j < q(n)`;
     `expect_simulate_abs_inv` (generic, `Tools.lean`) lifts this to whole runs of the adversary
     (at most `q(n)` queries). T2 (`exists_interactiveHandlerMachine`) for `bHandler`, the
     input-free companion of `A`, and `NUPPT.exists_comp` (pre `⟨[], ·⟩`) give `B` with budget
     `qRed q` (`= q·1 + 0`).
4. **The CPA experiment hides the bit** (owned file, `ccaScheme_cca2`): `PRFGame.exists_prfReduction B (qRed q) false b`
   gives `C_b` with `prfAdv(F_n, C_b^{qRed(qRed q)}) = |𝔼_k K_b(f_k) − 𝔼_R K_b(R)|`
   (`ETTGame.prfAdv_eq_expect`), and `PRFGame.abs_expect_fImpl_sub_le` (CPA: `decOpen_atkOf`;
   `ctP = 3n + 2`; `2n`-bit challenge queries) gives `|𝔼_R K_0(R) − 𝔼_R K_1(R)| ≤ Q(n)²/2ⁿ`,
   `Q = qRed q`.

**Combination.** For `n > 0`:
`|P₀ − P₁| ≤ adv(D₀) + adv(D₁) + 2 q(n)/2^{2n} + adv(C₀) + adv(C₁) + Q(n)²/2ⁿ` (linear arithmetic on
the two-sided forms of the seven facts). The witness is that sum plus `if n = 0 then 1 else 0`
(at `n = 0` the advantage is at most `1`, `advantage_le_one`; the other terms are nonnegative,
`prfAdv_nonneg`). Negligibility: `PRF.negligible_prfAdv` for `D_b` at budget `q` composed with
`n ↦ 2n` (`Negligible.comp_of_le`) and for `C_b` at budget `qRed (qRed q)`;
`2 q(n) 2^{-2n} ≤ 2 · q(n) (1/2)ⁿ` (`EnsembleLemmas.negligible_polyExpr_mul`,
`negligible_two_pow_neg`, `Negligible.const_mul`, `Negligible.mono`); `Q(n)²/2ⁿ = (Q·Q)(n) (1/2)ⁿ`;
the `n = 0` correction is eventually `0` (`negligible_zero.mono`); `Negligible.add`.

**Deviation from the route (documented; no statement changed).** The brief's step 3 cites
`prfFixedScheme_cpa` and, for the tags, `lazyImpl`. The proof uses instead PRFGame's public API
directly: the CPA adversary `B` is built against the oracles `PRFGame.fImpl` (the brief's "CPA
oracles"), and the CPA bound for `B` is assembled from `PRFGame.exists_prfReduction`,
`PRFGame.abs_expect_fImpl_sub_le` and `ETTGame.prfAdv_eq_expect`. Going through
`prfFixedScheme_cpa` would have required turning `B` into an adversary of the IND game of
`prfFixedScheme`, i.e. re-deriving the private readers of `OracleFromPRF.lean`
(`accept_prf_indGame`, `ofFn_prf_encryptAt`, …). `PRFGame.lazyImpl` is the §3.9 experiment's lazy
pad function (`n`-bit points, the §3.9 record); the tags need `2n`-bit points with the CCA2 table
and record, hence the ETT-specific `Lazy.lean` (on the generic `ovr`/`expect_sample_ovr` of
`Tools.lean`). Lazily sampled tags agree with `RF` on repeated pairs, so no tag-collision term
appears; the only collision term is PRFGame's `Q²/2ⁿ` (nonce collisions of the §3.9 scheme).

**Edge cases.**
- `n = 0`: steps 1, 3, 4 hold at every `n`; step 2 needs `n > 0`, and the witness adds `1` at
  `n = 0`. The transfer (step 1) matches every decryption answer, including the malformed four-bit
  words that decrypt at `n = 0` (same total projections `wR`, `wC`, `wT` and guards `validW`).
- Budget 0, no challenge, repeated challenges: all equalities are by induction on the adversary's
  computation (a returned value is the base case); repeated challenges answer the record in every
  experiment (`ettStep_challenge_some`, `lazyStep_challenge_some`, `bHandler_impl_challenge_some`).
- `Dec′` on the challenge: refused (`refW`) in every experiment; on the challenge with a changed
  tag or another word with the challenge's pair: rejected as a fresh pair in the rejecting
  experiment, and (step 2) a valid such query is the challenge itself for `n > 0` (canonical
  parsing, `eq_ctW_of_wfW`); malformed and over-long words: `wfW` fails, `⊥`; an earlier `Enc′`
  answer: the table's message (`decAnsW_tagTbl`).
- Nonce collisions: two `Enc′` answers with the same pair `r ‖ c₁` read the same tag (the table is
  read first, `tagOf`), as with a random function; the CPA bound carries the §3.9 collision term.
- Codecs' timeout outputs: each step is an equality of whole simulations of `A.toComp (bitCodec …)`
  (or of the machines from T2/T4, whose `toCompOn` equalities hold for every answer), so the
  timeout outputs are the same on both sides; the handlers read every outer answer, of every
  value, through padding.

## 2. Changed and new files

| File | Lines | Role |
|---|---|---|
| `PrivateKey/EncryptThenTag.lean` (owned) | 739 | readers of `ccaScheme`; steps 1, 2 (private); the proof of `ccaScheme_cca2` |
| `EncryptThenTag/Tools.lean` | 293 | generic: simulation through an abstraction in law (`expect_simulate_abs`, `_inv`), coins in advance, `ovr` |
| `EncryptThenTag/Machines.lean` | 352 | budget cap, parameter halving, width transport |
| `EncryptThenTag/Games.lean` | 437 | the CCA2 experiment with pad `f` and tag `g` |
| `EncryptThenTag/Handler.lean` | 833 | T2 handler of the tag-key PRF reduction |
| `EncryptThenTag/Reduction.lean` | 386 | step 1 |
| `EncryptThenTag/Transfer.lean` | 218 | the CCA2 game of a scheme as the experiment with `f`, `g` |
| `EncryptThenTag/Forgery.lean` | 528 | step 2 |
| `EncryptThenTag/Lazy.lean` | 585 | step 3: the experiment with lazily sampled tags |
| `EncryptThenTag/CPAHandler.lean` | 757 | step 3: the T2 handler of the CPA reduction |
| `EncryptThenTag/CPAReduction.lean` | 354 | step 3: the CPA reduction |

All below 1000 lines. Import graph (acyclic; the sweep checks it in order): Tools ← Machines;
Tools ← Games ← Handler ← Reduction (← Machines, ← `OracleFromPRF.Reduction`); Games ← Transfer;
Games ← Forgery; Games ← Lazy ← CPAHandler (← Handler, ← `OracleFromPRF.Handler`) ← CPAReduction
(← Reduction). The owned file imports all ten helpers (the lint's facade rule) and
`OracleFromPRF.Collision` (for `PRFGame.abs_expect_fImpl_sub_le`). No helper imports the owned
file; `OracleFromPRF` and its helpers do not import `EncryptThenTag`.

**Owned-file edits.** Title (dropped "(statement phase)"); `## Main results` (the theorem is
proved); new `## Contents` (the helper modules and what each provides); imports; the target's
docstring sketch rewritten to describe the delivered proof (four steps, the combination, the
`n = 0` correction, and the deviation above); the target's body. The statement, every other
declaration, the source notes and the `simps` attribute are unchanged.

## 3. New declarations

(All helpers in namespace `TCSlib.Cryptography.Composability.ETTGame`.) Checkpoint 1 and 2
declarations are listed in §7.4. New since checkpoint 2:
- Tools: `expect_simulate_abs_inv`.
- Games: `encW_eq_ctW` (replaces Forgery's private `encW_pairV`, now deleted).
- Lazy: public `LEntry`, `LEntry_eq`, `LSt`, `LSt_eq`, `keysL`, `keysL_eq`, `lookL`, `lookL_eq`, `tagOf`, `tagOf_eq`, `lazyDec`, `lazyDec_eq`, `tagTbl`, `tagTbl_eq`, `keysL_nil`, `tagTbl_none_nil`, `ovr_append`, `getD_idxOf_fst`, `ovr_tags_of_mem`, `keys_tagTbl`, `tagOf_eq_ovr`, `zipWith_xor_cancel`, `LInv`, `lInv_iff`, `lInv_nil`, `decAnsW_tagTbl`, `lazyStep`, `lazyStep_enc`, `lazyStep_dec`, `lazyStep_challenge_some`, `lazyStep_challenge_none`, `ettLazyK`, `ettLazyK_eq`, `ettLazy`, `ettLazy_eq`, `ettLazyTape`, `ettLazyTape_eq`, `expect_ettLazyTape`, `ettLazy_apply`, `expect_ettImpl_lazy`; private `tagTbl_cons`, `keysL_cons`, `ovr_cons_self`, `ovr_append_of_mem`, `ovr_append_of_not_mem`.
- CPAHandler: public `encE`, `encE_eq`, `tblW`, `tblW_eq`, `tblW_nil`, `tblW_cons`, `length_tblW`, `lookup_tblW`, `bStLen`, `bStLen_eval`, `bSeedLen`, `bSeedLen_eval`, `bState`, `bState_eq`, `bSeed`, `bSeed_eq`, `ofFn_bSeed`, `bTapeOf`, `bTapeOf_eq`, `bHandler`, `bHState`, `bHState_eq`, `ofFn_bHState`, `bHSeed`, `bHSeed_eq`, `ofFn_bHSeed`, `bHandler_init_hstate`, `bHandler_advInput`, `bHandler_finish`, `bKeyOf`, `bKeyOf_eq`, `bHandler_impl_enc`, `bHandler_impl_dec`, `bHandler_impl_challenge_some`, `bHandler_impl_challenge_none`; private `map_encE_eq_tblOf`, `fields_bState`, `bTbl`, `bJ`, `bFlag`, `bRec`, `bPad2`, `bTape`, `bKey`, `bLook`, `bChalKey`, `bChalTag`, `bTag`, `bCt`, `bNew`, `bDKey`, `bWF`, `bRef`, `bDecL`, `bDecAns`, `bRun`, `polyTimeComputable_bRun`, `bFin`, `polyTimeComputable_bFin`, `fields_input`, `rAns_one`, `log_ne_nil`, `bPad2_fields`, `bNew_fields`, `bTag_fields`, `bDecL_fields`, `recBits_fields`, `ofFn_padFin_msg`.
- CPAReduction: public `cpaRec`, `cpaRec_eq`, `bAbs`, `bAbs_eq`, `bInv`, `bInv_iff`, `bTapes`, `bTapes_eq`, `bTapes_of_lt`, `comp_bAbs`, `ettLazyTape_bInv`, `exists_cpaStep`; private `ofFn_ctOf`, `bKeyOf_ctOf`.
- Owned file: no new declaration since checkpoint 2 (the proof of `ccaScheme_cca2`).
- Handler: `rY_one`, `log_ne_nil` (private) generalized to any oracle-index word.

No `@[simp]` added. New public `abbrev`s: `LEntry`, `LSt` (with `LEntry_eq`, `LSt_eq`); earlier
`St`, `tagOut` (`St_eq`, `tagOut_eq`). Every public `def` has a lemma beside it (lint
check 8: no WARN for the new files).

## 4. Promotion requests, reader requests, PRFGame overlap

**Promotion list** (generic facts in the helpers; searches in `evidence/logs/checkpoint1-searches.log`
and `evidence/logs/final-searches.log`):
- Checkpoints 1–2 (unchanged): `expect_simulate_abs`; `freshImpl`, `tapeImpl`,
  `expect_simulate_tapeImpl`; `ovr`, `expect_sample_ovr`; `logCount`, `length_logCount_encodeLog`,
  `buildComp_cap`, `exists_capMachine`; `exists_halfMachine`; `eval_toOracleAdversary_len`;
  Forgery's private `abs_expect_sub_le_expect`.
- `expect_simulate_abs_inv` (Tools): `expect_simulate_abs` with an invariant kept by the calls
  (`Games.simulate_eq_of_abs_bounded` is the deterministic version, without invariant).
- `zipWith_xor_cancel` (Lazy): `(m ⊕ p) ⊕ p = m` for `|m| ≤ |p|`. Private copies:
  `zipWith_xor_xor_self` in `FromPRF.lean`, `FromPRG.lean`, `SecureComputation/SpecialEncryption.lean`
  and the owned file's `zipWith_xor_xor_self'` (base); the public
  `Foundations/BitLists.zipWith_xor_cancel_left` is the other orientation, `(a ⊕ c) ⊕ a = c` with
  `|a| = |c|`.
- `ovr_append` (Lazy): writing a concatenated table.

**Reader requests:** none (every foreign definition is read through a published lemma; see the
seals and the explicit-unfold scan, §5).

**PRFGame overlap** (private lemmas of `OracleFromPRF/` re-derived from published readers, in the
general form):
- `prfAdv_prfReduction` (private, `OracleFromPRF.lean`) → `ETTGame.prfAdv_eq_expect` (checkpoint 1):
  the PRF advantage of any oracle adversary as the gap of two expectations.
- `prf_advantage_le` (private, `OracleFromPRF.lean`): the CPA bound for an adversary of the §3.9
  scheme. Re-derived inline in `ccaScheme_cca2` for the machine `B` against the oracles `fImpl`
  (step 4), from `PRFGame.exists_prfReduction`, `ETTGame.prfAdv_eq_expect` and
  `PRFGame.abs_expect_fImpl_sub_le`.
- `rY_one`, `log_ne_nil` (private, `OracleFromPRF/Handler.lean`): the outer answer of a one-entry
  log and its non-emptiness. Re-derived as private lemmas of `Handler.lean` (`rY_one`,
  `log_ne_nil`) and `CPAHandler.lean` (`rAns_one`, `log_ne_nil`), for any oracle-index word `u`
  (PRFGame's are for `u = []`), from `InteractiveHandler.rAns_eq`, `pairFstD_pairEncode`,
  `pairSndD_pairEncode`, `pairEncode_ne_nil`.
- The handler-reading pattern of `OracleFromPRF/Handler.lean` (`fields_input`, `rNew_fields`,
  `recBits_fields`, private) recurs in `Handler.lean` and `CPAHandler.lean` (`fields_input`,
  `bNew_fields`, `recBits_fields`, …) for these files' own handlers and state encodings; the
  statements are about different definitions (not copies).

## 5. Checks (final)

All runs one Lean process at a time, each module through `scripts/lean_check_tree.sh` (via
`tools/check.sh`: start/end time, elapsed time and max RSS in the log). The post-sweep runs are
driven by `tools/final_pipeline.sh` (its step log: `logs/final-pipeline.log`).

- **Recheck and sweep** (`logs/final-sweep.log`, 06:31–06:52 UTC): the 274 modules of
  `logs/order-with-helpers.txt` (the 264 of `order.txt` with the ten helpers inserted before the
  owned module; otherwise identical to `order.txt`), each checked from scratch (stale olean
  removed first), in order: **274/274 status 0, no `error:` line**; the eleven files of this fill
  emit no warning at all. This is one uninterrupted run from the first module. Earlier final-sweep
  runs were stopped by me twice in the first 20 modules to make source changes (commits
  `c68fc02eb`, `c5e21bc04`), and one complete run (06:08, 274/274 status 0) was superseded by the
  `rCnt` fix (`b66a81a1a`, see the scan below); their logs were discarded, as noted in
  `logs/final-pipeline.log`. No restart of the host happened during the delivered runs.
- **Sorry census** (`logs/final-census.txt`, `logs/final-census-vs-base.diff`): 23 declarations in
  9 modules; the diff against `base-sorries.txt` is exactly the line
  `TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag: 1: ccaScheme_cca2` and the total
  (24 → 23).
- **Axioms** (`logs/final-axioms.log`, probe `probes/AxiomsFinal.lean`):
  `ccaScheme_cca2` depends on `[propext, Classical.choice, Quot.sound]`. The probe prints the axioms
  of every stored constant of the eleven files (all constants of the environment whose module is
  one of them, auxiliary constants included): **551 constants**, the union of their axioms is
  `{Classical.choice, Quot.sound, propext}`; no `sorryAx`. (The probe's first run failed on a
  syntax error of the probe itself, a shadowed mutable variable; it was fixed and rerun.)
- **Whole-file seals** (`seals/`; generator `tools/seal_gen.py`, runner `tools/seal_run.py`,
  `tools/seal_all.sh`). Each file is copied verbatim to a new module whose header makes every
  TCSlib definition of its whole import closure `irreducible` and removes it from instance
  unfolding (abbreviations excluded: structure projections, `casesOn`, `bitSpec`-style notation);
  the copy must elaborate. Variant **A** excludes `Complexity.PolyExpr.eval` as notation; variant
  **B** seals it too. Results (rows in `final-A.jsonl`, `final-B.jsonl`, `base-A.jsonl`,
  `base-B.jsonl`; raw output in the `.out` files; sealed copies in `seals/sources/`; each row
  carries the sha256 of the checked source and of the copy, which match the delivered `src/` and
  `seals/sources/` files):
  - final, A and B: **all eleven files elaborate sealed (0 errors, 0 failing declarations)**;
    about 1,500–1,640 definitions sealed per file (the counts are in each row);
  - base (the owned file is the only changed file that exists at the base; checked from
    `base/EncryptThenTagBase.lean`, sha256 equal to `SOURCE-SHA256SUMS`), A and B: 0 errors;
  - `seals/seals-compare.log`: no declaration fails at the final, so none is new.
  During development the first seal runs (variant A; not delivered) failed at eighteen places in
  seven files: `rfl` or `cases … <;> rfl` through `recBits`, `refW`, `keysL`, `LInv`,
  `padL`/`ettDout`, `InteractiveHandler.advInput`, `pairSndD`, an `intro` through `INDSecure`, and one
  `rw … at` whose result typechecked only by unfolding `pairW`. All were replaced by published
  readers (`recBits_none/some`, `refW_none/some`, the new `keysL_nil`, `lInv_nil` and
  `tagTbl_none_nil`, `EnsembleLemmas.ofFn_padFin_eq_padL`, `ettDout_zero/one/two`,
  `InteractiveHandler.advInput_eq`, `BinArith.iterate_pairSndD_nil`,
  `FixedLengthScheme.INDSecure_iff`, `pairW_eq`) in `731efd9ed`; the delivered runs above are on the
  final sources.
- **Paired controls** (`controls/`, `logs/controls-plain.log`, `seals/controls-A.jsonl`,
  `seals/controls-B.jsonl`):
  - `CtlUnfold` (`ETTGame.wR w = pairFstD w := rfl`, unfolding a helper's `def`): unsealed status 0;
    sealed A **1 error** (`ctl_unfold_wR`), sealed B **1 error**;
  - `CtlEval` (`(PolyExpr.const 1).eval 5 = 1 := rfl`): unsealed 0; sealed A 0 (eval excluded);
    sealed B **1 error** (`ctl_unfold_eval`);
  - `CtlReader` (the same two facts through `ETTGame.wR_eq`, `PolyExpr.eval_const`): unsealed 0,
    sealed A 0, sealed B 0.
  Each sealed negative fails exactly once, and the positive passes. (A first run of the controls
  was void: `pairFstD` was written unqualified and did not elaborate even unsealed; the sources
  were fixed and the controls rerun; the void logs were discarded.)
- **Explicit-unfold scan** (`scan/`; `tools/rwids.py`, `tools/rwids_run.sh`, `tools/cmp_scans.py`):
  every identifier in a `rw`/`rwa`/`nth_rw`/`simp`/`simp only`/`simpa`/`simp_rw`/`dsimp`/`unfold`/
  `delta` list of each file is resolved in the file's namespaces and `open`s by a scan module
  (`scan/sources/`), and classified. Final: 1,042 rows: 758 theorems, 13 definitions of the scanned
  file itself, 1 core simproc (`reduceIte`), 270 unresolved (local hypotheses, private
  declarations of the scanned file, projections of hypotheses, dot-notation theorem uses; listed in
  `scan/scan-unresolved.txt`), and **0 definitions of another TCSlib file**
  (`scan/scan-compare.log`: "NEW foreign explicit unfolds: 0"). Base: 42 rows, 0 foreign. The
  scan of the first complete run found one (`rw [rCnt, …]` in `Handler.fields_input`, the
  `InteractiveHandler.rCnt` of `Games/Efficiency.lean`); it now reads `InteractiveHandler.rCnt_input`
  (`b66a81a1a`).
- **Lint** (`logs/final-lint.log`): `python3 -I scripts/campaign_style_lint.py
  TCSlib/Cryptography/Encryption/PrivateKey --check8b`: **0 FAIL**, 5 WARN, all in files this fill
  does not touch (the same five as at checkpoints 1 and 2); none for the eleven files (the owned
  file imports every helper, the facade rule).
- **Searches** for the generic facts of step 3: `logs/final-searches.log` (ripgrep).

## 6. Evidence (`evidence/`, manifest `evidence/SHA256SUMS`)

`evidence/SHA256SUMS` lists exactly the files under `evidence/` (118), each delivered.
- `logs/`: environment and bootstrap (`preflight.log`, `mathlib-roots.txt`, `cache-store.log`,
  `source-sha256.log`, `cache-get.log`, `packages-check.log`, `cache-probe.log`, `order.txt`,
  `bootstrap.log`, `resume-1.log`, `resume-2.log`, `census-bootstrap.txt`,
  `census-bootstrap-vs-base.diff`); checkpoints (`checkpoint1-*`, `checkpoint2-*`); final
  (`order-with-helpers.txt`, `final-sweep.log`, `final-census.txt`, `final-census-vs-base.diff`,
  `final-axioms.log`, `final-lint.log`, `final-searches.log`, `final-pipeline.log`,
  `controls-plain.log`, `scan-final.ids.log`, `scan-final.raw.log`, `scan-base.ids.log`,
  `scan-base.raw.log`).
- `seals/`: `final-A.jsonl`/`.out`, `final-B.jsonl`/`.out`, `base-A.jsonl`/`.out`,
  `base-B.jsonl`/`.out`, `controls-A.jsonl`/`.out`, `controls-B.jsonl`/`.out`, `seals-compare.log`,
  and `sources/{finalA,finalB,baseA,baseB,ctlA,ctlB}/` (the sealed copies that were checked).
- `scan/`: `scan-final.tsv`, `scan-base.tsv`, `scan-compare.log`, `scan-unresolved.txt`,
  `sources/{final,base}/` (the scan modules).
- `controls/`: `CtlUnfold.lean`, `CtlEval.lean`, `CtlReader.lean`.
- `base/`: `EncryptThenTagBase.lean` (the owned file at the base, for the base seals and scan).
- `probes/`: `CacheProbe.lean`, `AxiomsCP1.lean`, `AxiomsCP2.lean`, `AxiomsFinal.lean`.
- `tools/`: `check.sh`, `dev.sh`, `mk.py`, `sweep_chunk.sh`, `census.py`, `cmpcensus.sh`,
  `pkgcheck.py`, `payload.sh`, `seal_gen.py`, `seal_run.py`, `seal_all.sh`, `rwids.py`,
  `rwids_run.sh`, `cmp_scans.py`, `final_pipeline.sh`, `finalize.sh`.

`patches/`: `git format-patch eff2dcd0a..b66a81a1a` (8 patches). `src/`: the eleven changed and new
files at `b66a81a1a`.

## 7. From the checkpoints

### 7.1 Environment (addendum v1)

- **Preflight** (`evidence/logs/preflight.log`): 4 CPUs; cgroup v1 limit unlimited, so the headroom is
  `MemAvailable` = 16442974208 B = 15.31 GiB; clone filesystem ext4 with 13927960576 B = 12.97 GiB
  free (floor 12 GiB): `PREFLIGHT PASS`. Two worktrees of finished jobs of this session
  (`/workspace/dlc-base`, `/workspace/base-wt`) were removed before the preflight to get above the
  floor; no dependency tree was copied or moved.
- **Cache**: the narrowed `lake exe cache get` for the 98 roots of `roots.txt`
  (`evidence/logs/mathlib-roots.txt` is the same list) printed "No files to download" and
  "Decompressing 2370" and exited 0 (`cache-get.log`). The cache tool's store
  (`~/.cache/mathlib`, `cache-store.log`) already held 2402 archives, left by this session's earlier
  fills on this host; none was downloaded for this fill. No zero-size olean; the probe importing
  `Mathlib.Algebra.BigOperators.Field` elaborates (`cache-probe.log`, `probes/CacheProbe.lean`).
- **Packages** (`packages-check.log`, last line): `RESULT: all present packages match the manifest`
  (`doc-gen4`, `UnicodeBasic`, `BibtexQuery`, `MD4Lean` ABSENT; no module of the order imports them).
- **Bootstrap** (`bootstrap.log`, one module per `scripts/lean_check_tree.sh` call through
  `tools/check.sh`): 264/264 modules of `order.txt`, status 0. The host was restarted twice during
  the bootstrap (a VM restore: uptime 0, `dmesg` "virtual machine fork"); each restart terminated
  the background sweep mid-module (no Lean failure, no OOM event). Both are logged
  (`resume-1.log`, `resume-2.log`) and the sweep resumed at the interrupted module, which was
  re-checked from scratch. Sorry census of the bootstrap = `base-sorries.txt` (24 declarations in 10
  modules; `census-bootstrap.txt`, `census-bootstrap-vs-base.diff`).

### 7.2 Step 1 (checkpoint 1)

`ETTGame.exists_tagStep` (helper) and `cca_tag_step` (owned file): for a machine adversary `A` with
budget `q` and a bit `b` there is a next-query machine `D` with, at every `n`,

`|Pr[IND_b(A, q(n), n) = 1] − 𝔼_{k₁} 𝔼_R ettAcc(f_{k₁}, R, rej = false, b)| = prfAdv(F_{2n}, D^{q(2n)}_{2n})`,

where `R` ranges over all functions on `2n` bits. With `PRF.negligible_prfAdv` and
`Negligible.comp_of_le` (`φ n = 2n`) this is negligible in `n`; the final combination does that.

**The reduction** (`ETTGame.exists_tagReduction`): the handler `dHandler` holds `k₁` and `q(2n)`
nonce tapes in its seed and the query count and the challenge record in its state; `Enc′` and a
first challenge ask the oracle at `r ‖ c₁`, `Dec′` refuses the record, asks the oracle at the pair of
a well-formed word and compares with the tag. T2 is applied with the budget `q(2n)` to the
input-free companion of a **capped** adversary, then T4 at length `2n`, then the parameter is halved.

**Why the cap and the halving.** `PRF.negligible_prfAdv` bounds machines run at parameter `m` with
an `m`-bit oracle and budget `Q(m)` for a polynomial `Q`. The handler runs the adversary at `n` with
a `2n`-bit oracle. So the distinguisher at `m = 2n` must run T2's machine at `m / 2`
(`exists_halfMachine`, from `NUPPT.exists_reparam_advice`), and T2's budget must be a polynomial in
`2n`: `q(2n)`. The adversary's budget is `q(n)`; `exists_capMachine` gives a machine that, at every
budget `K ≥ q(n)`, computes what `A` computes with budget `q(n)` (after `q(n)` log entries a query
word becomes the empty word, which every bit codec reads as the timeout output). No statement is
weakened: the game is still `A` at budget `q(n)`.

**Transfer** (`ETTGame.accept_indGame_eq`, `accept_cca_indGame`): the real oracles have, call by
call, the laws of `ettImpl (F n k₁) (F (2n) k₂) false b`, through the record
(`expect_simulate_abs`). The readers of `ccaScheme` used: `ccaScheme_gen/enc/dec/ctLen`,
`runAt_ccaGen`, `runAt_ccaEnc`, `ccaDecFun_eq`, `ccaDecOK_eq` and the `NUPPT` run readers. Every
decryption answer is matched, including malformed words and, at `n = 0`, the malformed four-bit
words that decrypt to the empty message: the experiment parses with the same total projections
(`wR`, `wC`, `wT`) and guards (`validW`).

### 7.3 Step 2 (checkpoint 2)

New helper `EncryptThenTag/Forgery.lean` (536 lines) and, in the owned file, `cca_rej_step`: for
`n > 0`, a machine adversary `A` with budget `Q` and a bit `b`,

`|𝔼_{k₁} 𝔼_R ettAcc(f_{k₁}, R, rej = false, b) − 𝔼_{k₁} 𝔼_R ettAcc(f_{k₁}, R, rej = true, b)| ≤ Q / 2^{2n}`

(`ETTGame.abs_ettAcc_rej_sub_le`, averaged over `k₁`). The route of the brief: couple both
experiments with the same tapes and random function; they agree until the first fresh valid query.
- *Identical until bad* (`ettBad_agree`, `ettBad_stick`, `simulate_ettBad_fst`,
  `abs_prob_ettImpl_rej_sub_le`): `identical_until_bad` with the flag `hitW` (a decryption query
  that is not refused, is valid and whose pair is not the pair of an earlier `Enc′` answer), and
  `prob_eq_until_bad` to read the flag's probability in the rejecting experiment.
- *The flag's probability* (`expect_prob_bad_le`, an equal-until-bad argument through the union
  bound rather than `prob_bad_le`, because the per-query bound needs the average over `R`): by
  induction over the computation with `R` overridden on the revealed pairs (`ovr`, invariant
  `RevInv`). A new pair moves `R`'s value into the table (`expect_sample_ovr`); the rejecting
  experiment's decryption answers read the tag function only at listed pairs, so they do not
  depend on `R`; a fresh guess hits the unrevealed value with probability at most `2^{-2n}`
  (`expect_hitW_le`), "even if the pair was queried before" (each guess is bounded separately; no
  conditional probability after failed guesses is used). A valid query with the challenge's pair
  is the challenge itself for `n > 0` (`eq_of_pairV_eq`, `eq_ctW_of_wfW`: canonical parsing through
  `pairEncode` and the two length guards) and is refused, so it is not a hit.
- The bound is `Q / 2^{2n}`, the brief's `q(n) / 2^{2n}`.

New public declarations (Forgery): `ettBad_agree`, `ettBad_stick`, `simulate_ettBad_fst`,
`abs_prob_ettImpl_rej_sub_le`, `RevInv`, `revInv_iff`, `revInv_nil`, `expect_prob_bad_le`,
`abs_ettAcc_rej_sub_le`; private: `revInv_enc_old`, `revInv_enc_new`, `revInv_chal_old`,
`revInv_chal_new`, `validW_pairW`, `encW_pairV`, `expect_hitW_le`, `prob_bad_of_flag`,
`prob_simulate_ettBad_query`, `abs_expect_sub_le_expect` (generic: candidate for promotion,
`|𝔼 f − 𝔼 g| ≤ 𝔼 h` under a pointwise bound; `ProbComp.abs_expect_sub_le` has a constant bound).
Owned file: `cca_rej_step` (private).

Evidence added: `logs/checkpoint2-checks.log` (fresh checks of the seven helpers and the owned
module, status 0), `checkpoint2-census.txt`, `checkpoint2-axioms.log` (`propext`,
`Classical.choice`, `Quot.sound`), `checkpoint2-lint.log` (0 FAIL), `probes/AxiomsCP2.lean`;
`order-with-helpers.txt` now lists Forgery before the owned module.

### 7.4 Declarations of checkpoints 1 and 2

- Tools: `expect_simulate_abs`, `freshImpl`, `freshImpl_apply`, `tapeImpl`, `tapeImpl_apply`,
  `simulate_tapeImpl_congr`, `expect_simulate_tapeImpl`, `ovr`, `ovr_nil`, `ovr_cons`,
  `ovr_of_not_mem`, `ovr_of_mem`, `ovr_update`, `expect_sample_ovr`.
- Machines: `logCount`, `logCount_eq`, `polyTimeComputable_logCount`, `length_logCount_encodeLog`,
  `buildComp_cap`, `capRaw`, `capRaw_eq`, `polyTimeComputable_capRaw`, `exists_capMachine`,
  `exists_halfMachine`, `eval_toOracleAdversary_len`.
- Games: `pairV`, `tagL`, `ctW`, `maskL`, `encW`, `wR`, `wC`, `wT`, `wfW`, `validW`, `decL`, `pairW`
  (each with its `_eq`), `wR_ctW`, `wC_ctW`, `wT_ctW`, `length_maskL`, `length_encW`, `eq_ctW_of_wfW`,
  `wfW_encW`, `eq_of_pairV_eq`, `St` (abbrev, `St_eq`), `refW` (`refW_none`, `refW_some`),
  `decAnsW`, `hitW` (with `_eq`), `decAnsW_agree`, `ettStep` (`ettStep_enc`, `_dec`,
  `_challenge_some`, `_challenge_none`), `ettImpl` (`ettImpl_apply`, `ettImpl_eq_freshImpl`),
  `hitQ` (`hitQ_zero/one/two`), `ettBad` (`ettBad_apply`), `ettTape` (`ettTape_apply`),
  `expect_ettTape`, `expect_ettImpl_transport`, `ettAcc` (`ettAcc_eq`, `ettAcc_nonneg`,
  `ettAcc_le_one`).
- Handler: `ettCt`, `ettDin`, `ettDout`, `tagLen`, `tagOut` (abbrev, `tagOut_eq`), `dStLen`,
  `dSeedLen`, `recBits`, `dState`, `dSeed`, `dTape`, `dHandler` (simps fields), `dHState`, `dHSeed`
  (each with `_eq`/readers), `ofFn_dSeed`, `ofFn_dHSeed`, `ofFn_dHState`, `dHandler_init_hstate`,
  `dHandler_advInput`, `dHandler_finish`, `dHandler_impl_enc`, `dHandler_impl_dec_ref`,
  `dHandler_impl_dec_wf`, `dHandler_impl_dec_nwf`, `dHandler_impl_challenge_some`,
  `dHandler_impl_challenge_none`.
- Reduction: `gOuter` (`gOuter_apply`), `dAbs` (`dAbs_eq`), `dTapes` (`dTapes_eq`, `dTapes_of_lt`),
  `comp_dAbs`, `eval_subst_tagLen`, `expect_ettImpl_outLen`, `exists_tagReduction`,
  `prfAdv_eq_expect`, `exists_tagStep`.
- Transfer: `stRec` (`stRec_eq`), `expect_indImpl_ettImpl`, `accept_indGame_eq`.
- Owned file (all `private`): `cca_ctLen_eval`, `cca_inLens`, `cca_outLens`, `cca_gen_coins`,
  `cca_enc_coins`, `cca_gen_len`, `ccaKeyEq`, `ofFn_ccaKeyEq`, `cca_gen_runAt`, `ccaNonceEq`,
  `ofFn_ccaNonceEq`, `ofFn_cca_encryptAt`, `ofFn_cca_decAnswer`, `accept_cca_indGame`,
  `cca_tag_step`.

No `@[simp]` was added. The one new public `abbrev`s (`St`, `tagOut`) have `St_eq`, `tagOut_eq`.
