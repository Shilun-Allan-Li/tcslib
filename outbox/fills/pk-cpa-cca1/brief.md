# Claude fill · private-key CPA and CCA1 from a PRF (`prfFixedScheme_cpa`, `prfFixedScheme_cca1`)

**Issue base** `8c3afbff69ad1273446750f47c05d424ab13ebe2` on `cryptography/pass-shelat-ch2-4` (after #292).
**Unit** `pk-cpa-cca1`. **Worker** Claude (standing ruling, 2026-11-11). **Lean** 4.25.0 and the Mathlib revision
in that commit's `lake-manifest.json`.

Prove the two admitted theorems of [PS10, Theorem 168.2] in
`TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF.lean`. They say that if `F` is a pseudorandom function
family, the scheme of Algorithm 99.1 (`Enc_k(m) = ⟨r, m ⊕ f_k(r)⟩` with fresh `r`) is CPA-secure and CCA1-secure.
The statements passed Gate 04. The CCA2 counterexample `prfFixedScheme_not_cca2` in the same file is proved
(#289); keep it.

## Checkout and delivery

- Fetch `cryptography/pass-shelat-ch2-4` and start a local branch `fill/pk-cpa-cca1` at the exact issue base.
  Record the base in `REPORT.md`, and keep the proof branch local.
- Read `policy.md`, the attached environment addendum and `README.md`.
- Deliver every checkpoint and the final payload under `inbox/fills/pk-cpa-cca1/` on `exchange/pass-shelat-ch5-8`:
  - `REPORT.md`;
  - `patches/`, the whole `git format-patch` series from the issue base;
  - `src/`, the changed files;
  - `evidence/`.

  Commit as `fill pk-cpa-cca1: checkpoint N` and `fill pk-cpa-cca1: final`. Pull with rebase before pushing,
  push only your delivery path, and never force-push. Campaign changes land by a maintainer PR for Seyoon's
  approval.

## Targets (frozen; quoted from the issue base)

```lean
theorem prfFixedScheme_cpa (hF : PRF F) : (prfFixedScheme F E hE hFE).INDSecure .cpa := by
  sorry

theorem prfFixedScheme_cca1 (hF : PRF F) : (prfFixedScheme F E hE hFE).INDSecure .cca1 := by
  sorry
```

The section variables are `F`, an evaluator `E` with `hE : PolyTimeComputable E` and the agreement `hFE`. The game
is `FixedLengthScheme.indGame` (`PrivateKey/OracleSecurity.lean`). It has three oracles:
- `Enc` (index 0, fresh coins per query);
- `Dec` (index 1; under CPA always `⊥`; under CCA1 answered only before the challenge);
- `Challenge` (index 2, answered once, then repeated).

## Published interfaces

| Interface | Provider |
|---|---|
| `PRF`, `PRF.negligible_prfAdv`, `prfAdv_toOracleAdversary`, `OracleEnsemble.Indist`/`indist_iff`, `OracleEnsemble.keyed`/`random`, `acceptProb_random_eq(_lazy)`, `oracle_hybrid_lemma`, `NUPPT.toOracleAdversary(_eq/_boundedBy)`, `buildTree_*`, `decodeOracleMove_*` | `Pseudorandom/Functions/Asymptotic/Defs.lean` |
| Lazy random-function sampling (`evalLazy_*`, `uprob_evalLazy`, `lazyDist_apply`) | `Pseudorandom/Functions/LazySampling.lean` |
| `Games.exists_interactiveHandlerMachine` (T2), `Games.exists_toOracleAdversary_of_bitCodec` (T4), `exists_toCompOn_of_toComp` and the handler readers | `Games/Efficiency.lean` |
| `identical_until_bad`, `prob_eq_until_bad`, `prob_mem_le`, `abs_prob_sub_le_of_agree`, `simulate_allOutputs_bad` | `Games/Hopping.lean` |
| `indImpl_enc/_dec/_challenge_none/_challenge_repeat/_dec_cpa`, `decOpen_cpa/_cca1`, `encryptAt_eq`, `decAnswer_*`, `splitHalf_*`, `indCodec_*`, `indGame_eq`, `INDSecure_iff`, and the specification-typed readers from #289 (`indSpec_decDom/_decRng/_challengeDom/_challengeRng`, `indImpl_dec_onSpec`, `indImpl_challenge_none_onSpec`) | `PrivateKey/OracleSecurity.lean` |
| `prfScheme_gen/_enc/_dec`, `runAt_prfEnc`, `runAt_prfDec`, `decodeFin_runAt_prfDec_of_not_wf`, `polyTimeComputable_prfEncFun/_prfDecFun` | `PrivateKey/FromPRF.lean` |
| `prfFixedScheme_gen/_enc/_dec`, the private helpers of the not-CCA2 proof (reusable patterns) | `PrivateKey/OracleFromPRF.lean` (owned) |
| `Negligible.*`, `Negligible.polyExpr_mul`, probability readers, `simulate`/`OracleComp` laws, `NUPPT` run/coin/closure lemmas | `Foundations/Negligible.lean`, `Asymptotic/ReductionSupport.lean`, `Games/*`, `Complexity/Randomized/*` |
| The adaptive and CPA-pilot proofs (`PublicKey/AdaptiveCPA/`, `PublicKey/BitwiseCPA/`, `PublicKey/OracleSecurity/ChallengeSim`) | worked models of T2 handlers, eager coins and cast transport; reuse their public lemmas where their contracts apply |

## Authorized reader additions

In `TCSlib/Cryptography/Encryption/PrivateKey/OracleSecurity.lean`, beside the existing `_onSpec` readers and in
the same form, you may add:
- `indSpec_encDom`, `indSpec_encRng`;
- `indImpl_enc_onSpec`;
- `indImpl_challenge_repeat_onSpec`.

Each must be public, not `@[simp]`, and carry a docstring with its formula. Add only those you use, and change
nothing else in that file.

## Proof route and checkpoints

The docstring sketches give the route. The CCA1 proof extends the CPA proof.

1. **PRF → random function.** Build the reduction `D` as an oracle machine for `OracleEnsemble.Indist`.
   - Use T2 and the input-free companion, then T4, as the CPA sketch says. `D` answers the game's `Enc` and
     challenge queries by querying its own function oracle at a fresh `r`. For CCA1 it also answers decryption
     queries before the challenge (`runAt_prfDec`; `⊥` on malformed queries by
     `decodeFin_runAt_prfDec_of_not_wf`).
   - The challenge bit `b` goes in the seed, and the finalization compares the guess with `b`.
   - Show: the game with `f_k` equals `D` against the keyed ensemble, and the game with a random function equals
     `D` against the random ensemble.

   Send checkpoint 1.
2. **The random-function game.**
   - Define the bad event: the challenge's `r*` collides with the `r` of an earlier `Enc` answer, a later one,
     or (CCA1) a pre-challenge decryption query.
   - Bound its probability by `q(n)/2^n` with `prob_mem_le`: one fresh uniform draw against at most `q` others.
   - Off the bad event, `m_b ⊕ RF(r*)` is uniform for both `b` (lazy sampling, `identical_until_bad`).

   Send checkpoint 2.
3. **The bound.** `A`'s advantage is at most `2 · prfAdv + q(n)/2^n`, or the exact form you prove. Both terms are
   negligible: the first by `PRF.negligible_prfAdv` at the reduction's polynomial budget, the second by the
   `Negligible` API. Close both targets.

   Send the final delivery.

Check the edge cases: budget 0; `n = 0` (the advantage is trivially bounded, or the collision bound is ≥ 1); no
challenge; repeated challenges; `Dec` on the challenge or on malformed strings; and the timeout output.

## Scope and proof discipline

- **Owned file.** Own `OracleFromPRF.lean`: replace the two proof bodies and add helpers there.
- **Helper modules.** Generic helper modules are permitted under `TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF/`.
  The owned file imports them precisely, and its module docstring gets a `## Contents` list if it becomes a facade.
- **Size.** Keep every file below 1000 lines (the owned file is 579 now).
- **Frozen.** Do not edit any other file except the authorized readers. If a lemma belongs in an existing file,
  put it in your helper module and list it in `REPORT.md` as a promotion request.
- **Duplication.** Generic probability, simulation or list facts go on the promotion list (duplication ledger
  DL-30 to DL-33 in `briefs/pass-shelat-ch5-8/duplication-ledger.md`). Grep first and reuse existing lemmas; the
  four CPA-pilot fills left many candidates.
- **Statements.** You may edit the targets' sketches to describe the delivered proofs. Preserve the statements,
  every other declaration (including `prfFixedScheme_not_cca2` and `not_prfFixedScheme_cca2`), the statement
  prose and the global simp attributes. Update the module docstring's status lines for the two targets.
- **Docstrings.** Public helpers get docstrings with their formulas, and proof sketches when nontrivial
  (policy §3). Lemma docstrings must state the formula, not just "the defining equation of …".
- **Rule 10.** Use only published readers for other files' definitions, including generated matchers and
  projections.
- **Escalation.** If a target appears false, or a required reader is missing with no clean route, record the
  exact failing obligation and the smallest proposed correction in `REPORT.md`, then push a checkpoint.

## Checks and report

- **Bootstrap.** Bootstrap from `order.txt` and the narrow `roots.txt` per the addendum. Check one module per
  `scripts/lean_check_tree.sh` call, with one Lean process per olean tree. Insert helper modules before their
  consumers, and recalculate roots if imports change.
- **Sweep.** Recheck the owned modules, then sweep the supplied order. Compare `sorry` warnings with
  `base-sorries.txt`: the only change must be the removal of `prfFixedScheme_cpa` and `prfFixedScheme_cca1`.
- **Axioms.** Print the axioms of both targets. Expect only `propext`, `Classical.choice` and `Quot.sound`.
- **Rule 10 evidence.**
  - Run whole-file seals of every changed or new file over its full TCSlib import closure, with controls that
    pass unsealed and fail sealed.
  - Run the explicit-unfold scan.
- **Lint.** Run `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography/Encryption/PrivateKey --check8b`.
- **Report.** Give the base, both targets' status, the changed files and sketch edits, the new declarations, any
  promotion or reader requests, and the evidence.

**Ready to dispatch**
