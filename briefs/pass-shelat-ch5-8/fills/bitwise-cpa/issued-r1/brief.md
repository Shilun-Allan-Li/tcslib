# Claude fill · padded bitwise CPA (`bitwise_padded_cpa`)

**Issue base** `4a9b2c91eb2f89c4fb624339d5b4ba9cfd35ac27` on `cryptography/pass-shelat-ch2-4`
(the merges of #287 and #288). **Unit** `bitwise-cpa`. **Worker** Claude. **Lean** 4.25.0 and the
Mathlib revision in that commit's `lake-manifest.json`.

Prove the admitted theorem `BitPublicKeyScheme.SingleBitSecure.bitwise_padded_cpa` in
`TCSlib/Cryptography/Encryption/PublicKey/BitwiseCPA.lean`. It says: if a single-bit public-key
scheme is secure, the padded bitwise scheme with `n`-bit messages is CPA-secure in the game of
[PS10, Definition 171.5], where the adversary chooses its messages after seeing the public key
[PS10, the bitwise scheme and hybrid argument of p. 103]. The statement passed Gate 12. With the
parallel `adaptive-cpa` fill it completes `SingleBitSecure.exists_adaptive_cpa`, which is already
proved from the two targets. The `adaptive-cpa` fill does not touch this file, and this fill does
not touch `AdaptiveCPA.lean`.

## Checkout and delivery

- Fetch `cryptography/pass-shelat-ch2-4` and start a local branch `fill/bitwise-cpa` at the exact
  issue base above. Record the base in `REPORT.md`. Keep the local branch at that ancestry.
- Read `policy.md`, the attached environment addendum and `README.md`.
- Deliver every checkpoint and the final payload under `inbox/fills/bitwise-cpa/` on
  `exchange/pass-shelat-ch5-8`:
  - `REPORT.md`;
  - `patches/`: the whole `git format-patch` series from the issue base;
  - `src/`: the owned paths;
  - `evidence/`.

  Use the commit messages `fill bitwise-cpa: checkpoint N` and `fill bitwise-cpa: final`. Pull with
  rebase before pushing, push only your delivery path, and never force-push. Keep the proof branch
  local. Campaign changes land by a maintainer PR for Seyoon's approval.

## Target

The statement is frozen. This quote comes from the issue base.

```lean
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.bitwise_padded_cpa
    {S : BitPublicKeyScheme} (h : S.SingleBitSecure) (L : PolyExpr)
    (hL : ∀ n (rg : S.bitwise.gen.Coins n) (m : Fin n → Bool) (re : S.bitwise.enc.Coins n),
      2 * (S.bitwise.enc.runAt n (pairEncode (pairFstD (S.bitwise.gen.runAt n [] rg))
        (List.ofFn m)) re).length + 2 ≤ L.eval n)
    (hmsg : ∀ n, n ≤ L.eval n) : (S.bitwise.padded L hL hmsg).INDSecure .cpa := by
  sorry
```

## The worked precedent

`BitPublicKeyScheme.SingleBitSecure.padded_cpa` (`PublicKey/OracleSecurity.lean`, landed in #288,
Gate 13 CLEAR) proves the one-bit case of this argument. Its proof shows an exact identity:
`advantage = distAdv` for a distinguisher built by T1. It uses three steps:
- eager challenge coins (`expect_simulate_indImpl_cpa`);
- first-challenge congruence (`ChallengeSim.chRun_congr`);
- a recording handler (`RecordHandler.recHandler`).

This fill reuses that pattern with a hybrid over the `n` message bits. Study it first.
`ChallengeSim` and `RecordHandler` are public. Reuse them where their contracts apply. Where they
do not (`RecordHandler` records 2-bit challenges), write a new handler in your helper module.

## Published interfaces

| Interface | Provider |
|---|---|
| `bitwise_gen`, `bitwise_enc`, `bitwise_dec`, `bitwise_enc_runAt`, `bitwise_enc_runAtL`, `bitwiseEncCoins`, `bitwiseEncCoins_ofFn`, `bitwise_enc_coinLen`, `singleBitSecure_iff`, `pkEncDist_eq` | `PublicKey/EnsembleSecurity.lean` |
| `PublicKeyScheme.padded_msgLen/_ctLen/_gen/_enc/_dec`, `padCt_eq`, `length_padCt`, `pairFstD_padCt`, `padEnc_coins`, `runAt_padEnc`, `padEncFun_eq`, `indImpl_*` (incl. `_onSpec`), `indSpec_*`, `inLens_*`, `outLens_*`, `indCodec_*`, `indGame_eq`, `INDSecure_iff`; the `padded_cpa` proof's private helpers are a model, not an interface | `PublicKey/OracleSecurity.lean` |
| `ChallengeSim.*`, `RecordHandler.*` | `PublicKey/OracleSecurity/` |
| `Games.exists_handlerMachine` (T1) and the `PolyHandler` readers | `Games/Efficiency.lean` |
| `Games.exists_advantage_hybrid_gap`, `advantage_eq`, `accept_eq` | `Games/Advantage.lean` |
| `Negligible.polyExpr_mul` | `Asymptotic/ReductionSupport.lean` |
| `NUPPT.distinguisherL_eq`, `Bridge.distAdv_eq`, `acceptProb_eq`, `expect_sample_pair` | `Asymptotic/Adversary.lean`, `Games/Bridges/Experiments.lean` |
| `prob_*`, `expect_*`, `simulate` equations, `OracleComp` laws, `NUPPT` run/coin/closure lemmas, `encodeList` readers | `Games/*`, `Complexity/Randomized/*`, `PrivateKey/Scheme.lean` |

The same abbreviation, notation and escalation rules apply as in the `padded_cpa` fill.

## Proof route and checkpoints

The docstring sketch, confirmed by Gate 12's auditor, is authoritative.

1. **Bit hybrids.** For `j ≤ n`, let `H_j` be the CPA experiment whose challenge encrypts, with
   independent coins per bit, the first `j` bits of the right message and the rest of the left.
   - Prove `H_0` and `H_n` are the `b = false` and `b = true` games.
   - Read the bitwise layout through `bitwise_enc_runAt`, and the coin blocks through
     `bitwiseEncCoins_ofFn`.
   - At `n = 0` both messages are empty and the advantage is `0`.

   Send checkpoint 1.
2. **The single-bit distinguisher `D` (T1).**
   - On `⟨pk, c⟩`, `D` runs `A`. It answers the challenge `⟨m₀, m₁⟩` with the padded bitwise
     ciphertext whose block `j⋆` is `c`. It encrypts the other blocks itself on `pk` and its seed
     tapes: bits of `m₁` before `j⋆`, bits of `m₀` after.
   - It records the first challenge. Repeated challenges get the same assembled ciphertext.
   - Its output is `A`'s bit, flipped when `(m₀_{j⋆}, m₁_{j⋆}) = (1, 0)`, and `[0]` when the two
     bits agree or no challenge was asked.
   - `j⋆(n)` is in the handler's initial state (any function of `n`). The seed is `n` single-bit
     encryption tapes.

   Send checkpoint 2.
3. **The exact identity.** Prove that `advantage(H_{j⋆}, H_{j⋆+1})` equals `D`'s single-bit
   advantage between `⟨pk, Enc_pk(0)⟩` and `⟨pk, Enc_pk(1)⟩`.
   - Use eager coins and the first-challenge congruence, as in `padded_cpa`.
   - The signed case split is the same as Gate 12's table: `(0,1)`, `(1,0)`, equal bits, and no
     challenge.

   Send checkpoint 3.
4. **The bound.**
   - `exists_advantage_hybrid_gap` at `n > 0` gives `A`'s advantage `≤ n ·` `D`'s advantage.
   - `singleBitSecure_iff` makes the latter negligible.
   - `Negligible.polyExpr_mul` with `PolyExpr.var` concludes.

   Send the final delivery.

Check: budget `q = 0`, no challenge, repeated challenges, the timeout output, and `n = 0`.

## Scope and proof discipline

- **Owned files.** Own `TCSlib/Cryptography/Encryption/PublicKey/BitwiseCPA.lean`: replace the one
  proof body and add helpers there. Generic helper modules are permitted under
  `TCSlib/Cryptography/Encryption/PublicKey/BitwiseCPA/`, imported precisely by the owned file. Keep
  every file below 1000 lines.
- **Frozen.** Do not edit `AdaptiveCPA.lean`, `OracleSecurity.lean`, the `OracleSecurity/` helpers,
  `EnsembleSecurity.lean` or any other existing file. If a lemma belongs in an existing file, put it
  in your helper module and list it in `REPORT.md` as a promotion request.
- **Generic lemmas.** List generic probability facts for promotion (duplication ledger DL-30), and
  reuse existing ones; grep first.
- **Edits allowed.** You may edit the target's sketch to describe the delivered proof. Preserve the
  statement, every other declaration (including the proved corollaries), the statement prose and
  the global simp attributes. Public helpers get formula docstrings and proof sketches (policy §3).
- **Reading definitions.** Use published readers for other files' definitions, in tactics and in
  term elaboration, including generated matchers and projections.
- **Escalation.** If the target appears false or a required reader is missing with no clean route,
  record the exact failing obligation and the smallest proposed correction in `REPORT.md`, then push
  a checkpoint.

## Checks and report

- **Bootstrap.** Use `order.txt` and the narrow `roots.txt` per the addendum. Insert new helper
  modules before their consumer. Check one module per `scripts/lean_check_tree.sh` call, with one
  Lean process per olean tree.
- **Sweep.** Recheck the owned modules, then sweep the supplied order. Compare `sorry` warnings with
  `base-sorries.txt`: the only change must be the removed `bitwise_padded_cpa`.
- **Axioms.** Print the axioms of `bitwise_padded_cpa` (only `propext`, `Classical.choice`,
  `Quot.sound`). Also print them for `bitwise_padded_adaptive_cpa` and `exists_adaptive_cpa`, and
  report exactly what they print: they still depend on the `adaptive-cpa` target.
- **Seal and scan.** Run an instance-aware seal of the touched declarations with the full candidate
  list and controls, and the explicit-unfold scan.
- **Lint.** Run `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography/Encryption/PublicKey --check8b`.
- **Report.** Give the base, the status, the changed files and sketch edits, the new declarations,
  any promotion or reader requests, and the evidence.

**Ready to dispatch**
