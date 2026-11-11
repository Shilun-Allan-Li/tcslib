# Codex fill · the §3.9 scheme is not CCA2-secure (`prfFixedScheme_not_cca2`)

**Issue base** `4a09f3993eb9344fc5714610e41ab141a0144db8` on `cryptography/pass-shelat-ch2-4`
(later campaign commits are records only).
**Unit** `not-cca2`. **Worker** Codex. **Lean** 4.25.0 and the Mathlib revision in that commit's
`lake-manifest.json`.

Prove the admitted theorem `Composability.prfFixedScheme_not_cca2` in
`TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF.lean` [PS10, §7.1.3, p. 169,
Claim 169.a]: an explicit adversary with a constant query budget has advantage exactly `1`
against the scheme of Algorithm 99.1 in the CCA2 game, at every `n > 0` and for every family
`F`. The proved corollary `not_prfFixedScheme_cca2` then holds without admissions. The
statement passed Gate 04.

## Checkout and delivery (Codex)

- Fetch `cryptography/pass-shelat-ch2-4` and start a local branch `fill/not-cca2` at the exact
  issue base above. Record the base in `REPORT.md`. Do not push any branch.
- Read `policy.md`, the attached environment addendum and `README.md`.
- **Return each checkpoint and the final delivery in the chat**, clearly labelled, as a ZIP with
  `not-cca2/` at its root containing `REPORT.md`, `patches/` (the whole `git format-patch` series
  from the issue base), `src/` (the final owned files under their repository paths) and
  `evidence/`. A self-contained Markdown delivery with the same content is also acceptable.
  Do not push to GitHub. The maintainer files your delivery under `inbox/fills/not-cca2/` and
  reviews it for a PR that Seyoon approves.

## Target

The source declaration is frozen. This quote comes directly from the issue base (line 143).
The section variables are `F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)`,
`E : List Bool → List Bool`, `hE : PolyTimeComputable E` and
`hFE : ∀ n s x, E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (F n s x)`.

```lean
theorem prfFixedScheme_not_cca2 :
    ∃ (A : NUPPT) (q : PolyExpr), ∀ n, 0 < n →
      advantage ((prfFixedScheme F E hE hFE).indGame .cca2 A (q.eval n) false n)
        ((prfFixedScheme F E hE hFE).indGame .cca2 A (q.eval n) true n) = 1 := by
  sorry
```

The game (`FixedLengthScheme.indGame`, `Encryption/PrivateKey/OracleSecurity.lean`) samples the
key-generation coins and `A`'s coins and simulates `A.toComp (S.indCodec n) n q r` against three
oracles (`indImpl`): `Enc` (index 0, `n`-bit messages), `Dec` (index 1, `(3n+2)`-bit ciphertexts,
answers `⟨1, m⟩` or `⊥`; under CCA2 it refuses only the recorded challenge) and `Challenge`
(index 2, `2n`-bit query `⟨m₀, m₁⟩`, answers `Enc_k(m_b)` once and repeats it). The output is
`A`'s one-bit result.

## Published interfaces

Read every definition of another file through these published lemmas (policy §1, rule 10).
`OracleFromPRF.lean`'s own `prfFixedScheme` may be unfolded, but prefer its readers.

| Interface | Provider |
|---|---|
| `prfFixedScheme_toPrivateKeyScheme`, `prfFixedScheme_ctLen` (simps), `prfFixedScheme_gen/_enc/_dec` | `Encryption/PrivateKey/OracleFromPRF.lean` (owned) |
| `prfScheme_gen`, `prfScheme_enc`, **`prfScheme_dec` (to add, see Scope)**, `runAt_prfEnc`, `runAt_prfDec`, `decodeFin_runAt_prfDec_of_not_wf`, `polyTimeComputable_prfEncFun/_prfDecFun` | `Encryption/PrivateKey/FromPRF.lean` |
| `runAt_coinKey` | `Encryption/PrivateKey/FromPRG.lean` |
| `inLens_zero/_one/_two`, `outLens_zero/_one/_two`, `indSpec_eq`, `decOpen_cca2`, `encryptAt_eq`, `decAnswer_some/_none`, `splitHalf_fst/_snd`, `indImpl_enc/_dec/_challenge_none/_challenge_repeat/_dec_cca2_challenge`, `indCodec_decodeMove/_encodeEntry/_timeout`, `indGame_eq` | `Encryption/PrivateKey/OracleSecurity.lean` |
| `NUPPT.ofPolyTimeUniform`, `coins_ofPolyTimeUniform`, `ofPolyTimeUniform_uniform`, `runAtL_ofPolyTimeUniform`, `runAt_eq`, `coinLen_eq`, `coinsEquiv_ofPolyTimeUniform(_ofFn)`, `inArg_eq`, `inParam_eq`, `inCoins_eq`, `advInput_eq` | `Complexity/Randomized/PPT.lean`, `NonUniform.lean`, `Closure.lean` |
| `NUPPT.toComp_eq`, `buildComp_zero_of_ret/_of_query`, `buildComp_succ_of_ret/_of_query` | `Games/Machines.lean` |
| `bitCodec_decodeMove`, `bitCodec_encodeEntry`, `bitCodec_timeout`, `decodeBitMove_query`, `decodeBitMove_ret`, `encodeLog_bitCodec`, `zeroBits_apply`, `ofFn_zeroBits` | `Games/BitCodec.lean` |
| `simulate` equations and `OracleComp` pure/bind/query laws | `Games/Simulate.lean`, `Games/OracleComp.lean` |
| `accept_eq`, `advantage_eq`, `prob_bind`, `prob_pure`, `expect_*`, `sample_eq` | `Games/Advantage.lean`, `Games/Probability.lean` |
| `pairEncode_eq_dbl`, `pairDecode_pairEncode`, `pairFstD_pairEncode`, `pairSndD_pairEncode`, `length_pairEncode`, `decodeFin_ofFn`, `padFin` readers | `Complexity/TuringMachine/Encoding.lean`, `Asymptotic/Adversary.lean` |

`NUPPT.Coins`, `bitSpecAt`, `bitSpec`, `QueryImpl` and `indSpec` are abbreviations;
`PolyExpr.eval` is notation. If another needed equation has no published reader, record it in
`REPORT.md` and use the escalation route; do not unfold the foreign definition.

## Proof route and checkpoints

The docstring sketch is the route.

1. **The adversary.** Define a polynomial-time string function on `A`'s activation input (its
   encoded log, read through `toComp_eq`, `encodeLog_bitCodec` and the decoder cases) that:
   with an empty log, moves `Challenge ⟨0^n, 1^n⟩`; with one entry (the challenge answer `c`),
   moves `Dec c'` where `c'` is `c` with its last bit flipped; with two entries, outputs
   `¬ m'_{n-1}` where the second entry's answer is `⟨v, m'⟩`. Build `A` with
   `NUPPT.ofPolyTimeUniform` and choose a constant budget `q` (for example `.const 2`; check
   how `buildComp` spends its budget so that the third activation's output is read). Prove the
   function polynomial-time from the closure combinators. Send checkpoint 1.
2. **The challenge.** For `n > 0`, the challenge in `IND_b` is
   `padFin (3n+2) (pairEncode r (b^n ⊕ f_k(r)))` (`encryptAt_eq`, `prfFixedScheme_enc`,
   `prfScheme_enc`, `runAt_prfEnc`, `hFE`, `runAt_coinKey`). Its length is exactly `3n + 2`, and
   its last bit lies in the second component (`pairEncode_eq_dbl`). Flipping it gives `c' ≠ c`,
   still well-formed, with second component `b^n ⊕ e_{n-1} ⊕ f_k(r)`. Send checkpoint 2.
3. **The decryption answer.** Under CCA2 with state `some c` and query `c' ≠ c`, `Dec` answers
   `decAnswer (decodeFin n (Dec_k ⟨r, …⟩))` (`indImpl_dec`, `decOpen_cca2`). With
   `prfFixedScheme_dec`, the new `prfScheme_dec` and `runAt_prfDec`, the answer is
   `⟨1, b^n ⊕ e_{n-1}⟩`, so its last message bit is `¬ b`. Send checkpoint 3.
4. **The advantage.** For every key and coins, the simulation returns `b` (step 1 reads the
   answers off the log). So `indGame .cca2 A q b n` returns `b` with probability `1`, its
   acceptance is `0` for `b = false` and `1` for `b = true`, and the advantage is `|0 − 1| = 1`.
   Send the final delivery.

Check: `n > 0` is used only for the last-bit position; the `Enc` oracle is never queried; the
timeout output is not reached with the chosen budget.

## Scope and proof discipline

- Own `TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF.lean`: replace the one proof body
  and add helpers there (keep the file below 1000 lines).
- **Authorized reader addition.** In `TCSlib/Cryptography/Encryption/PrivateKey/FromPRF.lean`,
  add exactly one public theorem beside `prfScheme_gen`/`prfScheme_enc`, in the same form:
  `prfScheme_dec : (prfScheme F E hE hFE).dec = NUPPT.ofPolyTimeUniform
  (polyTimeComputable_prfDecFun hE) (.const 0) := rfl`, with a docstring stating that formula.
  Change nothing else in that file.
- You may edit the target's proof sketch to describe the delivered proof. Preserve the statement,
  every other declaration (including the admitted `prfFixedScheme_cpa`/`_cca1`), the statement
  prose and the global simp attributes. Public helpers get a docstring with their formula and a
  proof sketch when nontrivial (policy §3). Do not edit any other file.
- Use published readers for other files' definitions in tactics and in term elaboration,
  including generated matchers and projections. For core and Mathlib use their equation lemmas
  in `simp`, `rw` and `unfold`.
- **Escalation.** If the target appears false, or a required reader is missing with no clean
  route, write the exact failing obligation and the smallest proposed correction in `REPORT.md`
  and return a checkpoint. At a partial delivery identify the remaining admission and the
  checked frontier.

## Checks and report

- Bootstrap from `order.txt` and the narrow `roots.txt` using the environment addendum. Check one
  module per `scripts/lean_check_tree.sh` invocation; one Lean process per olean tree; never
  `lake build`, never an unfiltered cache get; Python as `python3 -I`.
- Recheck `PrivateKey/FromPRF` and `PrivateKey/OracleFromPRF`, then sweep the rest of the supplied
  order (it includes every module downstream of `FromPRF`). Compare `sorry` warnings with
  `base-sorries.txt`: the only change must be the removed `prfFixedScheme_not_cca2`.
- Print the axioms of `prfFixedScheme_not_cca2` and `not_prfFixedScheme_cca2` (only `propext`,
  `Classical.choice`, `Quot.sound`).
- Collect foreign references from the elaborated new proofs, including generated matcher and
  projection helpers. Run an instance-aware seal of the touched declarations with the full
  candidate list, plus a control that passes before sealing and fails after sealing. Report the
  candidates, controls and any findings. Include the explicit-unfold scan and
  `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography/Encryption/PrivateKey --check8b`.
- Report the issue base, the target's status, exact changed files and sketch edits, new helper
  declarations, any reader requests, and the resource, cache, bootstrap, sweep, axioms, seals and
  lint evidence.

**Ready to dispatch**
