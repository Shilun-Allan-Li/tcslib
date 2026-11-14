# Claude fill · encrypt-then-tag is CCA2-secure (`ccaScheme_cca2`, Theorem 170.4)

**Issue base** `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9` on `cryptography/pass-shelat-ch2-4` (the merge of #299).
**Unit** `cca2-ett`. **Worker** Claude (standing ruling, 2026-11-11). **Lean** 4.25.0 and the Mathlib revision in that
commit's `lake-manifest.json`.

Prove the admitted theorem of [PS10, Theorem 170.4] in
`TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag.lean`. The theorem says that Algorithm 169.3 is CCA2-secure
when `F` is a pseudorandom function family. The scheme is the §3.9 scheme with its ciphertext `(r, c₁)` tagged by
`f_{k₂}(r ‖ c₁)`. The statement passed its Gate 06 audit (chapters 5–8 statements) and is frozen.

This fill starts after the duplication consolidation (#298) and its follow-up folds (#299), so the shared Games-layer
API is current. Seyoon ruled on 2026-11-13 that this job waits for those folds.

## Checkout and delivery

- Fetch `cryptography/pass-shelat-ch2-4`. Start a local branch `fill/cca2-ett` at the exact issue base, and record
  the base in `REPORT.md`. Keep the proof branch local.
- Read `policy.md`, the attached environment addendum and `README.md`.
- Deliver every checkpoint and the final payload under `inbox/fills/cca2-ett/` on `exchange/pass-shelat-ch5-8`:
  - `REPORT.md`;
  - `patches/`: the whole `git format-patch` series from the issue base;
  - `src/`: the changed and new files;
  - `evidence/`, with a `SHA256SUMS` manifest (see *Evidence completeness*).
- Commit as `fill cca2-ett: checkpoint N` and `fill cca2-ett: final`.
- Pull with rebase before pushing, push only your delivery path, and never force-push. Campaign changes land by
  a maintainer PR for Seyoon's approval.

## Target (frozen; quoted from the issue base)

```lean
theorem ccaScheme_cca2 (hF : PRF F) : (ccaScheme F E hE hFE).INDSecure .cca2 := by
  sorry
```

It lives in namespace `TCSlib.Cryptography.Composability`, with these variables:
- `F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)`;
- `E : List Bool → List Bool` and `hE : PolyTimeComputable E`;
- `hFE`, which says `E` agrees with `F` on `⟨s, x⟩` when `|s| = |x|`.

**The scheme `ccaScheme`** (all in the owned file):
- `Gen′` uses `3n` coins, split at `n` into the keys `k₁` (n bits) and `k₂` (2n bits), so the key is `⟨k₁, k₂⟩`.
- `Enc′` takes `n` coins `r` and outputs `⟨r, ⟨c₁, t⟩⟩`, where `c₁ = m ⊕ E⟨k₁, r⟩` and `t = E⟨k₂, r ++ c₁⟩`.
- `Dec′` checks the two length guards and the tag, and outputs `⊥` otherwise (`ccaDecOK`, `ccaDecFun`).
- Ciphertexts have `6n + 4` bits.
- The readers are `runAt_ccaGen`, `runAt_ccaEnc`, `runAt_ccaDec`, the `*_eq` lemmas and `length_eval_of_length`.

**The security notion `INDSecure .cca2`** (`INDSecure_iff`, `indGame_eq`, `indImpl_*` in
`PrivateKey/OracleSecurity.lean`): every adversary has negligible advantage between `indGame .cca2 A q false` and
`true`.

The module docstring's *source notes* record two points; read them:
- the tag covers `(r, c₁)`;
- at `n = 0` there is malformed-but-accepted behaviour, which changes no asymptotic claim.

The target's docstring sketch is the maintainer's route. You may edit it to describe the delivered proof.

## Published interfaces

| Interface | Provider |
|---|---|
| `ccaGenFun`, `ccaMaskFun`, `ccaEncFun`, `ccaDecOK`, `ccaDecFun` and their `_eq`; `polyTimeComputable_*`; `runAt_ccaGen/_ccaEnc/_ccaDec`; `length_eval_of_length`; `ccaScheme` and its `simps` fields | `PrivateKey/EncryptThenTag.lean` (owned) |
| `FixedLengthScheme` fields, `decAnswer`, `decOpen_*`, `indImpl`, `indImpl_dec`, `indCodec_*`, `indGame_eq`, `INDSecure_iff` | `PrivateKey/OracleSecurity.lean` |
| `prfFixedScheme`, `prfFixedScheme_cpa`, `prfFixedScheme_cca1` (Thm 168.2, proved, with the bound in its docstring) | `PrivateKey/OracleFromPRF.lean` |
| PRFGame's public API: `fImpl`, `eImpl` (`Games`); `pkHandler` (`Handler`); `exists_prfReduction` (`Reduction`); the `Transfer` readers; `lazyImpl`, `expect_lazyImpl` (`Lazy`); `abs_expect_fImpl_sub_le` (`Collision`) | `PrivateKey/OracleFromPRF/*.lean` (import them, do not copy) |
| `PRF`, `PRF.negligible_prfAdv`, `prfAdv_toOracleAdversary`; `prfAdv` | `Pseudorandom/Functions/Asymptotic/Defs.lean`, `Pseudorandom/Functions/Defs.lean` |
| T2 `exists_interactiveHandlerMachine`, T4 `exists_toOracleAdversary_of_bitCodec`, the `InteractiveHandler` readers (`rU`…`rL`, `rAns`, the `_input`/`_finInput` readers, `impl_of_ret`, `impl_of_query`, `finish_of_ret`) | `Games/Efficiency.lean` |
| `fwdHandler`, `fwdHandler_impl` | `Games/Forwarding.lean` |
| `prob_eq_until_bad`, `expect_eq_until_bad`, `prob_bad_le` (per-query potential bound), `expect_sample_mem_le`, `expect_simulate_eager`, `expect_congr_of_allOutputs` | `Games/Hopping.lean` |
| `simulate` equations, `simulate_eq_of_abs(_bounded)`, `castImpl` family, `buildComp_*`, `CostBoundedBy`, `bitCodec_*`, `padFin*`, `cntRead`/`ansRead`, `OracleComp` laws, `advantage_eq`, `accept_eq`, `ProbComp.expect_*` | `Games/*` |
| `NUPPT.exists_comp`, `exists_compParam`, `exists_withAdvice(On)`, `exists_seq`, `exists_reparam`; `NUPPT` run/coin readers; `Negligible` closure: `add`, `const_mul`, `mono`, `negligible_two_pow_neg`, and `comp_of_le`, which takes the PRF bound at parameter `2n` back to `n` | `Complexity/Randomized/Closure.lean`, `Asymptotic/*`, `Foundations/Negligible.lean` |
| `coinBlock`, `FunFamily.blocks`, `ofFn_blocks`, `Foundations/BitLists` | `Asymptotic/Adversary.lean`, `Foundations/BitLists.lean` |

## Proof route and checkpoints

Fix a CCA2 adversary `A`, with query budget `q` and challenge-bit games `b = false, true`.

1. **The tag key becomes a random function** (sketch step 1).
   - Build a PRF distinguisher at parameter `2n`. It samples `k₁` itself and runs `A`. It answers:
     - `Enc′` and the challenge with its oracle in place of `f_{k₂}`;
     - `Dec′` by recomputing the tag with its oracle.

     It is a T2 handler (`exists_interactiveHandlerMachine`) with `k₁` in its seed, made an oracle adversary with
     T4 at length `2n`.
   - For each `b`, the gap between the real game and the game with a random tag function is at most `prfAdv` at
     `2n`, which is negligible in `n` by `Negligible.comp_of_le` with `φ n = 2n`.

   Send checkpoint 1.
2. **Fresh decryption queries are rejected** (sketch step 2). For positive `n`, call a `Dec′` query `(r, c₁, t)`
   *fresh* if `(r, c₁)` is not the pair of an earlier `Enc′` or challenge answer.
   - Compare with the game that rejects every fresh query. Couple both with the same tapes and random function:
     they agree until the first fresh query with a valid tag.
   - Bound that event by `q(n)/2^{2n}` with `prob_bad_le`, or an equal-until-bad argument through
     `prob_eq_until_bad`/`expect_eq_until_bad`. In the always-reject game, a rejected guess reveals no value of the
     random function at an unanswered pair.
   - A *non-fresh* valid query is an earlier answer. Canonical parsing (`pairEncode` injectivity, the length guards)
     makes it either the refused challenge or an encryption of a chosen message.

   Send checkpoint 2.
3. **Reduction to the §3.9 scheme's CPA security** (sketch step 3).
   - The always-reject game is simulated by a CPA adversary against `prfFixedScheme` under `k₁`:
     - `Enc′` and challenge answers come from the CPA oracles, re-encoded from `⟨r, c₁⟩` (3n + 2 bits) to
       `⟨r, ⟨c₁, t⟩⟩`, with `t` from a lazily sampled random function (`lazyImpl`);
     - `Dec′` answers come from the table of earlier answers, or are `⊥`.
   - If you use fresh uniform tags instead of a lazily sampled function (the source's version), account for the
     nonce-collision term `q(n)²/2^n`.
   - Combine the terms: the PRF advantages at `2n`, the first-discrepancy term `q(n)/2^{2n}`, any collision term,
     and the CPA advantage (`prfFixedScheme_cpa`). The sum is negligible. Handle `n = 0` by `Negligible.mono`
     (eventual bounds).

   Send the final delivery.

Check the edge cases:
- `n = 0`, including the malformed `0000` that decrypts to the empty message;
- budget 0, no challenge, and repeated challenges;
- `A` querying `Dec′` on the challenge itself (refused), on the challenge with a changed tag, on malformed or
  over-long words, and on an earlier `Enc′` answer;
- nonce collisions;
- the codecs' timeout outputs, in every direction.

If the sketch is wrong, or the target is false as stated, stop and escalate with the exact obligation: a checkpoint
with the counterexample or the missing fact. Do not weaken the statement.

## Scope and proof discipline

- **Owned file.** You own `PrivateKey/EncryptThenTag.lean`:
  - replace the target's proof body and edit its sketch;
  - update the module title (drop "(statement phase)") and the `## Main results` status.
- **Helper modules.**
  - They are permitted under `TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/`.
  - The owned file imports them precisely and gets a `## Contents` list.
  - A helper may import `OracleFromPRF` and its helpers. They are not downstream of the owned file, so this creates
    no cycle; check it.
- **Size.** Keep every file below 1000 lines.
- **Frozen.** Do not edit any other file.
  - `Games/Efficiency.lean` is at 982 lines and must be split before it grows. Do not add to it.
  - If a lemma belongs in an existing file, put it in your helper module and list it as a promotion request.
  - If a reader of another file's definition is missing, escalate: record the exact obligation and the reader you
    need, and push a checkpoint.
- **Duplication (binding).**
  - **Public lemmas.** Do not copy them: import them, including PRFGame's public API above.
  - **Private lemmas** of `OracleFromPRF/` or `OracleFromPRF.lean`. Do not copy them. If you need one, re-derive it
    from published readers in your helper module, disclose it in `REPORT.md` as **"PRFGame overlap: <item>"**, and
    keep its statement in the general form.
  - **Other generic facts** (probability, simulation, machine or list) go on your promotion list. Grep first, and
    report the searches.
- **Statements.** Preserve the target statement, every other declaration, the statement prose and the global simp
  attributes.
- **Docstrings.** Public helpers get docstrings with their formulas, and proof sketches when nontrivial
  (policy §3). Add no `@[simp]`. A new public `abbrev` needs an `_eq`/`_iff` lemma.
- **Rule 10.**
  - Use only published readers for other files' definitions, including generated matchers and projections.
  - Your helper modules count as foreign to each other and to the owned file.
  - The owned file's definitions are foreign to your helpers. Read `ccaScheme` and its parts through
    `runAt_cca*`, the `_eq` lemmas and the `simps` fields.

## Checks and report

- **Bootstrap.** Bootstrap from `order.txt` (264 modules) and the narrow `roots.txt` (98), following the addendum.
  Check one module per `scripts/lean_check_tree.sh` call, with one Lean process per olean tree. Insert helper
  modules before their consumers.
- **Sweep.**
  - Recheck the owned module, then sweep the supplied order with 0 errors.
  - Compare the `sorry` warnings with `base-sorries.txt` (24 declarations in 10 modules). The only change must be
    the removal of `ccaScheme_cca2`.
- **Axioms.**
  - Print the axioms of `ccaScheme_cca2`. Expect only `propext`, `Classical.choice` and `Quot.sound`.
  - Print them for every stored constant of the changed and new files.
- **Rule 10 evidence.**
  - Run whole-file seals A and B of every changed or new file over its full TCSlib import closure, at base and
    final, and report every failing declaration.
  - Add paired controls that pass unsealed and fail sealed, each sealed negative failing exactly once.
  - Run the explicit-unfold scan.
  - Report the seals with `PolyExpr.eval` both excluded as notation and sealed.
- **Lint.** Run `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography/Encryption/PrivateKey --check8b`. It
  must show no new FAIL.
- **Report.** Give:
  - the base and the target's status;
  - the changed files and the sketch edits;
  - the new declarations;
  - the promotion and reader requests;
  - every "PRFGame overlap" item;
  - the evidence.

### Evidence completeness

Gate 20 held a delivery for omitted raw evidence (G20-01).
- Every file that `evidence/SHA256SUMS` names must be delivered. That includes:
  - seal and control sources, manifests and request records;
  - every raw log and `results.jsonl`;
  - the probe sources and the tools used.
- If the evidence is too large for one commit, deliver it in several commits, or as numbered ZIP parts, each part
  with an entry list. Do not leave anything out for size.
- Check before delivery that the delivered paths are exactly the manifest's.

The maintainer checks `TCSlib` and `audits/pass-shelat/Checks` on the full-library tree at landing.

**Ready to dispatch**
