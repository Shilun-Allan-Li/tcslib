# Claude fill · under CCA2, secrecy and non-malleability coincide (`indSecure_cca2_iff_nmSecure_cca2`)

**Issue base** `b96ab3ccc1915497ea3138df499eec00b6581db0` on `cryptography/pass-shelat-ch2-4` (the merge of #293).
**Unit** `nm-cca2`. **Worker** Claude (standing ruling, 2026-11-11). **Lean** 4.25.0 and the Mathlib revision in
that commit's `lake-manifest.json`.

Prove the admitted theorem of [PS10, Theorem 175.9] in
`TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability.lean`: for a fixed-length public-key
scheme, IND-CCA2 security (Definition 171.5) and CCA2 non-malleability (Definition 172.6) are equivalent. The
statement passed its Gate 06 audit (#232).

**This fill runs in parallel with the `dl-consolidation` job**, which moves the generic lemmas of duplication-ledger
rows DL-30 to DL-34. Read the duplication rule below.

## Checkout and delivery

- Fetch `cryptography/pass-shelat-ch2-4`. Start a local branch `fill/nm-cca2` at the exact issue base, and record
  the base in `REPORT.md`. Keep the proof branch local.
- Read `policy.md`, the attached environment addendum and `README.md`.
- Deliver every checkpoint and the final payload under `inbox/fills/nm-cca2/` on `exchange/pass-shelat-ch5-8`:
  - `REPORT.md`;
  - `patches/`: the whole `git format-patch` series from the issue base;
  - `src/`: the changed files;
  - `evidence/`.
- Commit as `fill nm-cca2: checkpoint N` and `fill nm-cca2: final`.
- Pull with rebase before pushing, push only your delivery path, and never force-push. Campaign changes land by
  a maintainer PR for Seyoon's approval.

## Target (frozen; quoted from the issue base)

```lean
theorem indSecure_cca2_iff_nmSecure_cca2 : S.INDSecure .cca2 ↔ S.NMSecure .cca2 := by
  sorry
```

It lives in namespace `TCSlib.Cryptography.Composability.FixedLengthPKScheme`, with `S : FixedLengthPKScheme`.
- **`NMSecure atk`:** for all `A`, `q`, `ℓ` and `D`, the advantage between `nmGame atk A q ℓ D false` and `true`
  is negligible.
- **`nmGame`:** the adversary runs against the IND oracles `indImpl atk b` through `nmCodec n ℓ` and outputs `ℓ`
  ciphertexts. They are decrypted by `nmOutput`, with `nmDecrypt` giving `⊥ = zeroBits` on a copy of the recorded
  challenge, and `D` judges the result.
- **`INDSecure`:** defined in `PublicKey/OracleSecurity.lean` (`indGame`, `INDSecure_iff`).

## Published interfaces

| Interface | Provider |
|---|---|
| `nmCodec_*`, `nthCt_eq`, `nmDecrypt_eq`, `nmDecrypt_challenge`, `nmOutput_eq`, `nmGame_eq`, `NMSecure_iff` | `PublicKey/NonMalleability/Indistinguishability.lean` (owned; the statement-phase readers) |
| `FixedLengthPKScheme` fields (`correct`, `enc_length`, `gen_uniform`, …), `inLens_*`, `outLens_*`, `indSpec_*` (incl. `_decDom`, `_challengeDom/_Rng`), `indImpl_dec`, `indImpl_dec_onSpec`, `indImpl_challenge_none(_onSpec)`, `indImpl_challenge_repeat(_onSpec)`, `indImpl_dec_cca2_challenge`, `indCodec_*`, `indGame_eq`, `INDSecure_iff` | `PublicKey/OracleSecurity.lean` |
| `FixedLengthScheme.decAnswer` and its readers | `PrivateKey/OracleSecurity.lean` |
| T1 `Games.exists_handlerMachine`, T2 `Games.exists_interactiveHandlerMachine`, `exists_toCompOn_of_toComp`, T4 `exists_toOracleAdversary_of_bitCodec`, and the `PolyHandler` / `InteractiveHandler` readers | `Games/Efficiency.lean` |
| `bitCodec_*`, `decodeBitMove`, `simulate` equations, `OracleComp` laws, `advantage_eq`, `accept_eq` | `Games/*` |
| `NUPPT.exists_comp`, `exists_compParam`, `exists_withAdvice`, `exists_seq`, `exists_reparam`; `NUPPT` run/coin readers; `distinguisherL_eq` | `Complexity/Randomized/Closure.lean`, `Asymptotic/Adversary.lean` |
| Worked models of T2 handlers with forwarded oracles, eager coins and cast transport | `PublicKey/AdaptiveCPA/`, `PublicKey/BitwiseCPA/`, `PrivateKey/OracleFromPRF/` (models only; see the duplication rule) |

## Proof route and checkpoints

The target's docstring sketch is authoritative.

1. **(⇒) IND-CCA2 ⇒ NM-CCA2.** Given an NM adversary `A` (budget `q`, `ℓ` ciphertexts) and a distinguisher `D`,
   build an IND adversary with a T2 handler:
   - `advIn = pk`; it forwards `A`'s `Dec` and challenge queries;
   - in finalization (`finCall = ℓ`) it asks CCA2's `Dec` on each of `A`'s ciphertexts, then runs `D` on the
     answers, for total budget `q + ℓ`;
   - the advice is carried through `z` with the `NUPPT` closure lemmas.

   Show that the IND game at each `b` equals `NM_b`, so the advantage is equal. The key facts:
   - CCA2's `Dec` refuses the recorded challenge with the same `zeroBits` that `nmDecrypt` gives a copy
     (`indImpl_dec_cca2_challenge`, `nmDecrypt_challenge`);
   - it decrypts every other ciphertext as `nmDecrypt` does;
   - with no challenge asked, both decrypt everything.

   Send checkpoint 1.
2. **(⇐) NM-CCA2 ⇒ IND-CCA2.** Given an IND adversary `A` with guess `g`:
   - The NM adversary runs `A` and outputs `ℓ = 2` fresh encryptions, of `g^{msgLen}` and `(¬g)^{msgLen}`, under
     `pk` with its own seed coins.
   - The two plaintexts differ for `msgLen(n) > 0`, so by `correct` at most one ciphertext is the challenge.
   - The distinguisher reads `g` from the first decryption if it is valid, and from the second (negated)
     otherwise.

   Show that the NM advantage equals the IND advantage. At `msgLen(n) = 0` both IND games coincide, so the
   advantage is 0.

   Send checkpoint 2.
3. **Assemble the equivalence**, with the polynomial budgets of each direction.

   Send the final delivery.

Check the edge cases:
- budget 0;
- `ℓ = 0`;
- `msgLen(n) = 0`;
- no challenge asked;
- repeated challenges;
- `A` outputting the challenge itself, or a malformed or invalid ciphertext;
- the codec's timeout output, in both directions.

## Scope and proof discipline

- **Owned file.** You own `NonMalleability/Indistinguishability.lean`: replace the proof body and add helpers.
- **Helper modules.** Helper modules are permitted under `TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability/`.
  The owned file imports them precisely. It gets a `## Contents` list if it becomes a facade, and its status line
  for the target is updated.
- **Size.** Keep every file below 1000 lines.
- **Frozen.** Do not edit any other file, `NonMalleability/Simulation.lean` included. If a lemma belongs in an
  existing file, put it in your helper module and list it in `REPORT.md` as a promotion request. If a reader of
  another file's definition is missing, escalate: record the exact obligation and the reader you need, and push
  a checkpoint.
- **Duplication (binding).**
  - Do not copy public lemmas: import them where they are at the issue base. The maintainer re-points them at
    landing if the consolidation has moved them.
  - Do not copy private lemmas from `AdaptiveCPA/`, `BitwiseCPA/` or `OracleFromPRF/`. These include the
    round-input readers `rU`…`rCnt`, `impl_of_ret` and `ofFn_padFin_eq_padL`. If your handler needs one of
    them, re-derive it from the published `InteractiveHandler` and `padFin` readers in your helper module,
    disclose it in `REPORT.md` as **"DL-30–34 overlap: <item>"**, and keep its statement in the general form. The
    maintainer replaces it with the promoted lemma at landing.
  - Any other generic probability, simulation or list fact goes on your promotion list. Grep first.
- **Statements.** You may edit the target's sketch to describe the delivered proof. Preserve the statement, every
  other declaration, the statement prose and the global simp attributes.
- **Docstrings.** Public helpers get docstrings with their formulas, and proof sketches when nontrivial (policy §3).
- **Rule 10.** Use only published readers for other files' definitions, including generated matchers and
  projections. Your helper modules count as foreign to each other and to the owned file.

## Checks and report

- **Bootstrap.** Bootstrap from `order.txt` (249 modules) and the narrow `roots.txt` per the addendum. Check one
  module per `scripts/lean_check_tree.sh` call, with one Lean process per olean tree. Insert helper modules before
  their consumers.
- **Sweep.** Recheck the owned modules, then sweep the supplied order. Compare the `sorry` warnings with
  `base-sorries.txt`: the only change must be the removal of `indSecure_cca2_iff_nmSecure_cca2`.
- **Axioms.**
  - Print the axioms of the target. Expect only `propext`, `Classical.choice` and `Quot.sound`.
  - Print them for every stored constant of the changed and new files.
  - Print them for `simNMSecure_cpa_iff_nmSecure_cpa` and report exactly what it prints. It still depends on the
    two `Simulation.lean` targets.
- **Rule 10 evidence.**
  - Run whole-file seals of every changed or new file over its full TCSlib import closure, with base controls and
    paired controls that pass unsealed and fail sealed.
  - Run the explicit-unfold scan.
  - Report the seal both with `PolyExpr.eval` excluded as notation and with it sealed.
- **Lint.** Run `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography/Encryption/PublicKey --check8b`.
- **Report.** Give:
  - the base and the target's status;
  - the changed files and the sketch edit;
  - the new declarations;
  - the promotion and reader requests, and every "DL-30–34 overlap" item;
  - the evidence.

**Ready to dispatch**
