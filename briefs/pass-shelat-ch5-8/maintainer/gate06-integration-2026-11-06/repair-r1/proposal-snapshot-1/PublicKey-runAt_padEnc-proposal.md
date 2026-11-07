# PublicKey padded encryptor: one proof/header transport proposal

**Unapplied, unchecked proposal.** Explicit source worktree:
`/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4`.
Frozen HEAD: `e9d64158461bfe24ddc88ab885bc4017899b4c16`.

Scope is exactly the existing `runAt_padEnc` declaration: an explicit typed-coin transport in its header, a matching clarification in its docstring, and replacement of its one existing tactic block. No definition, algorithm, data field, logical premise, admission, other theorem or caller proof changes. The separate Lamport proposals do not touch this module and remain unapplied.

## Diagnostic and precise root

Completed log:
`/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-rule10-r2/runs/G06Seal_015_TCSlib_Cryptography_Composability_PublicKey.log`.

The installed-status marker records 1677 requested/verified names, 1658 active and 19 already irreducible. The source/probe line map maps frozen source 194 to probe 1939. The primary error at probe `1939:49` is in the theorem header:

- supplied `r : enc.Coins n`;
- required `r : (padEnc enc L).Coins n`;
- offending application `(padEnc enc L).runAt n y r`.

The former implicit identification reduces the foreign machine constructor and/or `coinLen` to equate the two domains. A proof-body-only change cannot repair this header error. The second diagnostic at `1939:91` contains `List.ofFn (sorry ())`, produced by failed header elaboration; it is not a source admission or evidence of a separate mathematical defect.

Later unused/unreachable caller warnings arise after that recovery failure. They do not establish that either caller is sound under the seal.

## Explicit header and one proof block

```lean
theorem runAt_padEnc {enc : NUPPT} (henc : enc.Uniform) (L : PolyExpr) (n : ℕ) (y : List Bool)
    (r : (padEnc enc L).Coins n) : (padEnc enc L).runAt n y r =
      padCt (L.eval n) (enc.runAt n y (NUPPT.coinsCongr (padEnc_coins enc L) n r)) := by
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform, henc.runAt_eq,
    NUPPT.coinsCongr_ofFn]
  simp only [padEncFun_eq, NUPPT.inParam_eq, NUPPT.inArg_eq, NUPPT.inCoins_eq,
    NUPPT.layout_eq, NUPPT.advInput_eq, pairFstD_pairEncode, pairSndD_pairEncode,
    List.length_replicate]
```

The same parameter, argument and all coin strings are retained. The binder now uses the padded machine's own coin type; the original encryptor is called on its image under the existing public equivalence

`NUPPT.coinsCongr (padEnc_coins enc L) n : (padEnc enc L).Coins n ≃ enc.Coins n`.

This changes the representation of the all-coins equation, not its content. Every original encryptor coin input has a preimage under the equivalence, and `coinsCongr_ofFn` states that the bit list is exactly unchanged. No side condition, length restriction or extra security assumption is introduced.

The existing owner-local `padEnc_coins` (source 189–190) already publishes equality of coin polynomials using `NUPPT.coins_ofPolyTimeUniform`. There is no need for a new equivalence definition, helper theorem or raw machine-body alias.

## Public-reader proof route

1. `NUPPT.runAt_eq` (`Randomized/PPT.lean:234–235`) reads the padded typed run as an untyped run on its coin list.
2. `NUPPT.runAtL_ofPolyTimeUniform` (`PPT.lean:410–413`) reads the wrapped machine's output as `padEncFun` on the empty-advice layout. The owner-local `padEnc` abbreviation is allowed notation; no foreign constructor body is unfolded.
3. `NUPPT.Uniform.runAt_eq` (`Randomized/NonUniform.lean:100–102`) reads the original encryptor's typed activation on the transported coins.
4. `NUPPT.coinsCongr_ofFn` (`PPT.lean:245–247`) replaces the transported coin list by the original padded-machine coin list.
5. `padEncFun_eq`, public layout/input projection equations, the pairing readers and `List.length_replicate` identify the two padded output expressions.

Every identifier explicitly named in the new tactic lists is a theorem. The header applies the public `coinsCongr` function without reading its body. No explicit foreign ordinary definition, Core/Mathlib definition, raw `NUPPT` body or new simp attribute is introduced.

## Deferred caller adjustments: separate invocations

A full TCSlib search found only two callers beyond the declaration itself. **Neither is changed by this patch.** Each is a different existing tactic block and should be repaired in its own later invocation.

| Frozen source site | Future adjustment |
|---|---|
| `FixedLengthPKScheme.ofPadded.correct`, lines 264–267 | After rewriting with the repaired run contract and the existing unpadding lemma, instantiate the unchanged original `correct` premise with `NUPPT.coinsCongr (padEnc_coins enc L) n re`, where `re` is the padded encryptor's coin input. |
| `FixedLengthPKScheme.ofPadded.enc_length`, lines 268–271 | After rewriting with the repaired run contract, instantiate the unchanged `hL` premise with that same transported coin input before applying `length_padCt`. |

The wrapper algorithm, `ofPadded` fields and its original `correct/hL` hypotheses remain frozen. Do not rely on the old direct `re` applications: they are precisely the typed identification which must be explicit under seals. The chosen run-contract orientation lets these callers rewrite their actual padded-machine activation directly.

This patch alone does **not** claim full-module native success: the two caller proofs remain pending.

## Fingerprints and static validation

| Item | SHA-256 |
|---|---|
| Frozen PublicKey source | `8bc99296a28985a783285c42db1bc0e27787538e78d3c909bbff594dc0ef9717` |
| Proposed PublicKey source, in memory only | `915d1fea150487befcac3c2d9c169b025c352f93b48d5e9dc1bbf203fd36d18a` |
| Unapplied patch | `f7e52d031b254d58ae8047576ed4972d4f4a9fda35b9698e2e0e7a371cd09e0a` |
| Completed original seal log | `cc40fde56ebe4e42d24a7d66f58d8e91abcd1e806fc1eec3fa3104a5cfe225f3` |
| Original recorded seal probe | `8999779ccebb54d6c630bece655cb4713d83d56dd5fc850d6d392fa15a2bcf90` |

The old declaration block matched exactly once. Before/after splitting around that block verifies that every other source byte is unchanged. The number of `:= by` blocks is unchanged: only one existing proof block was replaced. HEAD and the live source fingerprint were verified against the frozen values.

Root should first check this contract/header in the authorized native environment (a prefix probe can isolate it from pending callers), then make each caller adjustment in a separate invocation and rerun the whole-file seal with installed-status checks. Recollect the changed declaration and inspect its explicit tactic lists/axioms; do not infer a complete module pass from elimination of the primary header diagnostic alone.

No Lean/cache, apps, Git mutations or library edits occurred. Only the requested ignored proposal files were saved.

**Not yet clear to merge — this proposal and the two separate caller repairs require native checking; the source remains frozen.**
