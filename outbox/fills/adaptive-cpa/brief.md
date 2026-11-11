# Claude fill · adaptive CPA lift (`adaptive_cpa`)

**Issue base** `4a9b2c91eb2f89c4fb624339d5b4ba9cfd35ac27` on `cryptography/pass-shelat-ch2-4`
(the merges of #287 and #288). **Unit** `adaptive-cpa`. **Worker** Claude. **Lean** 4.25.0 and the
Mathlib revision in that commit's `lake-manifest.json`.

Prove the admitted theorem `Composability.FixedLengthPKScheme.INDSecure.adaptive_cpa` in
`TCSlib/Cryptography/Encryption/PublicKey/AdaptiveCPA.lean`: single-challenge CPA security of a
fixed-length public-key scheme gives security in the adaptive left-or-right multi-challenge CPA
game [PS10, Definition 171.5; the single-to-many hybrid argument of p. 103, extended to adaptive
challenges]. The statement passed Gate 12. With the parallel `bitwise-cpa` fill it completes the
first catalog route (`SingleBitSecure.exists_adaptive_cpa`). The `bitwise-cpa` fill does not
touch this file, and this fill does not touch `BitwiseCPA.lean`.

## Checkout and delivery

- Fetch `cryptography/pass-shelat-ch2-4` and start a local branch `fill/adaptive-cpa` at the exact
  issue base above. Record the base in `REPORT.md`. Keep the local branch at that ancestry.
- Read `policy.md`, the attached environment addendum and `README.md`.
- Deliver every checkpoint and the final payload under `inbox/fills/adaptive-cpa/` on
  `exchange/pass-shelat-ch5-8`:
  - `REPORT.md`;
  - `patches/`, the whole `git format-patch` series from the issue base;
  - `src/`, the owned paths;
  - `evidence/`.

  Use the commit messages `fill adaptive-cpa: checkpoint N` and `fill adaptive-cpa: final`. Pull
  with rebase before pushing, push only your delivery path, and never force-push. Keep the proof
  branch local. Campaign changes land by a maintainer PR for Seyoon's approval.

## Target

The statement is frozen. This quote comes from the issue base:

```lean
theorem INDSecure.adaptive_cpa {S : FixedLengthPKScheme} (h : S.INDSecure .cpa) :
    S.AdaptiveINDSecure .cpa := by
  sorry
```

The games:
- `S.indGame .cpa B q b n` (`PublicKey/OracleSecurity.lean`) is the single-challenge game.
- `S.adaptiveIndGame .cpa A q cap b n` (`PublicKey/AdaptiveSecurity.lean`) is the adaptive game.
  It keeps a history of fresh challenges:
  - each fresh challenge below the cap prepends one entry, even when the ciphertext value repeats;
  - a challenge at the cap repeats the latest ciphertext;
  - with cap 0 and an empty history, every challenge returns `zeroBits`;
  - under CPA, `Dec` returns the refusal reply whatever the history.

## Published interfaces

Read every definition of another file through these published lemmas (policy §1, rule 10).

| Interface | Provider |
|---|---|
| `adaptiveIndImpl_dec_issued`, `_dec_other`, `_challenge_fresh`, `_challenge_encrypt`, `_challenge_full`, `_challenge_zero`, `adaptiveIndGame_eq`, `adaptiveINDSecure_iff`, `adaptiveIndGame_one`, `simulate_adaptiveIndImpl_one` | `PublicKey/AdaptiveSecurity.lean` |
| `indImpl_dec_cpa`, `indImpl_dec(_onSpec)`, `indImpl_challenge_none(_onSpec)`, `indImpl_challenge_repeat(_onSpec)`, `indSpec_eq`, `indSpec_dom/_rng`, `indSpec_decDom`, `indSpec_challengeDom/_Rng`, `inLens_*`, `outLens_*`, `indCodec_*`, `indGame_eq`, `INDSecure_iff` | `PublicKey/OracleSecurity.lean` |
| `ChallengeSim` (`chRun`, `firstQ`, their equations, `chRun_toCompOn_transport`, `expect_sample_*`, `expect_sub`) and `RecordHandler` (a worked `PolyHandler` with readers) | `PublicKey/OracleSecurity/` (from #288; reuse their patterns) |
| `Games.exists_interactiveHandlerMachine` (T2); `InteractiveHandler.input_eq`, `advInput_eq`, `call_eq`, `impl_apply`, `finInput_eq`, `finish_eq` | `Games/Efficiency.lean` |
| `Games.exists_advantage_hybrid_gap`, `advantage_eq`, `advantage_triangle`, `accept_eq` | `Games/Advantage.lean` |
| `Negligible.polyExpr_mul` | `Asymptotic/ReductionSupport.lean` |
| `prob_*`, `expect_*`, `sample_eq`, `Bridge.expect_sample_pair` | `Games/Probability.lean`, `Games/Bridges/Experiments.lean` |
| `simulate` equations, `OracleComp` laws, `NUPPT.toCompOn_eq`, `buildComp` cases, `bitCodec_*`, `decodeBitMove_*` | `Games/Simulate.lean`, `OracleComp.lean`, `Machines.lean`, `BitCodec.lean` |
| `NUPPT` run, coin and closure lemmas | `Complexity/Randomized/PPT.lean`, `NonUniform.lean`, `Closure.lean` |

`NUPPT.Coins`, `bitSpecAt`, `bitSpec`, `QueryImpl`, `OracleSpec.add` and `indSpec` are
abbreviations; `PolyExpr.eval` is notation. If a needed equation has no published reader, record
it in `REPORT.md` and use the escalation route below; do not unfold the foreign definition.

## Proof route and checkpoints

Gate 12's auditor confirmed this route. The docstring sketch is authoritative.

1. **Hybrids.** For `i ≤ cap(n)`, define `H_i` (a private game, or a family of oracle
   implementations) in which the first `i` fresh challenges encrypt the right message and later
   ones the left. Prove that `H_0` and `H_{cap(n)}` equal the `b = false` and `b = true` adaptive
   games. Read the cap semantics through the published equations. Send checkpoint 1.
2. **The reduction `B`.**
   - Build `B` through T2 with `perCall = 1` and `finCall = 0`. The handler state holds the
     fresh-challenge count, the latest ciphertext and the advised index `i⋆(n)`, placed in
     `InteractiveHandler.init`, which may be any function of `n`.
   - The seed is `cap(n)` encryption tapes.
   - The handler answers fresh challenges below `i⋆` with `Enc` of the right message and those
     above it with `Enc` of the left message, using `pk` and its own tapes. It forwards challenge
     `i⋆ + 1` to its outer `Challenge`, repeats the latest ciphertext past the cap, answers `Dec`
     with the refusal reply, and finishes with `A`'s bit.
   - Its run must be polynomial-time: `Enc` is uniform and polynomial-time.
   - **Codec alignment** is a known obligation: T2 states its simulation with
     `bitCodec (fun i => (din i).eval n) …`, while the games use `S.indCodec n`. Transport once,
     generically, as `chRun_toCompOn_transport` does.

   Send checkpoint 2.
3. **`B`'s game is `H_{i⋆+b}`.**
   - Prove that `B`'s single-challenge game with bit `b` has the same output distribution as
     `H_{i⋆(n)+b}`.
   - Independent seed tapes must reproduce the fresh-encryption distribution of the adaptive game.
     This includes branches that never reach challenge `i⋆ + 1`; there both sides agree.
   - Use T2's coin equivalence and the sampling identities.

   Send checkpoint 3.
4. **The bound.**
   - Apply `h` to `B` with the polynomial outer budget `q·perCall + finCall`.
   - With `exists_advantage_hybrid_gap` at `cap(n) > 0`, `A`'s advantage is at most
     `cap(n) · ε(n)`. Cap 0 gives advantage 0.
   - `Negligible.polyExpr_mul` with `cap` concludes.
   - Do not assume `n > 0`: a general scheme can have nonempty messages at `n = 0`.

   Send the final delivery.

Check: query budget 0, cap 0, repeated fresh ciphertext values, a run that never reaches
challenge `i⋆ + 1`, and the timeout output.

## Scope and proof discipline

- **Owned files.** Own `TCSlib/Cryptography/Encryption/PublicKey/AdaptiveCPA.lean`. Replace the one
  proof body and add helpers there. Generic helper modules are permitted under
  `TCSlib/Cryptography/Encryption/PublicKey/AdaptiveCPA/`, imported precisely by the owned file.
  Keep every file below 1000 lines.
- **Frozen.** Do not edit `BitwiseCPA.lean`, the `OracleSecurity/` helpers or any other existing
  file. If you need a lemma that belongs in an existing file, put it in your helper module and
  list it in `REPORT.md` as a promotion request.
- **Generic lemmas.** Put generic probability facts in a helper module and list them for promotion
  to `Games/Probability.lean` (duplication ledger DL-30). Do not copy existing lemmas; grep first.
- **Edits allowed.** You may edit the target's proof sketch to describe the delivered proof.
  Preserve the statement, every other declaration, the statement prose and the global simp
  attributes. Public helpers get a docstring with their formula, and a proof sketch when
  nontrivial (policy §3).
- **Reading definitions.** Use published readers for other files' definitions, in tactics and in
  term elaboration, including generated matchers and projections. For core and Mathlib, use their
  equation lemmas in `simp`, `rw` and `unfold`.
- **Escalation.** If the target appears false, or a required reader is missing with no clean
  route, write the exact failing obligation and the smallest proposed correction in `REPORT.md`,
  then push a checkpoint.

## Checks and report

- **Bootstrap.** Bootstrap from `order.txt` and the narrow `roots.txt`, following the environment
  addendum. Insert any new helper module before its consumer, and recalculate the roots if imports
  change. Check one module per `scripts/lean_check_tree.sh` invocation, with one Lean process per
  olean tree.
- **Sweep.** Recheck the owned modules, then sweep the supplied order. Compare `sorry` warnings with
  `base-sorries.txt`; the only change must be the removed `INDSecure.adaptive_cpa`.
- **Axioms.** Print the axioms of `adaptive_cpa` (expected: only `propext`, `Classical.choice`,
  `Quot.sound`). Also print those of `SingleBitSecure.bitwise_padded_adaptive_cpa` and
  `exists_adaptive_cpa`, and report exactly what they print. They still depend on the
  `bitwise-cpa` target.
- **Rule 10.**
  - Collect foreign references from the elaborated new proofs, including generated matcher and
    projection helpers.
  - Run an instance-aware seal of the touched declarations with the full candidate list.
  - Add controls that pass before sealing and fail after.
  - Run the explicit-unfold scan.
- **Lint.** Run `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography/Encryption/PublicKey --check8b`.
- **Report.** Give the issue base, the target's status, the exact changed files and sketch edits,
  the new declarations, any promotion or reader requests, and the resource, cache, bootstrap,
  sweep, axiom, seal and lint evidence.

**Ready to dispatch**
