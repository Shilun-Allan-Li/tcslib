# Gate 27 · Joint, length-generic multi-message security of special encryption (B1, statement)

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews).

- **PR:** draft [PR #311](https://github.com/Shilun-Allan-Li/tcslib/pull/311) at
  `46b780dc1b286f59da18e2d10f188b0faaab8088` (branch `stmt/pass-shelat-b1-multimsg`, tree
  `e4056622589640b722e43251359f6901d978b984`).
- **Target and base:** the PR targets `cryptography/pass-shelat-ch2-4` on base
  `013119f006af40d03b88b0fc2d9b453cf0a9b348` (the merge base). The two commits from the base to the records tip
  `41e3cd2a6b637ed10c6782b5f3c68212f9f77b65` (`b12a12f2`, `41e3cd2a`) touch records only: `PassShelatChapter5-8Plan.md`
  and the two evidence folders `maintainer/stmt-b1-2026-11-15/` and `maintainer/stmt-derand-2026-11-15/`. The diff
  `origin/cryptography/pass-shelat-ch2-4...46b780dc` equals `013119f0..46b780dc` byte for byte (`pr.diff.txt`).
- **Commits:** 1, by the maintainer (author Claude): `46b780dc` "B1 statement: joint, length-generic multi-message
  security of special encryption".
- **Scope:** a **statement audit**. It runs before any fill. Seyoon's ruling **B1** (2026-11-14) has the maintainer
  state, sorried and statement-gated, the joint, length-generic multi-message lemma that step 3 of
  `yaoHybrid_simulators` needs. The garbling unit `sc-garble` (U1) will prove it; the Yao unit `sc-yao` (U3) will use
  it. The PR also proves that the frozen `specialScheme_multiMessageSecure` (Claim 157.a (i)) follows from it, and adds
  three bridges for Yao.
- **Source:** [PS10] R. Pass and a. shelat, *A Course in Cryptography*, 3rd ed., January 2010: §6.2.2 (Algorithm 157.2,
  Claim 157.a, "it is easy to modify construction 99.1"), Definition 93.1 and Theorem 99.2; [LP09] for the
  one-inactive-key hybrid.

## What changed

The PR touches 2 Lean files (327 insertions, 0 deletions). Paths are under `TCSlib/Cryptography/`.

| File | Status | Lines | SHA-256 at head |
|---|---|---:|---|
| `SecureComputation/SpecialEncryptionMulti.lean` | new | 325 | `9644ca59…` |
| `SecureComputation.lean` (facade) | modified: one import and one `## Contents` line | 57 → 59 | `a31651a9…` |

Declarations of the new module (namespace `TCSlib.Cryptography.SecureComputation`): 11 public, 7 private.

| Declaration | Kind | Status |
|---|---|---|
| `sliceEnc G n o k r m` | `def` | `spEncStr (fun _ => ⟦G_k(r)⟧.drop o) ⟦k⟧ m ⟦r⟧`: Algorithm 157.2 with the pad `G_k(r)_{≥o}` |
| `sliceEnc_eq` | reader | `rfl` |
| `sliceEnc_eq_spEncStr` | bridge | proved: with an evaluator `E` of `G`, `sliceEnc = spEncStr (fun z => (E z).drop o)` |
| `sliceEnc_append_left` | bridge | proved: under `⟦G⟧ = ⟦G₁⟧ ++ ⟦G₂⟧`, offset `0` and `|m| ≤ n` give `spEncStr E₁` |
| `sliceEnc_append_right` | bridge | proved: offset `n + n` gives `spEncStr E₂`, every `m` |
| `sliceMultiEncDist G n q o len m` | `def` | the `encodeList` of the `q + 1` ciphertexts `sliceEnc G n o_i k r_i ⟦m_i⟧`, seed `(k, r)` |
| `sliceMultiEncDist_apply` | reader | `rfl` |
| `SliceMultiMessageSecure G` | `def` (Prop) | `∀ D q, ∃ ε, Negligible ε ∧ ∀ n o len, (∀ i, o_i + n + len_i ≤ L n) → ∀ m m', distAdv … ≤ ε n` |
| `sliceMultiMessageSecure_iff` | reader | `Iff.rfl` |
| **`sliceMultiMessageSecure_of_prfOut`** | theorem | **stated; the only `sorry`**: `PRFOut ℓ G → SliceMultiMessageSecure G` |
| `specialScheme_multiMessageSecure_of_joint` | theorem | proved: `SliceMultiMessageSecure G → (specialScheme G E hE hGE).MultiMessageSecure` |

The private declarations are the corollary's helpers (`specialScheme_gen_runAt`, `specialScheme_enc_runAt`,
`specialKeyEq`, `ofFn_specialKeyEq`, `specialNonceEq`, `ofFn_specialNonceEq`) and `zipWith_xor_append_of_le`.

The target:

```lean
theorem sliceMultiMessageSecure_of_prfOut {ℓ : PolyExpr}
    {G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (ℓ.eval n) → Bool)} (hG : PRFOut ℓ G) :
    SliceMultiMessageSecure G
```

with

```lean
def SliceMultiMessageSecure {L : ℕ → ℕ}
    (G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L n) → Bool)) : Prop :=
  ∀ (D : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ n (o len : Fin (q.eval n + 1) → ℕ), (∀ i, o i + n + len i ≤ L n) →
      ∀ m m' : ∀ i, Fin (len i) → Bool,
        distAdv (sliceMultiEncDist G n (q.eval n) o len m)
          (sliceMultiEncDist G n (q.eval n) o len m') (D.distinguisherL n) ≤ ε n
```

The maintainer's design choices, disclosed in the PR description for this gate:
1. **Slices are chosen after `ε`.** This is stronger than the frozen wording of Claim 157.a (i), which has no slices;
   Yao needs it because its reductions take the slices from advice.
2. **The fit hypothesis `o_i + n + len_i ≤ L(n)`** is kept, so that every pad lies inside `G_k(r_i)`.
3. **General `L`.** The definitions take any `L : ℕ → ℕ`; only the target fixes `L = ℓ.eval`. The corollary uses
   `(.add .var .var).eval n ≡ n + n`, matching the frozen `PRFOut (.add .var .var) G`.
4. **Statement only, existing definitions only** (`PRFOut`, `spEncStr`, `encodeList`, `distAdv`,
   `NUPPT.distinguisherL`). The proof needs the ℓ-output PRF machinery of job `prf-long` (ruling B3).
5. **The bridges are in this PR**, so that Yao's step 3 can instantiate the lemma at `G₁ ‖ G₂` under `hG₁₂` without
   reading `sliceEnc` or `spEncStr`.

## Rulings and records in force

- **B1 (Seyoon, 2026-11-14; decision log row "Next fills chosen"):** the joint, length-generic multi-message lemma that
  `yaoHybrid_simulators` needs is stated first by the maintainer in a sorried statement PR with its own gate, proved by
  the garbling unit, used by Yao. The analysis is `maintainer/securecomp-plan-2026-11-14/plan.md` §3 (B1, option (A)
  recommended and ruled), §2 (`yaoHybrid_simulators`, "well-posed: yes, modulo B1") and §4 (U1 owns
  `SpecialEncryptionSecurity.lean` and may add `SpecialEncryptionMulti.lean`).
- **B3 (Seyoon, 2026-11-14):** the PRF machinery is generalized to ℓ-bit outputs first, in a separate job `prf-long`
  (frozen `FromPRF` files, own gate), not duplicated. The plan's recommendation (accept as debt) was not taken.
- **B2 (brief-level, no ruling):** `sc-garble`'s brief must require a stronger published garbling bound. Not part of
  this PR.
- **Order (same row):** `sc-ot`, `sc-compose` (and the five single units) first; then the B1 statement PR and
  `prf-long`; then `sc-garble`; then `sc-yao`.
- **Decision log row 2026-11-15 "B1 statement PR"** records this PR, its evidence `b3b554d6` and the four design
  choices.
- **Standing rules:** Rule 10 (no proof reads another file's definition except through published readers, with the
  projection-coercion and abbreviation-notation lessons of 2026-11-14); formula docstrings with `[PS10 …]` tags and a
  `**Proof sketch.**` for every nontrivial proof (policy §§2–3); the #305 facade rule (a facade imports and lists every
  child module); lint baseline **92 FAIL / 101 WARN** on `TCSlib/Cryptography` with no new line; lines of at most 100
  characters.

## What is frozen

Every file other than the new module and the facade's import and `## Contents` lines. In particular
`SecureComputation/SpecialEncryptionSecurity.lean` (`PRFOut`, `specialScheme`, the frozen
`specialScheme_multiMessageSecure`), `SpecialEncryption.lean` (`spEncStr`), `GarblingSpecial.lean` (`nestedSpecial`,
`innerLen`), `Yao.lean` (`yaoHybrid_simulators` and its hypotheses `hG₁`, `hG₂`, `hG₁₂`) and every `FromPRF*` file are
byte-identical to the base (check with `pr.diff.txt`). `specialScheme_multiMessageSecure` stays an admitted target of
`sc-garble`; this PR does not change its statement or its body.

## Questions for the audit

1. **Does the statement say what Yao step 3 needs?** Read `yaoHybrid_simulators` (`Yao.lean`, its docstring step 3)
   with `nestedSpecial` (`GarblingSpecial.lean`).
   - In `H₂,ᵢ → H₂,ᵢ₊₁` the reduction embeds the rows of gate `i` under one inactive key `ι_u`. Those rows are outer
     (`G₂`, message length `innerLen = 4n + 2`) where `u` is a first argument and inner (`G₁`, `n`-bit messages) where
     it is a second or only argument, and `ι_u` keys the rows of every gate that reads `u`. Do the per-ciphertext
     slices `(0, n)` and `(2n, 4n + 2)` of `G = G₁ ‖ G₂`, with `L(n) = 2n + (n + (4n + 2))`, cover every row the
     reduction must obtain from its challenge, including rows whose plaintexts agree in both worlds?
   - Is the statement non-adaptive enough to be true, yet adaptive enough for Yao? The messages are fixed per `n`
     (advice). Can a plaintext of a challenge row ever depend on a challenge ciphertext? Consider a two-key row whose
     inner key is also `ι_u`; note `DAGCircuit.IsWellFormed` (`g.args.Nodup`) and `YaoCircuit.outs_sink`.
   - Are the hypotheses usable from `yaoHybrid_simulators` exactly: `hG₁₂ : PRFOut (.add (.add .var .var) (.add .var
     innerLen)) (fun n s x => Fin.append (G₁ n s x) (G₂ n s x))`, `hGE₁`, `hGE₂`? The probe `yao_step3_instance`
     checks this with exactly those hypotheses; is anything else Yao needs (the count `q`, the encoding of the
     challenge by `encodeList`, the input `1^n`, the coins of `nestedSpecial` as two independent nonces) missing or
     mismatched?
2. **Is it true as stated?** Check the quantifier order: `ε` is chosen after `D` and `q` and before `n`, the slices and
   the messages.
   - For fixed `n` there are finitely many fitting slice vectors and message pairs (each `o_i, len_i ≤ L(n)`), so a
     pointwise maximum `A(n)` exists. Is `A` negligible? Check the sketch: the advice-taking oracle machines `D_0`,
     `D_1` (maximizing slices and one message vector each, polynomial advice), the PRF step with `q(n) + 1` queries of
     `ℓ(n)`-bit answers, and the collision bound `C(q(n) + 1, 2) · 2^{-n}` (`MultiMsg.negligible_choose_div_two_pow`).
   - In the random-function world, is every ciphertext `⟨r_i, u_i⟩` with `u_i` uniform of length `n + len_i` off the
     collision event, given that within one ciphertext the revealed prefix `[o_i, o_i + n)` and the mask
     `[o_i + n, o_i + n + len_i)` are disjoint bits of one answer, but different ciphertexts with the same nonce share
     the answer?
   - Edge cases: `n = 0`; `ℓ(n) < n` (no slice fits; vacuous); `len_i = 0`; `q(n) = 0`.
3. **Is the fit hypothesis right?** Without it, `List.zipWith` and `List.take` truncate short pads silently. Is the
   statement with the fit exactly what both consumers can discharge (`0 + n + n ≤ 2n` for the corollary; `0 + n + n ≤
   7n + 2` and `2n + n + (4n + 2) = 7n + 2` for Yao)? Is the hypothesis too strong or too weak anywhere?
4. **Is the general `L` sound?** The definitions are stated for any `L : ℕ → ℕ`; only the target fixes `L = ℓ.eval`.
   Check that this introduces no unintended instance (the corollary at `L n = n + n`, the probe at
   `L n = (PolyExpr.add …).eval n`) and that the elaborated `L` of the target and of `frozen_from_joint` is the
   intended one (implicit-argument unification through `Fin (ℓ.eval n)`).
5. **Does the frozen corollary follow?** `specialScheme_multiMessageSecure_of_joint` is proved. Does it state the frozen
   claim's conclusion exactly, so that `specialScheme_multiMessageSecure G E hE hGE hG` is
   `specialScheme_multiMessageSecure_of_joint G E hE hGE (sliceMultiMessageSecure_of_prfOut hG)` (probe
   `frozen_from_joint`)? Is the coin relabelling (`specialKeyEq`, `specialNonceEq`, `acceptProb_comp_equiv`) sound?
6. **Readers and bridges.** Are `sliceEnc_eq`, `sliceMultiEncDist_apply` and `sliceMultiMessageSecure_iff` exact
   definitional readers, public, not `@[simp]`, each with its formula? Are the three bridges correct and sufficient for
   the two layers, including the length side condition `|m| ≤ n` of `sliceEnc_append_left`? Are they and the corollary
   Rule-10 clean (they read `spEncStr` only through `spEncStr_eq`, and `specialScheme` only through its `@[simps]`
   equations and published `runAt` lemmas)?
7. **Is anything missing for the prover (`sc-garble`)?** Name any reader, bridge or published lemma the fill will need
   that this PR should add now, for example a reader of `OracleEnsemble.keyed`/`random` at ℓ-bit outputs, a slice
   form of the oracle sampler, or anything `prf-long` must publish (and whether that dependency is stated in the
   records precisely enough for the `prf-long` brief).
8. **Duplication.** Compare with `prfScheme_multiMessageSecure` (`Encryption/PrivateKey/FromPRF.lean`),
   `PrivateKeyScheme.MultiMessageSecure` and `specialScheme_multiMessageSecure`. Is `SliceMultiMessageSecure` a
   justified new notion rather than a duplicate?
9. **Placement, imports, facade exports, docstrings.** Policy §§1–3: a new module beside
   `SpecialEncryptionSecurity.lean` (importing only it), listed in the facade; module docstring with `## Main
   definitions`, `## Main results`, `## References`; `[PS10 …]` tags and formulas on every public declaration; the
   target's and the corollary's `**Proof sketch.**`.

## Known dispositions (not findings)

- **The facade edit** (one import, one `## Contents` line) is the #305 facade rule, not a frozen-file change.
- **The proof of the target is out of scope.** It is assigned to `sc-garble` and depends on `prf-long` (B3). The gate
  asks only whether the statement is true, provable on the sketched route and sufficient.
- **The lint run** used `campaign_style_lint.py TCSlib/Cryptography` without the opt-in `--check8b`. Check 8b concerns
  structure-valued definitions; the new definitions are a `List Bool`-valued function, a sampler and a `Prop`. The
  derand-host PR (Gate 28) ran with `--check8b` and had the same 92/101 on `TCSlib/Cryptography`.
- **The PR description on GitHub** is an edited version of the evidence ZIP's `pr-body.md`; the evidence
  `PROVENANCE.txt` still calls it "draft PR description (not opened)". The PR was opened after the evidence was
  packed. The statement under audit is the Lean at the head.

### Slip noted by the staging (please rate)

- The target's docstring says of the two Yao slices "Both fit exactly". The outer slice `(2n, 4n + 2)` fits exactly
  (`2n + n + (4n + 2) = 7n + 2 = L(n)`); the inner slice `(0, n)` uses `2n` of the `7n + 2` bits. The evidence
  `PROVENANCE.txt` says "both shapes fit (the second exactly)".

## Also check

- The `sorry` is the only one in the PR, at `SpecialEncryptionMulti.lean:231` (`sliceMultiMessageSecure_of_prfOut`),
  and no other declaration depends on `sorryAx` except through it (`evidence/probe-runs/StmtB1Probe.log`).
- Every line of the two files is at most 100 characters (`source-head.json`: 0 over-width lines).
- The module imports only `SecureComputation.SpecialEncryptionSecurity`; nothing imports the new module except the
  facade (consumers will import it later).
- `set_option maxHeartbeats 0` at the top of the new module follows the neighbouring files; say if it should not.

## Evidence

`verification.zip` (28 entries; its `SHA256SUMS` lists every other entry, `PROVENANCE.txt` maps each to its source)
holds byte-identical originals from records `41e3cd2a`:
- `stmt-b1-evidence.zip` (SHA-256 `b3b554d6…`, 135 entries: 14 directories and 121 files = the 120 manifest paths under
  `stmt-b1/` plus that folder's `SHA256SUMS`, byte-identical to the manifest) and its manifest `evidence-SHA256SUMS`;
- `records/`: the evidence's `PROVENANCE.txt` (as beside the ZIP), the decision log, the secure-computation plan and
  the duplication ledger;
- `evidence/`: byte copies of the ZIP entries cited here:
  - `build/head-summary.tsv`, `order/build-head.txt`, `logs/head/*.log` (4 of the 63): the build at the head, one module
    at a time, imports first, 63 modules (the change's downstream since the olean base `eff2dcd0`, through root
    `TCSlib` and `audits/pass-shelat/Checks`), all rc 0 and 0 errors; the only `sorry` warning is
    `SpecialEncryptionMulti.lean:231`;
  - `build/restore-summary.tsv`, `tree/snapshot-pre.txt`, `restore/snapshot-post.txt`: the olean tree restored
    byte-identically (SHA-256 `457ba704…` before and after);
  - `probe-sources/StmtB1Probe.lean`, `probe-runs/StmtB1Probe.log`: (A) the bridges and the corollary re-elaborated
    with `spEncStr`, `specialScheme`, `sliceEnc`, `sliceMultiEncDist`, `SliceMultiMessageSecure`, the
    `PrivateKeyScheme` multi-message definitions, `distAdv`, `acceptProb`, the `NUPPT` coin and run definitions,
    `PolyExpr.eval` and `pairEncode` sealed; (B) `frozen_from_joint` and `yao_step3_instance`; (C) two sealed controls
    that read `sliceEnc` and `spEncStr` through their bodies, the only two errors of the run (lines 247 and 252);
    (D) `#print axioms`;
  - `probe-sources/StmtB1Control.lean`, `probe-runs/StmtB1Control.log`: the two controls unsealed, rc 0;
  - `lint/failwarn.diff` (empty: FAIL and WARN lines identical at base and head) and `lint/lint-full.diff` (only the new
    module's INFO line, the facade's line count and the file total);
  - `patches/COMMITS.tsv`, `patches/changed-files.txt`, `PROVENANCE.txt`, `pr-body.md`.

Also: `pr.diff.txt` (2 paths, 327/0), `source-head.json` (hashes, line counts, over-width counts of the 2 files) and
`sources.zip` (the import closure at the head of both changed modules, 145 files).

## Findings delivery

Return `gate27-b1-multimsg-findings.md` as a Markdown file in this chat. If you have several evidence files, return a
ZIP. The user dispatches and merges.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

**Severities**
- **blocker:** a false or unusable statement, or a scope violation (a frozen file changed).
- **major:** a missing or wrong hypothesis, a statement too weak or too strong for its consumers (Yao step 3, the
  frozen corollary, the `sc-garble` proof route), a forbidden read in a proved declaration, a duplicate public result,
  or necessary evidence that cannot be verified.
- **minor:** documentation or API defects, including an inaccurate formula docstring or proof sketch.
- **note:** anything else.

Report the audited head and the counts by severity. The gate closes at zero blockers and zero majors.
