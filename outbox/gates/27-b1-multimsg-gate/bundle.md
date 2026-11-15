## ===== briefs/pass-shelat-ch5-8/gates/27-b1-multimsg/pack.md =====

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

## ===== policy.md =====

# TCSlib Contribution Policy

Standards for all Lean contributions to this repository, whether written by humans or by
agents. This document covers three things: **modularity** (how code is organized),
**attribution** (how every result is traced to a source), and **proof sketches** (how every
formal proof is accompanied by readable mathematics).

It complements, and does not replace:

- `workflow.md` — the campaign formalization process (phases, audit gates, fill epochs)
  that produces code meeting these standards.
- `.github/copilot-instructions.md` — build workflows, import rules, CI integration points.
- `AGENTS.md` / `.claude/CLAUDE.md` — the sorry-ladder proof workflow and agent roster.
- `blueprint/BLUEPRINT_PIPELINE.md` — how blueprint entries are generated and validated.

Where this document names an existing mechanism (blueprint macros, hygiene scripts), the
policy is to *use that mechanism*, not to invent a parallel one.

## 1. Modularity

**Layout.** Content lives at `TCSlib/<Area>/<Topic>/<Piece>.lean`, one coherent concept or
lemma cluster per file, with a facade file `TCSlib/<Area>/<Topic>.lean` that imports every
child and carries a `/-! -/` module docstring with a `## Contents` list (one line per child).
See `TCSlib/Complexity/NPReductions.lean` for the reference example.

**File size.** Target 150–600 lines per math file. A file approaching 1000 lines should be
split unless there is a positive reason not to (e.g. a single long proof that cannot be
usefully decomposed).

**Exports.** Every new topic facade must be imported from `TCSlib.lean`. CI only builds what
is reachable from `TCSlib.lean`; an unexported file is invisible to CI, docs, and the
blueprint.

**Imports.** Precise module imports only. A bare `import Mathlib` fails CI. Import only what
the file uses.

**Namespaces.** Namespaces are area-local: pick one namespace root per topic and use it
consistently within that topic. Do not leak auxiliary definitions into the root namespace;
mark internal helpers `private` or put them in a dedicated inner namespace.
*Model registry exception*: a model-defining **type** (a machine, circuit, formula, or
decision-tree model) may live at the root namespace, Mathlib-style, provided it is
registered in the catalog facade `TCSlib/ComputationalModels.lean`; its operations and
lemmas still live in the type's own namespace. Anything else at root is a leak.

**Layering.** Keep definition files separate from heavyweight theorem files, so that
downstream work can import a model or a class definition without pulling in every proof about
it. When a development has both a "raw/general" layer and a "bundled" layer (e.g. a machine
model that is parametric in its types, plus a bundled version carrying finiteness instances),
headline definitions and theorems are stated against the bundled layer; the raw layer is
internal plumbing.

**Helpers.** Foundational helper lemmas that serve a whole area belong in that area's
`Basic.lean`, not in the file that first needed them.

**Definitions land with their lemmas** (user, 2026-10-16). Every new public `def` is published,
in the same PR and beside the definition, with the lemmas that let a consumer read it without
unfolding:
- a structure-valued definition (a contract, a configuration, zone contents): its field
  equations, generated by `simps` with `(config := { isSimp := false })` and explicit
  projections (`simps!` where the body is another constructor's result);
- any other definition: an equation lemma `<name>_eq` (by `rfl` where that holds), or case
  lemmas that together cover every input (`_of_lt`/`_of_le`, `_true`/`_false`, one per
  constructor);
- a predicate: an `_iff` characterization;
- a machine: its run or contract lemma, the only way consumers read a machine.

None carries `@[simp]` unless a gate approves it, and each docstring states its formula. Consumers
never unfold another file's definition (the no-unfolding rule of the briefs, user 2026-10-16). The
rule binds TCSlib's own definitions: core and Mathlib definitions may reduce in a `rfl`, `decide`
or `show` step, but are never passed to `simp`, `rw` or `unfold`; use their equation lemmas
(`Bool.toNat_true`, not `simp [Bool.toNat]`) (user, 2026-10-23).
**Reducible abbreviations are notation** (user, 2026-10-26). Lean unfolds a TCSlib `abbrev` (such
as `Turing.Cfg.Halted`, `cfg.state = none`) at every step, and the standard seal cannot cover it:
under Lean's default reducibility validation, `attribute [local irreducible]` fails on a reducible
declaration (only the unsafe override `set_option allowUnsafeReducibility true`, which the
campaign's seals do not use, lifts the check). So reading an abbreviation through its body,
for example `¬ c.Halted` as `c.state ≠ none`, is allowed and is not a definitional closure. A
consumer names it in `simp`, `rw` or `unfold` only through a published lemma where one exists, and
a new public `abbrev` still lands with its `_iff` or `_eq` lemma.
They read the machine model's primitives (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
`Cfg.mapState`) through the existing lemmas. The style lint's check 8 reports, per file, every
public `def` with no lemma named after it and no `simps` attribute, so a head-against-base diff
of the lint shows any new definition that lacks one. Definitions that predate the rule are listed
by the same check and covered as consumers need them.

**Construction reuse.** Machines are built from the verified construction layers, not from
scratch: the combinators and routine catalog of `TCSlib/Complexity/TuringMachine/Build/`
(conventions, wrappers, loops, primitives, embeddings, seams, and the catalog rows —
`machine-library-design.md` is the registry), the registered hosts (**Hosts come first**,
below), and the program layers (`LogProg.ARM`, `CounterProg`, and the general programming
layer of `machine-library-design.md` §15 once it lands) where a program-level description
suffices. Before writing a transition
table by hand, check the registry; a routine that exists is cited, not re-derived. A routine
that *almost* exists is the interesting case: do not write a third private variant — either
consume the general form, or commission the missing form into the shared layer (during a
fill batch: a `private` local copy plus a "requested shared lemma" in the report, promoted
at the next shared-file window). A hand-built machine is acceptable only when no layer
covers the need, and its docstring must say so and name what was missing — that sentence is
what turns the gap into the next catalog row. The chapter-1/2 files that predate this layer
re-derived the same bank/relocation/dispatch/frame families four times over (`emitterBank*`,
`clBank*`, `clSlot*`, …); the retrofit paying that debt back is the standing cautionary
tale. The same discipline applies to circuit construction once `CircuitComplexity`'s gadget
layer exists: gadgets, wiring combinators, and size/depth ledgers get one shared home and a
registry, and new circuits are assembled from it.

**Hosts come first.** A *host* is a control structure that drives other routines rather than
computing one value: a search or traversal (BFS, DFS, backtracking, an odometer over
assignments), a recursion or evaluation scheme (AND/OR evaluation, Savitch's midpoint
recursion), an interpreter or simulation step block, a clocked or windowed runner, a dispatcher
over a data structure (tables, records), or an input device. Any routine whose natural contract
does not depend on its first consumer counts as a host; leaf rows (copy, compare, seek,
arithmetic) do not. **A host is never built `private` inside the proof that first needs it.**
Its public contract is designed, statement-gated and placed in the shared construction layer
first, generic in the parts its consumers vary (the leaf test, the step relation, the data
domain), with time and space (head-envelope) clauses. Consumers cite it, under the campaign's
proved-modulo rule while its own fill is still running. The host registry is
`machine-library-design.md` §14. A private host already in the tree is harvested into the
shared layer before a second consumer is briefed against it. The rule exists because private
hosts were the main way the library overfitted to single proofs: four configuration encodings,
three reachability notions and a private search host per theorem, each to be re-derived by the
next consumer (assessment of 2026-10-12, recorded in the design document). (User, binding,
2026-10-12.)

**Duplication.** Some duplication is mechanically forced by the campaign discipline —
exclusive file ownership, the statement freeze, and `private` visibility leave a fill batch
no other legal way to use another file's unexported machinery — and occasionally it is the
right engineering call. It is never silently acceptable: **every instance of duplicated
proved material must be human-approved.** A fill batch discloses each copy in its report;
the maintainer's integration ledger totals copied material per file (`workflow.md` §4); and
the audit template treats accumulated duplication as a major finding that a gate cannot
close over without the human maintainer explicitly accepting the debt and naming where and
when it is paid back (the registry's dedup/refactor queue). Duplication that was never
disclosed is a freeze violation, not debt.

**File header.** Every math file begins with the Mathlib-style copyright block, its imports,
the repo-standard options

```
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
```

then a module docstring containing `# Title`, `## Main definitions`, `## Main results`, and
`## References` (see §2).

## 2. Attribution

Every mathematical statement in the library must be traceable to a source, at the level of
precision of a textbook theorem number or a paper section.

**File-level.** Every math file's module docstring contains a `## References` section giving
full citations with short tags, e.g.

```
## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
```

**Declaration-level.** Every definition, theorem, and lemma that corresponds to a result in
a source carries the tag with a precise location in its docstring: `[AB09, Claim 1.6]`,
`[AB09, §1.7]`, `[GRS25, Thm 4.2.1]`. Purely technical glue lemmas with no textbook
counterpart may omit the tag; anything a reader would recognize as "a result" may not.

**Deviations.** If the formal statement deviates from the source — different constants,
strengthened or weakened hypotheses, a reformulation — the docstring must say so and briefly
say why (e.g. "stated with explicit constant 5k rather than O(·), following the proof").

**Statement prose.** Every public declaration's docstring begins with a natural-language
statement of what it asserts (for a definition: what it is), precise enough that a reader
could judge the formalization's fidelity without parsing the Lean. The `[Tag, location]`
citation and any deviation note attach to that statement; the proof sketch (§3) follows it.
A bare label ("Unfolding lemma", "Helper for X") is not a statement. Instances are exempt,
as are vendored files (which follow upstream style). `private` declarations should carry
docstrings too, but at reviewer discretion rather than as a hard requirement. The blueprint
remains the cross-referenced informal layer for dependency structure (see **Blueprint**);
the docstring statement is what external audits compare blind restatements against, so it
is part of the trusted surface.

**Blueprint.** When an ingested reference exists under `blueprint/src/references/`, blueprint
entries use `\statementsource{<ref>}{<anchor>}` and `\proofsource{<ref>}{<anchor>}` to cite
it, subject to the existing rule that these are written only after an approved proofmatch
run. When starting a new chapter or paper, ingest it as a reference pair
(`<name>.raw.md` + `<name>.md`) so these citations are possible: put the PDF under
`blueprint/src/references/` in the change that formalizes it and run
`python3 scripts/dataset_pipeline.py --yes`, which ingests it, matches every text the
blueprint does not cite yet, and carries the new statements into the dataset
(`python3 scripts/sources.py add TAG=<pdf or md>` does the ingest and match alone, with
the docstring tag above; `python3 scripts/sources.py` shows which texts are attached and
which are still missing; see `dataset/INSTRUCTIONS.md`). The dataset builder does not
search outside that directory for sources; an unattached text leaves the theorems with
informalized proof notes instead of citations.

**Vendored code.** Lean code adapted from another project keeps the original copyright
header and license notice, and its file docstring names the source project, the commit it
was taken from, and a summary of local modifications.

**Design adaptation.** When a construction, proof architecture, or module design is
adapted from — or materially inspired by — another project's code, the debt is cited even
when no code is transcribed. The module docstring's `## References` section names the
source project, author, module or archive entry, the commit or version consulted, and its
license, with a short tag usable at declaration level; the precedent is
`TuringMachine/Composition.lean`'s `[Balbach22]` for the Isabelle AFP `Cook_Levin`
composition-combinator architecture. Design documents and blueprint entries built on the
adapted design carry the same citation. Examining external code purely for comparison,
with nothing taken, creates no citation duty, but on a campaign it belongs in the
campaign's records (plan decision log or backlog) so the provenance question is answerable
later. (Maintainer guideline, binding, 2026-10-06.)

## 3. Proof sketches

Every nontrivial formal proof is accompanied by a human-readable English proof sketch, kept
next to the Lean it describes.

**What counts as nontrivial.** Rule of thumb: any proof longer than ~20 lines of tactics, or
that would rate difficulty ≥ 3 on the blueprint scale. One-line `simp`/`omega`/`exact`
proofs need no sketch.

**Where sketches live.** In the Lean file itself:

- For most theorems: a `**Proof sketch.**` paragraph at the end of the theorem's docstring,
  written in mathematical English (not Lean identifiers), naming the key intermediate steps.
- For long proofs: additionally, short comments at the major `have`/section boundaries tying
  the tactics back to the sketch's steps.

The named intermediate steps of a sketch should be visible in the formalization as `have`s
or standalone lemmas — if the sketch says "first reduce to the one-tape case", there should
be a lemma that is that reduction.

**Where sketches do not live.** Not in the blueprint. Blueprint statement entries state
claims only; `scripts/dataset_hygiene.py --strict` hard-fails on proof content there. The
blueprint records *what* is true and its dependency structure; the Lean docstrings record
*why* it is true.

**Sketches and the sorry ladder.** When landing a sorry-skeleton, write the sketch at
skeleton time — the sketch *is* the plan, and each `sorry` should correspond to a named step
of it. A skeleton whose sketch cannot be written is not ready to land.

**Synchronization.** When a proof strategy changes, the sketch changes in the same commit.
A sketch that describes a proof the code no longer performs is worse than no sketch.

## Review checklist

Before merging new Lean content, check:

1. Files follow the Area/Topic layout with a facade, and `TCSlib.lean` exports are updated.
2. Imports are precise; no bare `import Mathlib`.
3. Every file has a `## References` section; every source-derived declaration has a
   `[Tag, location]` in its docstring; deviations from sources are noted.
4. Every nontrivial proof (or sorry-stub standing in for one) has a proof sketch.
5. Every public declaration (instances and vendored files excepted) has a docstring
   opening with a natural-language statement of what it asserts
   (`python3 scripts/style_lint.py` checks presence mechanically; statement quality is
   review judgment).
6. `zsh scripts/lean_check.sh <file>` reports zero errors for each touched file.
7. If blueprint content was touched: `python3 scripts/blueprint_validate.py --strict` and
   `python3 scripts/dataset_hygiene.py --strict` pass.
8. No new private host: every search, recursion, interpreter, runner or input device the
   change introduces is a registered public host, or cites one (§1, **Hosts come first**).

## ===== briefs/pass-shelat-ch5-8/maintainer/securecomp-plan-2026-11-14/plan.md =====

# Secure-computation admissions: analysis and proposed unit split

Read-only analysis. Branch `cryptography/pass-shelat-ch2-4` at
`58a061c98ef07e50a57f2a1a2d24485d24aac803` (fetched 2026-11-14; local = origin). No Lean was run,
nothing was staged, committed or pushed. Line counts and estimates come from reading the source.
The sizes are estimates, not measurements.

Source: `Pass–Shelat.pdf` at the root of the records branch (book page = PDF page − 12). Pages
156–164 were read (Alg 157.2, §6.2.3, Prot 160.4, Prop 161.5, Prot 162.6, Thm 163.7). The
"Claim 157.a" and "Claim 159.a" labels are the inventory's names for unnumbered claims in the
text of §6.2.2–6.2.3.

## 0. Census and corrections to the brief

**Admissions: 13 `sorry`s in 6 files.** The brief lists 13 declarations, and all 13 are confirmed.

| File | Lines | Admitted |
|---|---|---|
| `ObliviousTransfer.lean` | 671 | `otProtocol_simulators` (:639), `otProtocol_polyTime` (:656) |
| `SpecialEncryptionSecurity.lean` | 157 | `specialScheme_multiMessageSecure` (:115), `spDecStr_wrongKey` (:137), `specialScheme_wrongKey` (:155) |
| `Garbling.lean` | 427 | `uprob_not_good_le` (:425) |
| `GarblingSecurity.lean` | 87 | `nestedSpecial_wrongKeyBot` (:69) |
| `Yao.lean` | 942 | `yaoSeed_good_whp` (:820), `yaoHybrid_polyTime` (:843), `yaoHybrid_simulators` (:918) |
| `ComposeSecurity.lean` | 382 | `composeP_efficient` (:296), `composeV_efficient` (:305), `hbcSecure_compose` (:378) |

**`YaoReal.lean` has no admission.** Its only "sorry" match is module-docstring prose at line 43
("resting on their `sorry`s"). `yaoProtocol_hbcSecure` is a closed term built from
`hbcSecure_compose`, `yaoHybrid_hbcSecure` and `otProtocol_hbcSecure`.

**G3-8 is not pending.** It was ruled (A) by the user on 2026-11-05 (decision log row 268; QUEUE.md
:127, "ruled (A)"). It was applied in prong B commit `587843c76f95f10056c9ddc9174da9dc8fba8b54`
(row 272). `EnhancedHardCore` is already a hypothesis of the frozen `otProtocol_simulators`,
`otProtocol_hbcSecure` and `yaoProtocol_hbcSecure`. Gate 06B closed PASS (row 467), and the
internal review `maintainer/gate06-integration-2026-11-06/review-B.md` confirms the hypothesis is
still necessary. So G3-8 does not block OT. One residual point concerns the Implications layer
only: no collection in the library is proved to have an `EnhancedHardCore` predicate. Its only
consumers are `ObliviousTransfer.lean` and `YaoReal.lean`. That limits how the real Yao theorem
can be used, not whether it can be proved.

**Leaf admissions.** No other declaration's code uses `specialScheme_multiMessageSecure`,
`specialScheme_wrongKey` or `yaoSeed_good_whp`. The proved `garbling_good_whp` is also unused.
`yaoSeed_good_whp` appears only in the sketch of `yaoHybrid_simulators`.

## 1. Dependency graph

**Import graph** (within `SecureComputation/`):

```
Defs ─┬─ ObliviousTransfer (+ Asymptotic/Collections) ─────────────┐
      └─ Hybrid ─┬─ Compose ─ ComposePhases ─ ComposeSecurity ─────┤
                 └──────────────────────────┐                      ├─ YaoReal
SpecialEncryption ─┬─ SpecialEncryptionSecurity (+FromPRG, GGM) ─┐ │
Garbling ──────────┴─ GarblingSpecial ─────── GarblingSecurity ──┴─ Yao
```

No module outside `SecureComputation/` imports these files, apart from the facade
`SecureComputation.lean`.

**Proof-route graph.** `→` means "is used by the proof of".

- `otProtocol_polyTime`, `otProtocol_simulators` → `otProtocol_hbcSecure` → `yaoProtocol_hbcSecure`
- `composeP_efficient`, `composeV_efficient` → `polyTime_compose` → (sketch) `hbcSecure_compose` → `yaoProtocol_hbcSecure`
- `spDecStr_wrongKey` → `nestedSpecial_wrongKeyBot` → `garbling_good_whp` (proved, unused)
- `spDecStr_wrongKey` → `specialScheme_wrongKey` (leaf; sketch: reduces to `ℓ = n`)
- `uprob_not_good_le` → `garbling_good_whp`
- `nestedSpecial_wrongKeyBot` + (a generalized) `uprob_not_good_le` → `yaoSeed_good_whp` (sketch)
- `yaoSeed_good_whp` → `yaoHybrid_simulators` (sketch: steps 1 and 3, `Bad`) → `yaoHybrid_hbcSecure`
- `yaoHybrid_polyTime` → `yaoHybrid_hbcSecure`
- `specialScheme_multiMessageSecure` → **nothing as frozen**. The simulators' step 3 needs a
  joint, length-generic variant that is not yet stated (§3, B1).

**Does `hbcSecure_compose` need Yao or OT?** No. It is generic in `G`, `F`, `H` and `ρ`, and it
imports only `ComposePhases`. Yao and OT meet only in `YaoReal`. The OT file is independent of
every other admission, on both the import graph and the proof route.

## 2. Per-declaration analysis

Size: S < 300 lines, M 300–1000, L > 1000 (proof plus the helpers it needs).

### 2.1 `otProtocol_polyTime` (`ObliviousTransfer.lean`:656)

1. **Statement.** `otFunctionality.PolyTime (otProtocol T H)` given `hH : PolyTimeComputable H`:
   both strategies are `Strategy.Efficient`, and the messages of honest runs are bounded by a
   polynomial. Ref.: [PS10, Def 155.1] efficiency clause (ruling of 2026-11-05), for Prot 160.4.
2. **Dependencies.** None among the admissions. Used by `otProtocol_hbcSecure`.
3. **Well-posed.** Yes. `Strategy.Efficient` quantifies over all `x z r hist`. The next-message
   functions branch only on `hist.length`, and they use `T.gen`/`T.sample`/`T.inv` (uniform
   NUPPTs, so `runAtL` on arbitrary tapes is poly-time), `T.eval` (`eval_poly` is a field of
   `Collection`), `H` and `List.replicate (inv.coins.eval n)`. The message bound covers the index
   (at most the length of Gen's output), two sampler/eval outputs, two one-bit masks and empty
   fillers.
4. **Infrastructure.** Mostly present.
   - Present: `NUPPT.ofPolyTimeUniform`, `polyTimeComputable_output`, `polyTimeComputable_layout`,
     `polyTimeComputable_ite`, `pairXor`, `polyTimeComputable_coinSeg` (same file).
   - History readers over `encodeMsgs` exist in the GI efficiency work (`ZeroKnowledge/GraphIsomorphism/EfficiencyRep.lean`:
     `pairSndD_encodeMsgs`, `iterate_pairSndD_encodeMsgs`) and in `BinaryArith/Words` (`countW`).
   - Precedent: `giProver_efficient` and the other GI efficiency proofs, about 600 lines each.
   - Missing: a ready-made "length of the encoded history" reader in the OT file. The output-length
     bounds come from `PolyTimeComputable.output_length_le`.
5. **Size:** M (500–900).

### 2.2 `otProtocol_simulators` (`ObliviousTransfer.lean`:639)

1. **Statement.** For `hT : T.OneWay` and `hEHC : EnhancedHardCore T h` (with `henc`, `hH`):
   `∀ D, ∃ ε negligible, ∀ n a b`, `D`'s advantage is at most `ε n` for Alice's
   real/ideal pair (`otSimA`) and for Bob's (`otSimB`). Ref.: [PS10, Prop 161.5]. `S_B` is the
   source's exercise; the enhanced predicate follows [Gol04, App. C.1, §7.3.2].
2. **Dependencies.** None among the admissions. Uses the proved `otProtocol_outV`/`outP`.
3. **Well-posed.** Yes, as frozen. Checked:
   - **Alice.** Her tape coincides with `coinSeg 0 gen.coins`, and `simIdx` reads the same coins.
     Real `y_b = encD(perm x)` for `x` close to uniform; `SampleClose` holds *per generated index*,
     and `perm` is a bijection. `y_{1−b}` is canonical (`SamplerCanonical`). So both coordinates
     are δ-close to `encD(U)`, and the advantage is at most 2δ.
   - **Bob.** `otSimZb` uses exactly Bob's first coin block, and `H⟨i,w⟩ = [h x]` by
     `apply_of_decD`. The only difference is `z_{1−b}`. The predictor gets `⟨i, s'⟩` (the sampler
     coins of `y_{1−b}`), which is what `EnhancedHardCore` allows. Its advice is the worst of the 8
     triples `(b, a₀, a₁)`.
4. **Infrastructure.**
   - Present: `distAdv_le_of_statClose`, `StatClose` (`Asymptotic/Sampling`);
     `exists_pkPredictor` (`PublicKey/Trapdoor.lean`:337, but stated for `f : α ≃ α` inputs, so it
     needs an adapted copy for `⟨i, coins⟩` challenges); `NUPPT.exists_comp`, `exists_withAdvice`,
     `exists_split`; `uprob_prod`, `uprob_comp_equiv`; `Collection.sample_spec`, `inv_spec`,
     `f_perm`, `apply_of_decD`.
   - Missing: the view equations of the real execution (5 moves) for `viewP`/`viewV`, which follow
     the pattern of `otProtocol_outV`; the coin-space equivalences between real and simulated tapes.
5. **Size:** L (1500–2500).

### 2.3 `spDecStr_wrongKey` (`SpecialEncryptionSecurity.lean`:137)

1. **Statement.** Take any polynomial `ℓ`, a PRF `G'` with `n + ℓ(n)`-bit outputs and an evaluator
   `E'` on canonical inputs. Then `∃ ε` negligible such that for all `n` and every `ℓ(n)`-bit `m`,
   `1 − ε n < Pr_{k,k',r}[spDecStr E' n ℓ k' (spEncStr E' k m r) = none]`. Ref.: [PS10, §6.2.2],
   "the extra property" (Claim 157.a (ii)).
2. **Dependencies.** None. Used by `nestedSpecial_wrongKeyBot`, and by `specialScheme_wrongKey`
   per its sketch.
3. **Well-posed.** Yes.
   - The length guard always passes: `|p| = n + ℓ` by `hGE'`, so `|c₂| = n + ℓ`. Hence `none`
     holds exactly when `f_k(r)_{<n} ≠ f_{k'}(r)_{<n}`.
   - The one-query distinguisher has `Pr = 2^{-n}` against a random function.
   - `E'` has no `PolyTimeComputable` hypothesis, but the distinguisher can use the evaluator from
     `hG'.easy`, which agrees with `E'` on canonical inputs.
   - The strict `<` is met by adding `2^{-n}` to `ε`.
4. **Infrastructure.**
   - `PRFOut.pseudorandom` is an `OracleEnsemble.Indist` at a general `ℓ₂`, so it applies directly
     to `D.toOracleAdversary n n ℓ₂ q`.
   - **Missing:** a one-query next-query machine for an `ℓ₂`-output oracle, and an `ℓ₂` analogue of
     `PRF.negligible_prfAdv`. `PRFOut` has no consumer outside `SecureComputation`. The existing
     `MultiMsg.exists_queryChain_nuppt` is specific to `n`-bit outputs.
5. **Size:** M (400–700).

### 2.4 `specialScheme_wrongKey` (`SpecialEncryptionSecurity.lean`:155)

1. **Statement.** The same property for the `PrivateKeyScheme` (n-bit messages): `decodeFin n` of
   `Dec_{k'}(Enc_k(m))` is `none` except with negligible probability. Ref.: Claim 157.a (ii).
2. **Dependencies.** `spDecStr_wrongKey` at `ℓ = .var` (`G' = G`; the `Fin` types agree).
3. **Well-posed.** Yes. `runAt_spDec` returns `1^{n+1}` on `⊥`, which `decodeFin n` rejects. A
   `some` output has `n` bits. The coin space has an extra `dec.Coins` factor of size 1, removed
   by `uprob_comp_equiv`/`uprob_fst`.
4. **Infrastructure.** Present: `runAt_coinKey`, `runAt_spEnc`, `runAt_spDec`, `decodeFin_ofFn`.
5. **Size:** S (100–250).

### 2.5 `specialScheme_multiMessageSecure` (`SpecialEncryptionSecurity.lean`:115)

1. **Statement.** `(specialScheme G E hE hGE).MultiMessageSecure` for a length-doubling `PRFOut`
   `G`. Ref.: Claim 157.a (i), "easy to modify Construction 99.1"; [PS10, Def 93.1, Thm 99.2].
2. **Dependencies.** None. **No consumer as frozen.**
3. **Well-posed.** Yes. It is Thm 99.2 with a `2n`-bit pad and the message padded by `0^n`.
4. **Infrastructure.** This is the main gap.
   - The proof of `prfScheme_multiMessageSecure` (`Encryption/PrivateKey/FromPRF*.lean`, about
     1500 lines) is typed throughout for `F : … → (Fin n → Bool) → (Fin n → Bool)`
     (`prfEncReal`, `multiMsgAdv`, `distAdv_prfEncReal_le`, `exists_queryChain_nuppt`,
     `PRF.negligible_prfAdv`).
   - Generalizing to `ℓ₂`-bit outputs means editing those frozen files or copying them, which is
     duplication debt for the ledger.
   - The collision lemmas (`MultiMsg.negligible_choose_div_two_pow`) are reusable.
5. **Size:** L (1000–1800). If the joint lemma of B1 is proved generically, this declaration is a
   short corollary (S) of it.

### 2.6 `uprob_not_good_le` (`Garbling.lean`:425)

1. **Statement.** Assume `M.DecCorrect`, `M.WrongKeyBot δ` and `Cc.IsFaninTwo`. Then
   `Pr_{s ← GarbleSeed}[¬Good] ≤ 12 · |gates| · δ`. Ref.: Claim 159.a, probabilistic part
   ([PS10, §6.2.3], "all but one row will evaluate to ⊥"), weakened to first-success correctness.
2. **Dependencies.** None. Used by `garbling_good_whp`. Its argument is reused by `yaoSeed_good_whp`.
3. **Well-posed.** Yes.
   - `IsFaninTwo` gives `args.Nodup` and `|args| ≤ 2`. `args_lt` puts the gate's own vertex
     `n + i` outside its arguments, so the plaintext key is independent of the argument keys.
     `WrongKeyBot` is `∀ o`, so averaging over the plaintext is enough.
   - There are at most 4 × 3 = 12 ordered pairs `(a, a'')` with `a ≠ a''`. Constant gates add no
     event.
   - Failure is contained in the event "some other row decrypts", whatever the row order.
4. **Infrastructure.** Present: `uprob_exists_le` (union bound), `uprob_mono`, `uprob_prod`,
   `uprob_comp_equiv`, `uprob_fst`. Missing: the marginal of `Fin size → Bool → K` restricted to
   a `Nodup` argument list, through an equivalence such as `Equiv.piEquivPiSubtypeProd`, plus the
   bookkeeping for the `findSome?` failure event.
5. **Size:** M (400–700). This is the "contained garbling bound" of the decision-log rows
   480/481, with a 3-module local closure.

### 2.7 `nestedSpecial_wrongKeyBot` (`GarblingSecurity.lean`:69)

1. **Statement.** Given `hG₁` (length-doubling) and `hG₂` (`n + innerLen`):
   `∃ δ` negligible with `∀ n, (nestedSpecial E₁ E₂ n).WrongKeyBot (δ n)`. Ref.: Claim 157.a (ii)
   for the double encryption of [PS10, §6.2.3].
2. **Dependencies.** `spDecStr_wrongKey`, at `ℓ = .var` (with `G₁`) and at `ℓ = innerLen` (with `G₂`).
   Used by `garbling_good_whp`, and by `yaoSeed_good_whp` per its sketch.
3. **Well-posed.** Yes. The cases are `len = 1`, then `len = 2` where the first key differs (the
   outer layer fails), then `len = 2` where the first key agrees and the second differs.
   - In the last case the outer layer opens correctly: `spDecStr_spEncStr` applies, since the
     inner ciphertext has `innerLen` bits by `length_spEncStr`.
   - The inner message is random but independent of the outer keys, so Fubini over the remaining
     coordinates finishes the case.
   - `δ = ε₁ + ε₂`, negligible by `Negligible.add`.
4. **Infrastructure.** Present: `nestedSpecial_enc/dec` simps readers, `spDecStr_spEncStr`,
   `length_spEncStr`, `uprob_prod`. Missing: the relabelling `(Fin len → Bool → K) × ρ` ≃ (the
   two used keys × the rest).
5. **Size:** M (300–500).

### 2.8 `yaoSeed_good_whp` (`Yao.lean`:820)

1. **Statement.** On Alice's uniform `yaoCoins(n)` coins, the event "`yaoSeed` is not `Good`, or
   some output vertex has two equal keys" has probability at most `δ n`, for a negligible `δ`.
   Ref.: Claim 159.a, applied to Prot 162.6's seed.
2. **Dependencies.** `nestedSpecial_wrongKeyBot`, and the argument of `uprob_not_good_le`.
   - **`uprob_not_good_le` cannot be applied as frozen.** It is about a uniform `GarbleSeed`,
     whose third component is a uniform `Equiv.Perm`, but `yaoSeed` uses XOR shifts. Its sketch
     says "the argument applies".
   - The garbling proof should therefore publish a stronger form: the bound for every fixed
     row-permutation family, or for every seed distribution whose keys and row coins are uniform.
     `uprob_not_good_le` then follows by averaging, and `yaoSeed_good_whp` by push-forward.
3. **Well-posed.** Yes.
   - The blocks are disjoint and fit in `yaoCoins = 10Sn + 2S`. Keys sit at `(b·S + v)·n` with
     `v < size ≤ S`, rows at `2Sn + (4i + idx a)·2n` with `idx a < 4` (`assignIdx` is injective
     for `len ≤ 2`), and shifts at `10Sn + 2i`.
   - `|gates| ≤ size ≤ S`.
   - At `n = 0` the keys are trivial, but `δ(0)` is unconstrained.
   - `δ = 12·S·δ₀ + outLen·2^{-n}`, negligible.
4. **Infrastructure.** Present: `yaoSeed_fst/snd_fst/snd_snd`, `keyAt_yaoSeed`, `readBits_apply`,
   `uprob_exists_le`. Missing: the push-forward of the uniform measure through disjoint
   `readBits` blocks, and the generalized garbling bound described in item 2.
5. **Size:** M (500–900).

### 2.9 `yaoHybrid_polyTime` (`Yao.lean`:843)

1. **Statement.** `(yaoHybrid Y E₁ E₂).PolyTime (yaoFunctionality Y)` from `hE₁` and `hE₂`.
   This is the efficiency clause of `HybridProtocol.PolyTime`: efficient `main` strategies,
   poly-time call inputs and a message bound for **any** answers. Ref.: [PS10, Def 155.1] and the
   ruling of 2026-11-05.
2. **Dependencies.** None among the admissions.
3. **Well-posed.** Yes.
   - A row has at most `7n + 4` bits whatever `E` returns (`take`/`zipWith` cap the pads), so the
     bound does not depend on the answers.
   - Alice's `garbledTable` uses the noncomputable `Finset.univ.toList`. For `len ≤ 2` this is a
     fixed finite table, so `PolyTimeComputable` still holds: prove it for an arbitrary constant
     enumeration. The proof needs care here.
4. **Infrastructure.** Largely missing.
   - Missing: a poly-time decoder of `encodeCircuit`/`DAGCircuit.encode`. `Uniform.lean` has only
     the encoder and injectivity, and the CVAL machine (`CircuitEval*`, about 2260 lines) is a
     hand-built TM for Boolean gates that cannot be reused.
   - Missing: a poly-time `runWith` with a data-dependent gate function (`evalGate` with
     decryption), and the garbling function from coins as `PolyTimeComputable`.
   - Present building blocks: `polyTimeComputable_stateFind`/`iterate`/`blockMap`,
     `BinArith` `mapW`/`zipWithW`/`countW`, `polyTimeComputable_spEncFun`/`spDecFun`, and the GI
     `EfficiencyRep` history loops.
   - The same infrastructure is needed for `S_B` in `yaoHybrid_simulators`.
5. **Size:** L (1500–2500).

### 2.10 `yaoHybrid_simulators` (`Yao.lean`:918)

1. **Statement.** Assume `hE₁`, `hE₂`, `hG₁`, `hG₂` and the joint `hG₁₂`. Then `∃ SA SB`,
   `∀ D ∃ ε` negligible, both advantages are at most `ε n` uniformly in `x, y`. Ref.:
   [PS10, Thm 163.7] in the OT-hybrid model; the one-active-key simulator of [LP09].
2. **Dependencies.**
   - `yaoSeed_good_whp` (the `Bad` event) and the proved `yaoHybrid_correct`.
   - Step 3's hybrid needs multi-message security, under one inactive key `ι_u`, of the
     ciphertexts of **both** layers: the `G₂`-scheme with `(4n+2)`-bit messages where `u` is a
     first argument, and the `G₁`-scheme with `n`-bit messages where it is a second or only
     argument.
   - The frozen `specialScheme_multiMessageSecure` (`G` only, `n`-bit messages) does not give
     this. The docstring says so: "not yet stated in the library".
3. **Well-posed: yes, modulo B1.**
   - Alice's side is statistical: δ by `yaoSeed_good_whp`.
   - Bob's side:
     - the point-and-permute relabelling is a bijection of Alice's coins;
     - outputs are sinks (`outs_sink`), so the decoding pairs never reveal an encryption key;
     - Alice's keys and Bob's answers are active, so `ι_u` is only an encryption key.
   - The reductions are non-uniform: their advice is the worst `(x, y)`, the hybrid index, and
     the other randomness. The fixed-vector `MultiMessageSecure` bound is uniform in the messages.
   - No false statement found.
4. **Infrastructure.** Missing:
   - (a) the joint-key, length-generic multi-message lemma (B1);
   - (b) the poly-time garbling of 2.9 (for `S_B` and the reductions);
   - (c) the view equations of the two-move main phase, plus the hybrid-model sampler equations
     (`yaoMain_outV`/`outP` exist);
   - (d) a gate-indexed hybrid with an advice-selected index. `abs_sub_le_sum_hybrids` and
     `exists_hybrid_gap` exist.
5. **Size:** L, likely the largest (3000–5000, plus about 1000–1500 for (a)).

### 2.11 `composeP_efficient` / `composeV_efficient` (`ComposeSecurity.lean`:296/305)

1. **Statement.** Assume `hH : H.PolyTime F` and `hρ : G.PolyTime ρ`. Then `(H.composeP ρ).Efficient`,
   and symmetrically `(H.composeV ρ).Efficient`. Ref.: [Gol04, §7.3.1], efficiency of the
   protocol of Thm 7.3.3.
2. **Dependencies.** None. Used by `polyTime_compose` (proved), which the sketch of
   `hbcSecure_compose` uses for its efficiency clause.
3. **Well-posed.** Yes.
   - `composeP.next` (`Compose.lean`:344) branches on `|hist|` against `L·R`. It calls `runNextA`
     (one ρ-activation on a slot history cut from `hist`, with the run tape cut from `r`) or
     `main.P.next` on `⟨z, answersFromA⟩`.
   - `answersFromA` runs ρ's output function `L(n)` times. Each activation's input is at most the
     total input, so the time is `L(n)·poly`.
   - The call inputs are poly-time by the `callA`/`callB` clauses of `HybridProtocol.PolyTime`.
4. **Infrastructure.**
   - Present: `polyTimeComputable_blockMap` (fixed block size `b(|fst z|)`), `stateFind`/`iterate`,
     `exists_comp`/`exists_seq`, `Strategy.Efficient` readers, and `slotMsgs`/`runTape` readers
     in `Compose.lean`.
   - Missing: a "map a poly-time function over the `L(n)` run slots of a history" lemma (the slots
     are interleaved, not fixed-size blocks), and the extraction of a `PolyTimeComputable` function
     from `Strategy.Efficient` (`Computes.polyTimeComputable` exists for uniform NUPPTs).
5. **Size:** L for the pair (1000–1800). They are symmetric, so share the helpers.

### 2.12 `hbcSecure_compose` (`ComposeSecurity.lean`:378)

1. **Statement.** Assume `hM : ∀ n, 0 < H.main.rounds.eval n`, `H.HBCSecure F` and
   `HBCSecure ρ G`. Then `HBCSecure (H.compose ρ) F`. Ref.: [Gol04, Thm 7.3.3] (the numbering is
   "to be verified at audit"), with calls first. It is used unstated by [PS10, Thm 163.7].
2. **Dependencies.**
   - `composeP_efficient`/`composeV_efficient` through `polyTime_compose`, as statements only.
   - Not Yao, not OT.
3. **Well-posed: yes.**
   - **Output clause (step 2).** One non-uniform distinguisher with the worst inputs as advice
     tests the second component against `f_B(x*, y*)`. This gives
     `Pr[ρ-output ≠ ideal] ≤ ε₁`, uniformly, and is sound because `ε` precedes the inputs.
   - **Run hybrid (step 3).** The advice is the worst `i`, inputs, main tapes and ideal answers.
   - **`Φ` in step 4.** It recomputes the call inputs from `(x, r_main)`, which is poly-time by
     `H.PolyTime`, and runs `S_A^ρ`.
   - **Layout.** Real ρ-views have exact tape lengths, so `Φ`'s "cut to length" acts as the
     identity on them, and the end-hybrid matches exactly.
   - The worker's own `hM` counterexample is recorded in the docstring.
   - No false statement found.
4. **Infrastructure.**
   - Present: the phase lemmas in `ComposePhases.lean` (599 lines: `compose_exec_main`,
     `compose_viewP`, `compose_outV`, …), `compose_msg_bound`, `exists_runExec_eq_transcript`,
     `exists_hybrid_gap`, `abs_sub_le_sum_hybrids`, `uprob_exists_le`, and the NUPPT combinators.
   - Missing:
     - a NUPPT that runs a simulator `L(n)` times on blocks and assembles a view;
     - the statistical-switch argument "agree off a bad event";
     - the coin-space equivalence for the hybrid of run `i`;
     - `padFin` readback, which exists (`padFin_ofFn`).
5. **Size:** L (2000–3500).

## 3. Blockers and rulings

- **B1 (needed before the Yao simulators are dispatched): the joint multi-message lemma is not
  stated.** `yaoHybrid_simulators` cannot be proved from the frozen
  `specialScheme_multiMessageSecure`.
  - It needs a lemma of roughly this form: for a `PRFOut` family `G` and a list of encryption
    "slices" (pad offset and message length), many ciphertexts under one key, each from a slice
    of `G_k(r)`, are indistinguishable for any two message vectors. It is instantiated with
    `G₁ ‖ G₂` under `hG₁₂`.
  - Who states it is a design decision. Options, recommended first:
    - (A) the maintainer states it, sorried, in a small statement PR on the gate path, so that it
      is frozen. It is owned by U1 and consumed by U3. `specialScheme_multiMessageSecure` becomes
      a corollary.
    - (B) U3 states and proves it inside its own delivery, and U1 keeps the frozen
      `specialScheme_multiMessageSecure` only.
    - (C) U1 designs it as published API under a brief-level specification.
- **B2 (brief-level, no ruling): the garbling bound is too weak to reuse.** `uprob_not_good_le` as
  frozen is not reusable for `yaoSeed`'s XOR-shift seed. The U1 brief should require a published
  stronger lemma (every fixed permutation, or any seed law with uniform keys and coins), with
  `uprob_not_good_le` and `yaoSeed_good_whp` as corollaries. This is an addition, not a statement
  change.
- **B3 (likely ruling): duplication.** The `ℓ₂`-output PRF machinery duplicates `FromPRF/*` and
  `PRF.negligible_prfAdv` (n-bit only). Either accept it as recorded debt (a DL row, the precedent
  of DL-36/37/40) or generalize the frozen `FromPRF` files, which puts them outside the unit and
  needs a ruling. Recommended: accept as debt. Open a DL row at brief time. Consolidate later.
- **B4 (record only): G3-8 is closed.** See §0. The residual point, that no `EnhancedHardCore`
  instance exists, matters only to the Implications layer.
- **B5 (record only): Yao.lean size.** `Yao.lean` is at 942 lines. U1 edits one proof body and U3
  two large ones. Under the standing size rule a fill-owned file may pass 1000 lines and is never
  split, but helper modules (`Yao/…`) are better than growing the file.
- **No statement found false as frozen.** No missing hypothesis was found beyond B1, which is a
  missing *lemma* rather than a missing assumption: `hG₁₂` already supplies the hypothesis.

## 4. Proposed split (3 units, in dependency order)

Totals are rough: about 15–22k lines across the 13 admissions.

### U1 `sc-garble`: special encryption and garbling probability (wave 1)

- **Declarations (6).** `spDecStr_wrongKey`, `specialScheme_wrongKey`,
  `specialScheme_multiMessageSecure`, `nestedSpecial_wrongKeyBot`, `uprob_not_good_le`,
  `yaoSeed_good_whp`. Also the joint lemma of B1 under (A) or (C), and the stronger garbling
  lemma of B2.
- **Owns.** `SpecialEncryptionSecurity.lean`, `Garbling.lean`, `GarblingSecurity.lean`, and the
  body of `yaoSeed_good_whp` in `Yao.lean`. It may add new helper modules, for example
  `SecureComputation/SpecialEncryptionMulti.lean` and `SecureComputation/PRFOut.lean`.
- **Frozen.** Every statement; `SpecialEncryption.lean`, `GarblingSpecial.lean`, the rest of
  `Yao.lean`, `FromPRF*`, `Pseudorandom/*`.
- **Size.** About 3–5k (the multi-message lemma dominates).
- **Internal order.** `spDecStr_wrongKey` → `specialScheme_wrongKey`, `nestedSpecial_wrongKeyBot`;
  `uprob_not_good_le` (generalized) → `yaoSeed_good_whp`. The multi-message lemma is independent
  and can be checkpointed last.

### U2 `sc-ot-compose`: oblivious transfer and the composition theorem (wave 1, parallel to U1)

- **Declarations (5).** `otProtocol_polyTime`, `otProtocol_simulators`, `composeP_efficient`,
  `composeV_efficient`, `hbcSecure_compose`.
- **Owns.** `ObliviousTransfer.lean` and `ComposeSecurity.lean`, plus new helpers (for example
  `ObliviousTransfer/…`, `ComposeSecurity/…`).
- **Frozen.** `Defs.lean`, `Hybrid.lean`, `Compose.lean`, `ComposePhases.lean`, `YaoReal.lean`,
  `Asymptotic/Collections`, `PublicKey/Trapdoor`.
- **Size.** About 4–7k.
- **Structure.** Two independent halves on disjoint files, OT (about 2–3.4k) and composition
  (about 3–5k). Checkpoint per half. If a smaller job is wanted, U2 splits cleanly into U2a (OT)
  and U2b (compose) with no dependency between them, which gives four units.
- **Shared infrastructure.** The two efficiency targets share history readers with
  `otProtocol_polyTime`. This is one reason to keep them together.

### U3 `sc-yao`: Yao in the OT-hybrid model (wave 2)

- **Declarations (2).** `yaoHybrid_polyTime`, `yaoHybrid_simulators`.
- **Owns.** `Yao.lean` (these two bodies) and new `Yao/…` helper modules: a circuit decoder,
  poly-time garbling and garbled evaluation, the simulator `S_B`, and the hybrid.
- **Frozen.** Everything else, including U1's published lemmas.
- **Size.** About 5–8k. This is the long pole.
- **Wait condition.**
  - Under B1(A), U3 can start once the statement PR merges, using U1's sorried statements.
    However, it shares `Yao.lean` with U1's `yaoSeed_good_whp`, so the two land in sequence: U1,
    then U3 rebased.
  - Under B1(B), U3 can start now in parallel and lands after U1.
  - The simplest safe order is to dispatch U3 after U1 merges.

**Parallelism summary.**
- U1 ∥ U2 now.
- U3 after the B1 statement, or after U1's merge. U3 may run in parallel with U2.
- `YaoReal.lean` needs no unit: `yaoProtocol_hbcSecure` becomes free of admissions when U1, U2
  and U3 have all landed.

## 5. Recommendation

- **Dispatch U2 now.** No blocker. G3-8 is closed.
- **Dispatch U1 now if B1 is decided as (B).** Otherwise, first take the B1 ruling, recommended
  (A): a maintainer statement PR for the joint multi-message lemma, plus the brief-level B2
  requirement. Take the B3 debt ruling at the same time.
- **Hold U3** until B1 is settled and U1 has landed (or at least until the B1 statement is
  frozen).

## ===== briefs/pass-shelat-ch5-8/duplication-ledger.md =====

# Duplication ledger: Pass–shelat ch. 5–8

Accepted debt, each entry acknowledged by the user, with its scheduled resolution.

| ID | New declaration (where) | Existing copy (where) | Status | Resolution |
|---|---|---|---|---|
| DL-1 | `TCSlib.InformationTheory.abs_probTrue_sub_le_statDist` (#183, `InformationTheory/Extractors.lean`, for `main`) | `TCSlib.Cryptography.abs_sum_sub_le_statDist` (`Foundations/Experiments.lean`, Garg's concrete layer, on `cryptography/pass-shelat-ch2-4` and `cryptography/garg-ch1-3`; not on `main`) | accepted 2026-11-04 (user) | No copy on `main` today. When the concrete layer lands on `main`, its lemma becomes a one-line corollary of #183's (a `Finset` test is the `Bool` test `(· ∈ T)`) or is removed. Gate 01 pack erratum E1. |

## Inherited with ch. 2–4 (found 2026-11-05; acknowledged 2026-11-05 by the user: clean up now)

This campaign owns ch. 2–4 since 2026-11-05 (plan, decision log). These duplicates predate it.

| ID | Copies (where) | Status | Proposed resolution |
|---|---|---|---|
| DL-2 | XOR of encodings is the encoding of the Boolean sum, `zipWith xor (ofFn a) (ofFn b) = ofFn (a + b)`, stated three times: `TCSlib.Cryptography.zipWith_xor_ofFn_add` (`Asymptotic/HardCoreLoops.lean`; it was `zipWith_xor_ofFn`, renamed by the base repair to end the name clash with `Encryption.lean`'s different lemma); `TCSlib.Cryptography.zipWith_xor_ofFn_eq_add` (`Asymptotic/MultiMessage.lean`); `TCSlib.Cryptography.MultiMsg.zipWith_xor_ofFn_eq_add` (`Asymptotic/MultiMessageLemmas.lean`) | accepted; scheduled now | Keep the most upstream copy (`HardCoreLoops`) and point the other two at it, in a ch. 2–4 cleanup PR. |
| DL-3 | `pairEncode a b ≠ []`, stated four times: `GGMRed.pairEncode_ne_nil` (`Asymptotic/GGMReduction.lean`), `GI.pairEncode_ne_nil` (`ZeroKnowledge/GraphIsomorphism/Proofs.lean`), `ColMachines.pairEncode_ne_nil` (`ZeroKnowledge/ThreeColoring/Machines.lean`); and, on `main`, `Complexity.pairEncode_ne_nil` (`Complexity/SpaceComplexity/Logspace/InputAccess.lean`), the copy that made the merge's ambiguity | accepted; scheduled now | `main` is merged (#186). Remove the three local copies in favour of `Complexity.pairEncode_ne_nil`, in the same cleanup PR. |
| DL-4 | Not a copy (different carriers): the sampler-based `StatClose` (`Asymptotic/Sampling.lean`) and `main`'s `EpsClose` on `FinDist` (`InformationTheory/Extractors.lean`, #183) | accepted; scheduled now | A bridge lemma, in the same cleanup PR (user, 2026-11-05). |
| DL-5 | Not a copy (different carriers; found by the gate 02 round 2 review): `Games.guessAdv_eq_half_advantage` and `Games.accept_guessGame` (games) and the concrete layer's `predict_eq` (`Asymptotic/Ensembles.lean`, on `uprob` over seed spaces), both the identity behind [PS10, Lemma 73.8] | disclosed in the docstring (gate 02 closing commit) | Derive one from the other through bridge B2 when ch. 2–4 lands on `main`. |

## Found in the ch. 5–8 statement phase (2026-11-05)

| # | Statement | Copies | Status | Resolution |
|---|---|---|---|---|
| DL-6 | Coin-tape slices `(r.drop (j * c)).take c` in global/GI-shadow graph isomorphism, Lamport and sequential ZK, alongside the former BlockEncryptor home | historical duplicates found by the Lamport worker/maintainer | **Implemented at `e9d64158461bfe24ddc88ab885bc4017899b4c16`; final source `3f6db40e1688c4a0bb922c9575dd3bd2157a650b` is checked in draft PR #232. Native and layered Rule10 reconciliation identify zero new/touched reads; all older failures remain recorded. External gates and landing pending.** | One `TCSlib.Cryptography.coinBlock`, `coinBlock_eq` and `length_coinBlock` live in `Asymptotic/Adversary.lean`. The BlockEncryptor definition moved upstream; global/shadow `coinSlice` and sequential ZK's `phaseSlice`/unused length lemma are retired. Lamport already used the public BlockEncryptor `coinBlock`; its length lemma moved upstream. Consumers use the shared name and published reader. |
| DL-7 | Equal-length padding: Lamport's `ofFn_padFin_of_length`, and the inline step in `Composability.length_eval_of_length` (`CCA2Scheme.lean`) | General equation `Collection.ofFn_padFin_of_le` in **`Asymptotic/CollectionsHelpers.lean`**, not `Collections.lean` | **Implemented at `e9d64158461bfe24ddc88ab885bc4017899b4c16`; final source `3f6db40e1688c4a0bb922c9575dd3bd2157a650b` is checked in draft PR #232. Native and layered Rule10 reconciliation identify zero new/touched reads; all older failures remain recorded. External gates and landing pending.** | Lamport's duplicate theorem is deleted. Its uses and CCA2's two padding steps use the general equation, whose conclusion is `List.ofFn (padFin ℓ w) = w ++ List.replicate (ℓ - w.length) false`; at `w.length = ℓ`, simplify `Nat.sub_self`, `List.replicate_zero` and `List.append_nil`. |
| DL-8 | `SecureComputation.PRFOut ℓ₂` (prong B, `SpecialEncryptionSecurity.lean`): ch. 2–4's `PRF` with `ℓ₂(n)`-bit outputs; `PRF` is its case `ℓ₂ = n` | resolved 2026-11-05 | `prfOut_var_iff : PRFOut .var F ↔ PRF F` proved beside `PRFOut` (prong B). The ch. 2–4 layer is unchanged. |


## Found by gate 03 (2026-11-05; rulings G3-5 and R-03l-1: clean up in the gate 03 clean-up PR, after #195)

Most copies trace to helpers that are `private` in pack 03a's and 03l's files. The clean-up makes
one copy public in the most upstream file and re-points the rest.

| Id | Copies | Status | Payback |
|---|---|---|---|
| DL-9 | The coin-block bijection `blocks` (`Fin (m · c) → Bool ≃ Fin m → Fin c → Bool`) and its lemmas, copies and an inverse: `FunFamily.blocks`, `OneWayYao.blocksE`, `blocksEquiv`, `blocksEquivX`, `EnsembleLemmas.blocks`, `SoundnessRep.blocksEquiv`, and `Ensemble.blocks` (private, `Asymptotic/Ensembles.lean`, which calls itself a copy of `FunFamily.blocks`; added on gate 03a round 2, R2-4); with S2b's public duplicate `take_drop_ofFn_blocks` of `EnsembleLemmas.take_drop_ofFn_blocks` (gate 04 N4) | accepted; scheduled (G3-5) | One `FunFamily.blocks` in a low file; re-point 03h, 03i, 03k's statements, `Ensembles.lean` (03a) and S2b's copy. |
| DL-10 | `ptc_comp` (composition of polynomial-time functions in a convenient form), six private or public copies (`Closure`/`Repetition` helpers, `Universal*`, `ThreeColoring/Machines`, …) | accepted; scheduled (G3-5) | Public once in 03a's `Closure.lean`; delete the copies. |
| DL-11 | The state loop `stateFind` (private in `Repetition.lean`) and its copies `GI.stateFind`, `EncodingMachines.polyTimeComputable_stateFind`, `GGMRed.stateLoopFun`, and the variant `stateIterate` | accepted; **half done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)** (`polyTimeComputable_stateFind` public, prose fixed); the copies are re-pointed in clean-up part 2 | `polyTimeComputable_stateFind` public in `Repetition.lean`; re-point; update the prose that calls it private (`StringLoops.lean:36–38`, `HardCoreLoops.lean:68`). |
| DL-12 | `abs_uexp_sub_le`, two copies (`PublicKeyLemmas` and a private one) | accepted; scheduled (G3-5) | One public copy. |
| DL-13 | `negligible_zero` (`Foundations/Negligible.lean` since G3-7a) and `negligible_const_zero` (`ZeroKnowledge/Defs.lean`) | accepted; scheduled (G3-5) | Delete `negligible_const_zero` (2 uses). |
| DL-14 | `forall_of_uprob_eq_one`, two copies | accepted; scheduled (G3-5) | One public copy. |
| DL-15 | `decodeFin_eq_some_iff`, a private copy in `Collections.lean` and a public one in `GGMReductionEval.lean` (`GGMRed.decodeFin_eq_some_iff`; making the `Collections.lean` copy public must avoid the namespace clash, gate 03b review #12c), and the new forward lemma `ofFn_of_decodeFin_eq_some` (`CollectionsHelpers.lean`, #198); S2b's private `eq_ofFn_of_decodeFin` | accepted; scheduled (G3-5) | One public `decodeFin_eq_some_iff` in `Asymptotic/Adversary.lean`; the forward lemma derived from it. |
| DL-16 | `IterateFindHost` (03l) copies 26 declarations of `main`'s private module layer in `Complexity/ClassNP/SAT.lean` (ten now public); the new host is missing from the policy's host registry (§14) | **done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)**: one public host `Turing.ModuleHost` (`TuringMachine/Build/ModuleHost.lean`), consumed by `SAT.lean` and `IterateFindHost.lean`; registry row H14 | Make `SAT.lean`'s layer public on the ch. 2–4 branch and re-point `IterateFindHost`; register the host. |
| DL-17 | `StateLoop` (03l) restates five `main` lemmas, plus `tail_poly` and `xor_poly` (arrived with the `main` merge, #186) | accepted; scheduled (R-03l-1) | Use `main`'s lemmas. |
| DL-18 | `UnaryMul` (03l) privately copies `PairSplit`'s parser | **done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)** (`Turing.PairParse` in `PairSplit.lean`) | Use `PairSplit`'s. |
| DL-19 | Not a copy yet: a latent name clash between `StateLoop.BlockLoop` and `main`'s `Complexity.BlockLoop` (nothing uses it) | **done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)** (renamed `StateLoop.BlockMapLoop`) | Rename or merge in the same PR. |
| DL-20 | `main`'s `TuringMachine/Build/Loop.lean` keeps a private `loop_first_halt`, the same lemma as the new public `Turing.ModuleHost.first_halt` (found by #203's worker). `Loop.lean` is upstream of the host, so it cannot consume it | noted | Move `first_halt` and `live_prefix` down into `Loop.lean` (or the machine core) at the `main` landing, and have `Loop.lean` use them. |
| DL-21 | Elementary number theory that Mathlib already has (audit `mathlib-overlap-nt.md`, 2026-11-06, Mathlib pin `029db123`): 6 DUP (`QR` = `(powMonoidHom 2).range`, `crtUnits` (keep as alias, `rfl`), `coprime_of_ne` = `(Nat.coprime_primes hp hq).2`, `powOneSubgroup` = `(powMonoidHom m).ker`, `rsaPerm` ≈ `powCoprime` (optional), `IsGenerator` ≈ `∀ x, x ∈ zpowers g`) and 9 WRAP (shorter proofs from Mathlib: `units_val_mem`, `pow_mod_totient_modEq`, `units_pow_eq_one_iff`, `two_mul_card_le_of_ne_top`, `card_units_eq_mul_card_QR`, `card_QR_prime`, `sq_pow_div_four_succ`, `fmultNat_eq_mul_prime`; and the core of the sorried `elGamal_correct`) | accepted; scheduled (user direction 2026-11-06: Mathlib first) | Replace by Mathlib's (alias where a name is load-bearing), clean-up part 2 item M; rows in fill-owned files (`Candidates/*`) after those fills land, as landing edits. The fill briefs cite the report's Mathlib names. |
| DL-22 | TCSlib's Chebyshev lower bound (`NumberTheory/Chebyshev.lean`) and Korselt-type facts are in newer Mathlib (`Chebyshev.pi_ge`, `theta_ge`, `psi_ge`; `Nat.isCarmichael_iff_korselt`; master `94f43000`, Lean v4.36.0-rc2), not at our pin | noted | Replace at the next Mathlib bump (repository-wide, `main`'s pin). At the same bump, the hypothesis `BlumDensity` (`Rabin.lean`) can be discharged in its eventual form (`n ≥ n₀`): apply `WienerIkehara.tendsto_sum_range_div` (master only) to `vonMangoldt.residueClass 3` mod 4, with the continuation `vonMangoldt.continuousOn_LFunctionResidueClassAux` (already at our pin) and Chebyshev's `ψ(x) ≪ x` (master), to get `ψ(x; 4, 3) ~ x/2`; then `θ ≥ ψ − (ψ − θ)` (`Chebyshev.psi_sub_theta_le_mul_sqrt`) and `π(x; 4, 3) ≥ θ(x; 4, 3)/log x`. This changes the Rabin statements that take `BlumDensity` (they would take nothing, or `n ≥ n₀`); a statement gate then. |
| DL-23 | fac fill (`Candidates/Factoring.lean`, delivery review 2026-11-07): private near-copies of public lemmas: `fac_chunkEquiv` = `FunFamily.blocks`; `fac_arrowCongr` = `finCastEquiv`; `fac_ofFn_halves` repeats a private `OneWay` lemma (half is `ofFn_block_eq_take_drop`); `fac_listToNat_inj` repeats a private `Sampling` lemma; plus the REPORT's three near-duplicates and small numeral facts re-proved across the fac, rsa and dl-a fills | noted | Clean-up part 2: re-point to the public lemmas; publish the two private ones beside their files and share the numeral facts. |
| DL-24 | col-b fill (delivery review 2026-11-07): `ColZK.acceptProb_seed_to_coins` = `acceptProb_bind` reversed and `ColZK.findSome?_map_option` = core `List.map_findSome?` (removed by landing edits E3–E4); a third copy of `pushesUniform_restrict` across fill units (dl-a has one); `table_index_*` vs `finProdFinEquiv`; `polyTimeComputable_next` repeats `reply_poly`'s proof (review finding 6 has the full list) | E3–E4 at landing; rest noted | Clean-up part 2: publish one `pushesUniform_restrict`, re-point the rest. |
| DL-25 | dl-b fill (`DiscreteLogHardcore.lean`, delivery review 2026-11-07): `dlb_statClose_pi` copies the public `OneWay.statClose_pi` (removed by landing edit E1); `dlb_stateIterate_poly` (from `HardCoreLoops`), `dlb_count_ofFn` (from `HardCoreGL`; relative of `List.count_ofFn`), the `listToNat` fold lemmas, `two_pow_size_le` (dl-a and 3-col have inline `2^size m ≤ 2m` bounds), `pushesUniform_castLE` copies (review D1) | E1 at landing; rest noted | Clean-up part 2: publish one copy of each beside its source; missing equations `HardcoreBit.majority_eq` (`PairwiseIndependence.lean`) and `expSampler_coins` (`DiscreteLog.lean`) at the next shared-file window. |
| DL-26 | col-a fill (delivery review 2026-11-07): `colRep_xor_poly` = `StateLoop.xor_poly`, `eq_of_xor_eq_false` = core `bne_eq_false_iff_eq`, `pushesUniform_blockRead` rebuilds `FunFamily.blocks` (removed by landing edits E2–E4); `ColRep.exec_four_mul`'s step repeats `GI.exec_repViews`'s proof (promote `exec_four_mul`, request R-3); cross-unit near-copies with col-b's `ColZK.pushesUniform_offsetTable`, `ColZK.ofFn_drop_take` | E2–E4 at landing; rest noted | Clean-up part 2: promote `exec_four_mul`, share the col-a/col-b helpers; requests R-2 (`(decGraph x).1` equation), R-5 endorsed. Base reading for #210's next round: `R3COL_witnessRelation`'s `bounded` clause destructures `R3COL` instead of using `R3COL_iff`. |
| DL-27 | rsa fill (delivery review 2026-11-07): 151 lines copied verbatim from dl-a's private helpers (`dla_findSome?_ite`, `dla_find?_range_lt`, `dla_listToNat_append`, `dla_drop_natToList_zero_append`, `dla_ss*`); `rsa_appendEquiv` = Mathlib `Fin.appendEquiv` (landing edit E1); `rsa_comp`/`ptc_congr` copies of the private `ptc_comp` family; loop lemmas descend from Primality's private `spStep`; near-copies of `findSome?_eq_bind_find?`, `find?_range_eq_map_find?_finRange`; parallels with fac (`fac_natToList_mod`, `fac_pairDec`) | E1 at landing; shared-lemma PR planned | **Landing order:** (1) dl-a lands; (2) a shared-lemma PR publishes `PolyTimeComputable.comp'`/`.congr` (`PolyTime.lean`), `IterateFind.find?_range_and_lt` (`IterateFind.lean`), nine `listToNat`/`natToList` lemmas (`Arithmetic.lean`), `rejectBlocksL_eq_find?` (`Concrete.lean`), removing dl-a's copies; (3) rsa lands with E1–E3 and E4 (cites them; checked against stubs); (4) a statement-gated `polyTimeComputable_rejectBlocksL` retires the copied loops in dl-a, rsa, rabin (and dl-c, pending its review). |
| DL-28 | dl-c fill (delivery review 2026-11-07): near-verbatim copies of the trial loop and numeral helpers shared with dl-a and rsa (and dl-b's own modular-numeral layer); `dlc_abs_uexp_sub_le` duplicates `Sampling.lean`'s private lemma and its public copy in `PublicKeyLemmas.lean` (review D1) | noted | Folds into DL-27's shared-lemma PR. The review's D2 homes: generic `polyTimeComputable_rejectBlocksL` (`Concrete.lean`), `listToNat` lemmas, width lemmas (`Arithmetic.lean`), `find?_range` (`Repetition.lean`), `PolyTimeComputable.congr` (`PolyTime.lean`), `abs_uexp_sub_le` public in `Sampling.lean`, `finCastEquiv` to `CollectionsHelpers.lean`. Reconcile with DL-27's homes when that PR is drafted. |
| DL-29 | rabin fill (delivery review 2026-11-07): `rabin_appendEquiv` = Mathlib `Fin.appendEquiv` and `rabin_pushesUniform_prod` (re-proved from `PushesUniform.prodMap`) handled by landing edits E1–E2; undisclosed copies: `rabin_statClose_one` = dl-a's `dla_statClose_one`; `rabin_listToNat_mulStr`, `rabin_prime_poly` copy rsa helpers; `rabin_rS`/`_rQ`/`_rTest` ≈ rsa's `rsa_fS`/`_fQ`/`_fTest`; the block loop is a fourth copy (with dl-a, rsa, dl-c `dlc_ss*`); `rabin_drop_zeros_append`'s step = fac's `fac_natToList_mod` | E1–E2 at landing; rest noted | Folds into DL-27/DL-28's shared-lemma PR and the `polyTimeComputable_rejectBlocksL` host PR. Base reads `rabinCollection_index`, `rabinBlumTrapdoor_index` (through `show`; re-point via `Collection.index_eq`) go to clean-up part 2's (b) list. |
| DL-30 | padded-cpa fill (delivery review 2026-11-11): generic `ProbComp` facts published in a public-key helper as `Composability.ChallengeSim.expect_sample_equiv`, `expect_sample_comm`, `expect_sample_unique`, `expect_sub` (`PublicKey/OracleSecurity/ChallengeSim.lean`); `expect_sample_prod` repeated `Bridge.expect_sample_pair`'s proof. | `ChallengeSim.lean` only | **Paid** ([#298](https://github.com/Shilun-Allan-Li/tcslib/pull/298), merge `d3f2290a`, 2026-11-13; Gate 20) | Landing edit re-proved `expect_sample_prod` from `Bridge.expect_sample_pair`. Promote the four lemmas to `ProbComp` in `Games/Probability.lean` and re-point their uses. |
| DL-31 | `ofFn_padFin_of_length` (`List.ofFn (padFin d w) = w` when `w.length = d`): `GGMRed.ofFn_padFin_of_length` (`GGM/Run.lean`), copy in `Asymptotic/HardCoreGLColl.lean`, private copy in `ElGamal.lean`; padded-cpa's `RecordHandler.lean` uses the GGM one through a transitive import. | 3 | **Paid** ([#298](https://github.com/Shilun-Allan-Li/tcslib/pull/298), merge `d3f2290a`, 2026-11-13; Gate 20) | Promote one public lemma beside `padFin` in `Asymptotic/Adversary.lean`; re-point all uses and delete the copies. |
| DL-32 | `List.ofFn (cast h f) = List.ofFn f` for a width equality: public `Composability.AdaptiveCPA.ofFn_cast` (`PublicKey/AdaptiveCPA/Games.lean`) and private `cca2OfFn_cast` (`PrivateKey/OracleFromPRF.lean`, #289). adaptive-cpa review also lists for promotion: `expect_sample_update` (→ `Games/Probability.lean`, with DL-30), `simulate_eq_of_abs` and the `castImpl` family (→ `Games/Simulate.lean`), `padFin_ofFn_zeroBits`, `headD_ofFn_one`, `ofFn_splitHalf_fst/_snd`; reader request `indCodec_eq_bitCodec`; new uses of `GGMRed.ofFn_padFin_of_length` join DL-31. | 2 (+ candidates) | **Paid** ([#298](https://github.com/Shilun-Allan-Li/tcslib/pull/298), merge `d3f2290a`, 2026-11-13; Gate 20) | Promote one generic `ofFn_cast` beside `padFin`/`BitCodec`; re-point both; promote the listed generic lemmas. |
| DL-33 | bitwise-cpa fill (delivery review 2026-11-11): `BitwiseSim.expect_sample_update` vs `AdaptiveCPA.expect_sample_update` (two forms, same name); generic `BitwiseSim.expect_simulate_eager` and public near-copy `BitwiseSim.expect_simulate_indImpl_cpa` of the private lemma in `PublicKey/OracleSecurity.lean`; `chRun_toCompOn_transport_list` generalizes `ChallengeSim.chRun_toCompOn_transport`; `BitwiseSim.headD_drop` = public `CommitmentLemmas.headD_drop` (and private `headD_drop_ofFn` in `Pseudorandom/NextBit.lean`); `flatten_ofFn_singleton` = private `flatten_ofFn_one` (`Yao.lean`); `decodeFin_nil_getD` (→ `Games/BitCodec`); `padded_enc_runAt/_coins` (→ beside the padded readers); `qDin/qDout` third copy of the two-oracle length vector (`recDin/recDout`, `acDin/acDout`); private `ofFn_half`, `bitwise_runAtL` re-prove published facts; reader request `HybridMachine.hybridPre_eq`. | several | **Paid** ([#298](https://github.com/Shilun-Allan-Li/tcslib/pull/298), merge `d3f2290a`, 2026-11-13; Gate 20) | One consolidation PR with DL-30–DL-32: promote to `Games/Probability`, `Games/Simulate`, `ChallengeSim`, `BitCodec`, a shared list module; re-point and delete copies. |
| DL-34 | pk-cpa-cca1 fill (delivery review 2026-11-12): `OracleFromPRF/Handler.lean` copies private AdaptiveCPA handler pieces (`ofFn_padFin_eq_padL`, round-input readers `rU`…`rCnt`, `impl_of_ret`, `replicate_one`); public `ofFn_pkTapes` re-proves `AdaptiveCPA.ofFn_acTapes` (a generic `⟦blocks q ℓ ω j⟧ = (⟦ω⟧.drop (j·ℓ)).take ℓ` belongs beside `FunFamily.blocks`, input-layout readers beside `InteractiveHandler.input`); private-key `indCodec_eq_bitCodec` (DL-32 reader request); `mem_keys_of_lookup_isSome` (core `List.lookup_isSome_iff`); promotion candidates `simulate_eq_of_abs_bounded` (generalizes `AdaptiveCPA.simulate_eq_of_abs`), `expect_simulate_congr` (→ `Games/Simulate`), `abs_expect_sub_le` (→ `Games/Probability`), `prob_bad_le`, `expect_sample_mem_le` (→ `Games/Hopping`), `padFin_nil`, `padFin_replicate_false`, `ofFn_arrowCongr_finCongr` (→ beside `padFin`), `zipWith_xor_cancel_left`, `xorPerm` (shared list/vector module); owned-file private overlaps with the `cca2*` helpers. | several | **Paid** ([#298](https://github.com/Shilun-Allan-Li/tcslib/pull/298), merge `d3f2290a`, 2026-11-13; Gate 20) | Fold into the DL-30–DL-34 consolidation PR. |
| DL-35 | Found while staging the consolidation (2026-11-12): public `blocks` in `Asymptotic/EnsemblesLemmas.lean` and private `blocks` in `Asymptotic/Ensembles.lean`, both the equivalence `(Fin (q * ℓ) → Bool) ≃ (Fin q → Fin ℓ → Bool)` of `FunFamily.blocks` (`Asymptotic/Adversary.lean`). | 2 | Open (ch. 2–4 inherited) | Re-point to `FunFamily.blocks` in a later ch. 2–4 cleanup; out of scope for `dl-consolidation`. |
| DL-36 | nm-cca2 fill (delivery review 2026-11-12): `NMCCA2.logEmit` (`PublicKey/NonMalleability/Indistinguishability/Forward.lean`) generalizes `Games.EffFill.relabelN`/`relabel` (`Games/Efficiency/OracleBridge.lean`), and its log facts `logEmit_encodeLog`, `iterate_pairSndD_encodeLog`, `flatMap_range_drop`, `length_le_length_encodeLog`, `length_iterate_pairSndD_le`, `polyTimeComputable_logEmit` mirror `relabelN_encodeHist`, `length_le_length_encodeHist` and the orbit bound of `bridgePre_poly` (undisclosed); public `finU`, `finZ`, `finW`, `finA`, `finL`, `fields_finInput` are the DL-34 round-input readers (`rU`…`rL`) again; `ofFn_nthCt` (owned file) is DL-34's generic block fact (`ofFn_acTapes`, `ofFn_pkTapes`); the private readers `rState`…`rAns` (disclosed). Promotion requests: `fwdHandler`/`fwdHandler_impl`, `exists_withAdviceOn` (→ `Games/Efficiency`), `cntRead`/`ansRead` (→ `BitCodec`), `indImpl_eq_of_msgLen_eq_zero` (→ `PublicKey/OracleSecurity`, after that file is split: it is at 999 lines). | several | **Paid** ([#299](https://github.com/Shilun-Allan-Li/tcslib/pull/299), merge `eff2dcd0`, 2026-11-14; Gate 21) | After the DL-30–DL-34 consolidation lands: put `logEmit` beside `relabelN` with `relabel x = logEmit relabelEmit x`; re-point `dCnt`/`dCt`/`dIn`/`dFin`/`eBit`/`eMsg`/`eTape`/`eCt` to R6's readers and delete `finU`…`fields_finInput`; derive `ofFn_nthCt` from the generic block lemma; promote the accepted requests. |
| DL-37 | nm-sim fill (delivery review 2026-11-13; **undisclosed**, accepted as debt by Seyoon 2026-11-13): `NMSim.chunkAt`/`chunkAt_eq`/`length_chunkAt` (`PublicKey/NonMalleability/Simulation/Hybrid.lean`) and the block lemmas `ofFn_block`, `chunkAt_flatten_append`, `map_chunkAt_flatten`; private `padFin_replicate_false` (`Simulation/Challenge.lean`); `Rounds.impl_of_ret`, `rdU`…`rdLog`/`rdState`, `rdAns`, `Simulator.finSt` (`Simulation/Rounds.lean`, `Simulator.lean`); also generic neighbours `expect_eq_until_bad`, `NMSim.expect_simulate_eager`, `expect_congr_of_allOutputs`, `chunkMap`; disclosed: `flatMap_range_drop`, `ofFn_padFin_eq_padL`, `polyTimeComputable_guessBit`, `ofFn_eq_map_range` | `coinBlock`/`coinBlock_eq`/`length_coinBlock` (`Asymptotic/Adversary.lean`), `OneWayLemmas.ofFn_block_eq_take_drop`, `NMCCA2.ofFn_nthCt`, Lamport `coinBlock_flatten`; `PRFGame.padFin_replicate_false` (`OracleFromPRF/Transfer.lean`; → `Games.padFin_replicate_false` in the consolidation); DL-34 private `impl_of_ret` (`AdaptiveCPA/Handler.lean`, `PRFGame`) and readers `rU`…`rL`/`rS`; `Games.prob_eq_until_bad`, `BitwiseSim.expect_simulate_eager`, `ProbComp.expect_mono_of_allOutputs`, `relabelN`/`logEmit` (DL-36); ZK `ofFn_eq_map_range` ×2; A4 `EnsembleLemmas.ofFn_padFin_eq_padL`; `rFwd`/`rY`/Forward `rAns` | **Paid** ([#299](https://github.com/Shilun-Allan-Li/tcslib/pull/299), merge `eff2dcd0`, 2026-11-14; Gate 21) | Landing of the consolidation (after nm-sim): delete the private `padFin_replicate_false` and use `Games.padFin_replicate_false`; re-point the nm-sim files to the moved names. Post-consolidation fold window, with DL-36: fold `chunkAt` onto `coinBlock` (58 uses) and place the block lemmas beside it; re-point `rdU`…`rdLog`, `rdState`, `finSt` to `InteractiveHandler.rU`…`rS` and `impl_of_ret` to `InteractiveHandler.impl_of_ret`; derive `prob_eq_until_bad` and `ChallengeSim.expect_simulate_eager` from the general nm-sim forms; one iterate-and-emit definition for `relabelN`/`logEmit`/`chunkMap`; merge the three `ofFn_eq_map_range` into `Foundations/BitLists`; make `NMSim.ofFn_padFin_eq_padL` the A4 lemma; fold `rdAns` with the `rFwd`/`rY`/`rAns` readers; promote the accepted requests (review r1 table). |
| DL-38 | dl-folds fill (worker REPORT §0.6, disclosed; delivery review 2026-11-14): inline re-proofs of `impl_of_query` (`acHandler_impl_forward`) and of a returning finalization (`pkHandler_finish`, `acHandler_finish`); a local `have` equal to `polyTimeComputable_ansRead` (`OracleFromPRF.lean`); further block-window restatements (`Primality.ofFn_chunk`, `ColRep.drop_take_ofFn_blockRead`, `Factoring.fac_ofFn_halves`, already corollaries); other iterate-and-emit loops (`BlockEncryptor`, `EnsembleLemmas.CopiesLoop`, `StretchMachine`, `CommitmentLemmas.ComLoop`, ZK `EncodingMachines`); the ZK pair `GI.iterate_pairSndD_encodeMsgs` / `ColMachines.iterate_pairSndD_encodeMsgs`; and the B3 `blocks` aliases (`EnsembleLemmas.blocks` and its lemmas, private `Ensembles.blocks`), escalated. | `InteractiveHandler.impl_of_query`, `finish_of_ret`; `Games.polyTimeComputable_ansRead`; `FunFamily.ofFn_blocks`; `Games.iterEmit`; `FunFamily.blocks` | Open (deferred) | Opportunistic: fold each when its file is next touched. The B3 aliases need a gate-approved restatement of `exists_copiesRed`, `ofFn_blocks_symm`, `take_drop_ofFn_blocks`, `ComLoop.emit_init_of_lt` and of the bodies of `PRFGame.pkTapes`, `Ensemble.copies` (all definitionally equal). Complexity copies of `ofFn_eq_map_range` and `flatMap_range_drop` are another campaign's. |
| DL-39 | ext-nosrc fill (worker request and delivery review 2026-11-14, disclosed): `Randomness.Rejection.tupleEquiv` restates Mathlib's `(Fin.consEquiv _).symm`; generic `FinDist` facts local to `Randomness/Extraction/Rejection.lean` (`sum_map`, `expect_map`, `probTrue_map`, `probTrue_le_one`, `probTrue_nonneg`, `map_map`, `map_prod_snd`, `uniform_prod`, `map_uniform_equiv`, `mixture`, `mixture_isSource`, `uniform_probTrue`); no exact duplicate in TCSlib (nearest: `SamplingFinDist.uprob_comp_eq_probTrue_map`, `Experiments.uprob_comp_eq_sum_map`, `ProbComp.expect_map`). | Mathlib `Fin.consEquiv`; `InformationTheory/FinDist` (to be added) | Open (deferred) | Promote the `FinDist` facts to `InformationTheory/FinDist` and use `Fin.consEquiv` in a later job (`FinDist` was frozen for the fill). The authoritative full promotion list (also `map_apply_expect`, `branch_apply`, the uniform-machine family, `take_poly`) is the delivery's `evidence/promotion-requests.md`, `rejection-review.md`, `sampler-review.md` (exchange `a5da5cc3`, `inbox/fills/ext-nosrc/`; Gate 22 observation). |
| DL-40 | cca2-ett fill (delivery review 2026-11-14): undisclosed `ETTGame.eval_toOracleAdversary_len` (`EncryptThenTag/Machines.lean`) generalizes public `PRFGame.eval_toOracleAdversary_width` (`OracleFromPRF/Reduction.lean`, its `ℓ = n` case); disclosed `ETTGame.zipWith_xor_cancel` = four private `zipWith_xor_xor_self` copies (`FromPRF`, `FromPRG`, `SpecialEncryption`, owned `zipWith_xor_xor_self'`; public relative `zipWith_xor_cancel_left`, other orientation); Gate 23 (G23-01, Seyoon 2026-11-14: debt now, fold in cleanup): private `length_le_length_encodeLog` (`EncryptThenTag/Machines.lean`) = the private copy in `NonMalleability/Indistinguishability/Forward.lean:108`; `ETTGame.prfAdv_eq_expect` re-derives private `prfAdv_prfReduction` (public relative `prfAdv_eq`, uprob form); generic forms `ETTGame.tapeImpl`/`simulate_tapeImpl_congr`/`expect_simulate_tapeImpl` (AdaptiveCPA), `recBits` family and `ovr` (PRFGame), `expect_simulate_abs` (`Games.simulate_eq_of_abs_bounded`), private `abs_expect_sub_le_expect` (`ProbComp.abs_expect_sub_le`). | `Foundations/BitLists`, `Pseudorandom/Functions`, `Games/*`, the general ETT forms | Open (deferred) | Promote the general forms (worker requested most) and re-derive the specialised copies from them; fold the private XOR copies; publish `length_le_length_encodeLog` in `Games/Efficiency/Strings.lean` beside `length_encodeLog_le` and delete both private copies (cleanup job). |
| DL-41 | dl-crh fill (delivery review 2026-11-14): **undisclosed** `FromDiscreteLog.inputWord_split` restates `ofFn_eq_init_append` (`Asymptotic/ReductionSupport.lean`, up to `Fin.init`); `ofFn_splitBits_fst/_snd` restate `ofFn_splitCoins_fst/_snd` (`CollectionsHelpers.lean`; `Authentication.splitBits` = `splitCoins`); disclosed re-derivations from public readers of private `dlb_expo_val`, `fac_listToNat_inj`, `ofFn_splitCoins_symm_cast`, `dla_statClose_expDec`; near relatives `residueFinEquiv` (Mathlib `ZMod.finEquiv`), `boundedInputEquiv` (`Fin.snocEquiv`), `expect_sample_eq_uexp` (`Games.Bridge.prob_sample_eq_uprob`). | `ofFn_eq_init_append`, `ofFn_splitCoins_*`, a `splitBits = splitCoins` bridge; worker promotion list `evidence/PROMOTION.md` (exchange `9ad236d1`) | Open (deferred) | `inputWord_take` (Gate 24 G24-01) and `inputWord_split` re-pointed to `take_ofFn_castLE` / `ofFn_eq_init_append` by LE-reuse `d356381a` (#307); the rest: re-point and promote in a later job. |
| DL-42 | hash-sign fill (delivery review 2026-11-14): `HashSignForward.roundWord`/`handler` repeats the `Games/Forwarding` `fwdRun`/`fwdHandler` pattern with a hashed query and different widths (disclosed); `splitBits_pad_concat` is a corollary of `Games.padFin_append_split`; `expect_simulate_sample_once` near `Games.expect_simulate_eager`; `MachineCodec.ext_of_fields`, `forgerCodec_eq_bitCodec`, `eq_pure_of_cost_zero` overlap the parallel lamport delivery's `lamport_codec_ext`, `lamport_forgerCodec`, `exists_pure_of_cost_zero`. | `Games/Forwarding` (a query-map `fwdHandler`), `Games/BitCodec`, `Games/Hopping`, `Games/Machines` | Open (deferred) | Generalize `fwdHandler`; promote the codec/cost facts to `Games/Machines` (no attribute) and fold the lamport copies once both units have landed. |
| DL-43 | lamport fill (delivery review 2026-11-14): **undisclosed** `LamportFill.signatureBlock σ i` = `FunFamily.blocks n n σ i` (via `blocks_apply`; DL-9 class); near relatives `Blocks.flatten_ofFn_update` (`CommitmentLemmas.ofFn_update_eq`), `Averaging.expect_favourable_of_success` (`ProbComp` counterpart of `HardcoreBit.uprob_mul_le_uexp`). Overlaps with hash-sign are DL-42. Also the follow-up (Seyoon, 2026-11-14): restate the frozen `lamport_oneTimeSecure` hypothesis `f` over `Fin (var.eval n)` with a published reader, clearing its 16 seal-B failures. | `FunFamily.blocks`; `CommitmentLemmas`; `HardcoreBit` | Open (deferred) | Re-point `signatureBlock`; promote the averaging lemma; the frozen-statement restatement needs its own gate. |

## ===== TCSlib/Cryptography/SecureComputation/SpecialEncryptionMulti.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.SpecialEncryptionSecurity

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Joint, length-generic multi-message security of special encryption (statement phase)

[PS10, Algorithm 157.2] encrypts `m` as `⟨r, (0^n ‖ m) ⊕ f_k(r)⟩`. Yao's protocol uses it in two
layers with two pseudorandom families `G₁` (`2n`-bit outputs, `n`-bit messages) and `G₂`
(`n + (4n + 2)`-bit outputs, `(4n + 2)`-bit messages), and one wire key may key both
(`GarblingSpecial.lean`, `Yao.lean`). The hybrid of `yaoHybrid_simulators` (step 3) needs
multi-message security of both layers *under one key*. Under the joint hypothesis `hG₁₂`, both
layers read their pads from one family `G = G₁ ‖ G₂`, at different offsets.

This module states that property for any `PRFOut` family `G` with `ℓ(n)`-bit outputs. A
ciphertext is cut from a **slice** of `G_k(r)`: the pad of the `i`-th ciphertext is
`G_k(r_i)_{[o_i, o_i + n + ℓ_i)}` for an offset `o_i` and a message length `ℓ_i`, both chosen
per ciphertext. Polynomially many slice ciphertexts under one key `k ← U_n`, with independent
nonces `r_i ← U_n`, are indistinguishable for any two message vectors, uniformly in the slices.
The frozen `specialScheme_multiMessageSecure` (one family, `n`-bit messages) is the corollary
with every slice `(0, n)` (`specialScheme_multiMessageSecure_of_joint`, proved here).

**Placement.** A new module beside `SpecialEncryptionSecurity.lean`, not inside it: this
statement PR is additive and leaves that file (frozen statements, owned by the garbling unit)
byte-identical. It imports `SpecialEncryptionSecurity` for `PRFOut` and `specialScheme`;
`yaoHybrid_simulators`' helper modules import it.

**B3.** The statement uses only existing definitions (`PRFOut`, `spEncStr`, the private-key
`encodeList`, `distAdv`, `NUPPT.distinguisherL`). Its proof needs the PRF hybrid machinery with
`ℓ`-bit outputs, which the separate job `prf-long` provides (ruling B3, 2026-11-14).

## Main definitions

* `SecureComputation.sliceEnc`: Algorithm 157.2 with the pad `G_k(r)_{≥o}` (a slice of `G_k(r)`).
* `SecureComputation.sliceMultiEncDist`: `q + 1` slice ciphertexts under one key.
* `SecureComputation.SliceMultiMessageSecure`: their indistinguishability for any two message
  vectors, uniformly in the slices.

## Main results

* `SecureComputation.sliceMultiMessageSecure_of_prfOut` (stated; `sorry` under a sketch): every
  `PRFOut` family is slice multi-message secure (ruling B1, 2026-11-14).
* `SecureComputation.specialScheme_multiMessageSecure_of_joint` (proved): the frozen Claim
  157.a (i) follows.
* `SecureComputation.sliceEnc_eq_spEncStr`, `sliceEnc_append_left`, `sliceEnc_append_right`
  (proved): slice ciphertexts are special ciphertexts, in particular those of the two layers of
  `nestedSpecial` under `G₁ ‖ G₂`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §3.7 (Definition 93.1, Theorem 99.2) and §6.2.2 (Algorithm 157.2, book pp. 156–157).
* [LP09] Y. Lindell, B. Pinkas, *A proof of security of Yao's protocol for two-party computation*,
  Journal of Cryptology 22(2), 2009, pp. 161–188 (the hybrid with one inactive key per step).
-/

namespace TCSlib.Cryptography.SecureComputation

open Complexity Turing TCSlib.Cryptography

/-! ### Slice ciphertexts -/

/-- **A slice ciphertext**: Algorithm 157.2 [PS10, §6.2.2] under the key `k` with nonce `r`, whose
pad is the slice `p = G_k(r)_{≥o}` of the family's output from offset `o`. That is `spEncStr`
with the constant evaluator `p`, the ciphertext `⟨r, p_{<n} ‖ (m ⊕ p_{≥n})⟩`, where `m` uses
the pad bits `G_k(r)_{[o + n, o + n + |m|)}`. -/
def sliceEnc {L : ℕ → ℕ} (G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L n) → Bool))
    (n o : ℕ) (k r : Fin n → Bool) (m : List Bool) : List Bool :=
  spEncStr (fun _ => (List.ofFn (G n k r)).drop o) (List.ofFn k) m (List.ofFn r)

/-- A slice ciphertext is `spEncStr` with the constant pad `G_k(r)_{≥o}`:
`sliceEnc G n o k r m = spEncStr (fun _ => ⟦G_k(r)⟧.drop o) ⟦k⟧ m ⟦r⟧`. -/
theorem sliceEnc_eq {L : ℕ → ℕ} (G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L n) → Bool))
    (n o : ℕ) (k r : Fin n → Bool) (m : List Bool) :
    sliceEnc G n o k r m =
      spEncStr (fun _ => (List.ofFn (G n k r)).drop o) (List.ofFn k) m (List.ofFn r) := rfl

/-- **Slices of an evaluated family**: if `E` evaluates `G` (`E(⟨s, x⟩) = G_s(x)`), the slice
ciphertext from offset `o` is the special ciphertext with the evaluator `z ↦ E(z)_{≥o}`:
`sliceEnc G n o k r m = spEncStr (fun z => (E z).drop o) ⟦k⟧ m ⟦r⟧`. -/
theorem sliceEnc_eq_spEncStr {L : ℕ → ℕ}
    {G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L n) → Bool)} {E : List Bool → List Bool}
    (hGE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
      List.ofFn (G n s x))
    (n o : ℕ) (k r : Fin n → Bool) (m : List Bool) :
    sliceEnc G n o k r m = spEncStr (fun z => (E z).drop o) (List.ofFn k) m (List.ofFn r) := by
  rw [sliceEnc_eq, spEncStr_eq, spEncStr_eq, hGE]

/-- Masking with a longer pad uses only its first `|m|` bits. -/
private theorem zipWith_xor_append_of_le : ∀ (m p b : List Bool), m.length ≤ p.length →
    List.zipWith xor m (p ++ b) = List.zipWith xor m p
  | [], _, _, _ => by simp
  | _ :: _, [], _, h => by simp at h
  | a :: m, c :: p, b, h => by
    simp only [List.cons_append, List.zipWith_cons_cons, List.cons.injEq, true_and]
    exact zipWith_xor_append_of_le m p b (by simpa using h)

/-- **The inner layer as a slice of `G₁ ‖ G₂`**: if `⟦G_k(r)⟧ = ⟦G₁_k(r)⟧ ++ ⟦G₂_k(r)⟧` and `E₁`
evaluates `G₁` (`2n`-bit outputs), then for `|m| ≤ n` the slice from offset `0` is the
`G₁`-ciphertext: `sliceEnc G n 0 k r m = spEncStr E₁ ⟦k⟧ m ⟦r⟧`. -/
theorem sliceEnc_append_left {L L₂ : ℕ → ℕ}
    {G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L n) → Bool)}
    {G₁ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (n + n) → Bool)}
    {G₂ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L₂ n) → Bool)} {E₁ : List Bool → List Bool}
    (hG : ∀ n (s x : Fin n → Bool),
      List.ofFn (G n s x) = List.ofFn (G₁ n s x) ++ List.ofFn (G₂ n s x))
    (hGE₁ : ∀ n (s x : Fin n → Bool), E₁ (pairEncode (List.ofFn s) (List.ofFn x)) =
      List.ofFn (G₁ n s x))
    (n : ℕ) (k r : Fin n → Bool) {m : List Bool} (hm : m.length ≤ n) :
    sliceEnc G n 0 k r m = spEncStr E₁ (List.ofFn k) m (List.ofFn r) := by
  have h₁ : (List.ofFn (G₁ n k r)).length = n + n := List.length_ofFn
  rw [sliceEnc_eq, spEncStr_eq, spEncStr_eq, hGE₁, List.drop_zero, hG, List.length_ofFn,
    List.take_append_of_le_length (by omega), List.drop_append_of_le_length (by omega),
    zipWith_xor_append_of_le _ _ _ (by rw [List.length_drop]; omega)]

/-- **The outer layer as a slice of `G₁ ‖ G₂`**: if `⟦G_k(r)⟧ = ⟦G₁_k(r)⟧ ++ ⟦G₂_k(r)⟧` with `G₁`
of `2n`-bit outputs and `E₂` evaluates `G₂`, the slice from offset `2n` is the `G₂`-ciphertext:
`sliceEnc G n (n + n) k r m = spEncStr E₂ ⟦k⟧ m ⟦r⟧`, for every message `m`. -/
theorem sliceEnc_append_right {L L₂ : ℕ → ℕ}
    {G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L n) → Bool)}
    {G₁ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (n + n) → Bool)}
    {G₂ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L₂ n) → Bool)} {E₂ : List Bool → List Bool}
    (hG : ∀ n (s x : Fin n → Bool),
      List.ofFn (G n s x) = List.ofFn (G₁ n s x) ++ List.ofFn (G₂ n s x))
    (hGE₂ : ∀ n (s x : Fin n → Bool), E₂ (pairEncode (List.ofFn s) (List.ofFn x)) =
      List.ofFn (G₂ n s x))
    (n : ℕ) (k r : Fin n → Bool) (m : List Bool) :
    sliceEnc G n (n + n) k r m = spEncStr E₂ (List.ofFn k) m (List.ofFn r) := by
  rw [sliceEnc_eq, spEncStr_eq, spEncStr_eq, hGE₂, hG, List.drop_left' List.length_ofFn]

/-! ### Joint multi-message security -/

/-- **`q + 1` slice ciphertexts under one key** (the sampler of [PS10, Definition 93.1], with
slices): from the key `k` and the nonces `r_0, …, r_q` (the seed `(k, r)`, uniform), the
`encodeList` of `sliceEnc G n o_i k r_i m_i` for `i ≤ q`, i.e. of
`⟨r_i, (0^n ‖ m_i) ⊕ G_k(r_i)_{[o_i, o_i + n + ℓ_i)}⟩` with `m_i ∈ {0,1}^{ℓ_i}`. -/
def sliceMultiEncDist {L : ℕ → ℕ}
    (G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L n) → Bool)) (n q : ℕ)
    (o len : Fin (q + 1) → ℕ) (m : ∀ i, Fin (len i) → Bool) :
    (Fin n → Bool) × (Fin (q + 1) → Fin n → Bool) → List Bool :=
  fun t => PrivateKeyScheme.encodeList
    (List.ofFn fun i => sliceEnc G n (o i) t.1 (t.2 i) (List.ofFn (m i)))

/-- The slice sampler at the seed `t = (k, r)` is the `encodeList` of the `q + 1` ciphertexts
`sliceEnc G n o_i k r_i ⟦m_i⟧`. -/
theorem sliceMultiEncDist_apply {L : ℕ → ℕ}
    (G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L n) → Bool)) (n q : ℕ)
    (o len : Fin (q + 1) → ℕ) (m : ∀ i, Fin (len i) → Bool)
    (t : (Fin n → Bool) × (Fin (q + 1) → Fin n → Bool)) :
    sliceMultiEncDist G n q o len m t = PrivateKeyScheme.encodeList
      (List.ofFn fun i => sliceEnc G n (o i) t.1 (t.2 i) (List.ofFn (m i))) := rfl

/-- **Slice multi-message security** of a family `G` with `L(n)`-bit outputs ([PS10,
Definition 93.1], with slices and one key): for every non-uniform PPT `D` and polynomial `q`
there is a negligible `ε` such that for all `n`, all offsets and lengths `o, ℓ ∈ ℕ^{q(n)+1}`
with `o_i + n + ℓ_i ≤ L(n)`, and all `m, m'` with `m_i, m'_i ∈ {0,1}^{ℓ_i}`,
`|Pr[k, r ← U : D(1^n, ⟨Enc^{o_i}_k(m_i; r_i)⟩_i) = 1] − Pr[… m' …]| ≤ ε(n)`, where
`Enc^o_k(m; r) = sliceEnc G n o k r m`.

`ε` precedes the slices as well as the messages, so a reduction may choose the slices by advice.
With every slice `(0, n)` and `L(n) = 2n` this is `PrivateKeyScheme.MultiMessageSecure` of
`specialScheme` (`specialScheme_multiMessageSecure_of_joint`).

**Deviation:** `D` receives `1^n`; the ciphertexts are encoded by `encodeList` (as in
`MultiMessageSecure`). -/
def SliceMultiMessageSecure {L : ℕ → ℕ}
    (G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L n) → Bool)) : Prop :=
  ∀ (D : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ n (o len : Fin (q.eval n + 1) → ℕ), (∀ i, o i + n + len i ≤ L n) →
      ∀ m m' : ∀ i, Fin (len i) → Bool,
        distAdv (sliceMultiEncDist G n (q.eval n) o len m)
          (sliceMultiEncDist G n (q.eval n) o len m') (D.distinguisherL n) ≤ ε n

/-- The defining property of `SliceMultiMessageSecure`: for every `D` and `q` a negligible `ε`
bounds `D`'s advantage between the slice ciphertexts of any two message vectors, for every
slice vector that fits in `L(n)`. -/
theorem sliceMultiMessageSecure_iff {L : ℕ → ℕ}
    (G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L n) → Bool)) :
    SliceMultiMessageSecure G ↔ ∀ (D : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n (o len : Fin (q.eval n + 1) → ℕ), (∀ i, o i + n + len i ≤ L n) →
        ∀ m m' : ∀ i, Fin (len i) → Bool,
          distAdv (sliceMultiEncDist G n (q.eval n) o len m)
            (sliceMultiEncDist G n (q.eval n) o len m') (D.distinguisherL n) ≤ ε n := Iff.rfl

/-- **Joint, length-generic multi-message security** (ruling B1, 2026-11-14) [PS10, §6.2.2, "it
is easy to modify construction 99.1"; Definition 93.1, Theorem 99.2]: every pseudorandom family
`G` with `ℓ(n)`-bit outputs (`PRFOut ℓ G`) is slice multi-message secure. For every
non-uniform PPT `D` and polynomial `q` there is a negligible `ε` with, for all `n`, all slices
`(o_i, ℓ_i)_{i ≤ q(n)}` with `o_i + n + ℓ_i ≤ ℓ(n)` and all `m, m'` with `|m_i| = |m'_i| = ℓ_i`,
`|Pr[D(1^n, ⟨r_i, (0^n ‖ m_i) ⊕ G_k(r_i)_{[o_i, o_i+n+ℓ_i)}⟩_i) = 1] − Pr[… m' …]| ≤ ε(n)`
over `k, r_0, …, r_{q(n)} ← U_n`.

**Corollaries.**
- `specialScheme_multiMessageSecure` (frozen Claim 157.a (i)) is
  `specialScheme_multiMessageSecure_of_joint G E hE hGE (sliceMultiMessageSecure_of_prfOut hG)`:
  every slice is `(0, n)` and `ℓ(n) = 2n`.
- Step 3 of `yaoHybrid_simulators` takes `G = G₁ ‖ G₂` under `hG₁₂`, with
  `ℓ(n) = 2n + (n + (4n + 2))`. The rows under the inactive key `ι_u` where `u` is a second or
  only argument are slices `(0, n)` (`sliceEnc_append_left`: the `G₁`-ciphertexts
  `spEncStr E₁`). Those where `u` is a first argument are slices `(2n, 4n + 2)`
  (`sliceEnc_append_right`: the `G₂`-ciphertexts `spEncStr E₂`). Both fit exactly. The bound is
  uniform in the slices, so the reduction's advice may fix which rows, of which layer, it
  embeds.

**Deviations.** [PS10] states the claim for one scheme and `n`-bit messages. Here the claim is
length-generic and joint: the pads of different ciphertexts may come from different slices
of one family under one key. The fit `o_i + n + ℓ_i ≤ ℓ(n)` keeps every pad inside `G_k(r_i)`.

**Proof sketch.** As [PS10, Theorem 99.2] (`prfScheme_multiMessageSecure`), with `ℓ`-bit
outputs. Fix `n` and let `A(n)` be `D`'s largest advantage over the finitely many fitting slice
vectors and message pairs (each `o_i, ℓ_i ≤ ℓ(n)`).
1. *PRF step.* For `b ∈ {0, 1}` the oracle machine `D_b` has as advice the maximizing slices and
   the message vector `m` (`b = 0`) or `m'` (`b = 1`), all of polynomial length. It draws the
   `r_i`, queries `O(r_i)` once each (`q(n) + 1` queries), forms each ciphertext from the slice
   of the answer, and runs `D`. Against `G_k` it is the slice sampler; against a random function
   `F` with `ℓ(n)`-bit outputs it is the same sampler for `F`. Its advantage is negligible by
   `hG.pseudorandom`.
2. *Random function.* If the `r_i` are distinct, the values `F(r_i)` are independent and uniform.
   Within one ciphertext the revealed prefix and the mask are disjoint bits of the slice, so each
   ciphertext is `⟨r_i, u_i⟩` with `u_i` uniform of length `n + ℓ_i`, whatever the message. The
   laws for `m` and `m'` agree off the collision event, which has probability at most
   `C(q(n) + 1, 2) · 2^{-n}` (`MultiMsg.negligible_choose_div_two_pow`).
3. *Total.* `A(n) ≤ adv(D_0) + adv(D_1) + C(q(n) + 1, 2) · 2^{-n}`, which is negligible. Take
   `ε = A`. The ℓ-output PRF hybrid machinery is supplied by `prf-long` (ruling B3). -/
theorem sliceMultiMessageSecure_of_prfOut {ℓ : PolyExpr}
    {G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (ℓ.eval n) → Bool)} (hG : PRFOut ℓ G) :
    SliceMultiMessageSecure G := by
  sorry

/-! ### The frozen Claim 157.a (i) as a corollary -/

section Corollary

variable (G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (n + n) → Bool))
  (E : List Bool → List Bool) (hE : PolyTimeComputable E)
  (hGE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (G n s x))

/-- The key generator of `specialScheme` outputs its coins: `Gen(1^n; rg) = ⟦rg⟧`. -/
private theorem specialScheme_gen_runAt (n : ℕ) :
    ∀ rg : (specialScheme G E hE hGE).gen.Coins n,
      (specialScheme G E hE hGE).gen.runAt n [] rg = List.ofFn rg := by
  rw [specialScheme_gen]
  intro rg
  exact runAt_coinKey .var n rg

/-- The encryption machine of `specialScheme` is `spEncStr` with its coins as the nonce. -/
private theorem specialScheme_enc_runAt (n : ℕ) :
    ∀ (k m : List Bool) (re : (specialScheme G E hE hGE).enc.Coins n),
      (specialScheme G E hE hGE).enc.runAt n (pairEncode k m) re =
        spEncStr E k m (List.ofFn re) := by
  rw [specialScheme_enc]
  intro k m re
  exact runAt_spEnc hE .var n k m re

/-- The key coins of `specialScheme` as an `n`-bit key, keeping the string. -/
private noncomputable def specialKeyEq (n : ℕ) :
    (specialScheme G E hE hGE).gen.Coins n ≃ (Fin n → Bool) :=
  (NUPPT.coinsCongr (by rw [specialScheme_gen]) n).trans
    ((NUPPT.coinsEquiv_ofPolyTimeUniform polyTimeComputable_pairSndD .var n).trans
      (Equiv.arrowCongr (finCongr (PolyExpr.eval_var n)) (Equiv.refl Bool)))

/-- `⟦specialKeyEq n rg⟧ = ⟦rg⟧`. -/
private theorem ofFn_specialKeyEq (n : ℕ) (rg : (specialScheme G E hE hGE).gen.Coins n) :
    List.ofFn (specialKeyEq G E hE hGE n rg) = List.ofFn rg := by
  rw [specialKeyEq, Equiv.trans_apply, Equiv.trans_apply, ofFn_arrowCongr_finCongr,
    NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn, NUPPT.coinsCongr_ofFn]

/-- The encryption coins of `specialScheme` as an `n`-bit nonce, keeping the string. -/
private noncomputable def specialNonceEq (n : ℕ) :
    (specialScheme G E hE hGE).enc.Coins n ≃ (Fin n → Bool) :=
  (NUPPT.coinsCongr (by rw [specialScheme_enc]) n).trans
    ((NUPPT.coinsEquiv_ofPolyTimeUniform (polyTimeComputable_spEncFun hE) .var n).trans
      (Equiv.arrowCongr (finCongr (PolyExpr.eval_var n)) (Equiv.refl Bool)))

/-- `⟦specialNonceEq n re⟧ = ⟦re⟧`. -/
private theorem ofFn_specialNonceEq (n : ℕ) (re : (specialScheme G E hE hGE).enc.Coins n) :
    List.ofFn (specialNonceEq G E hE hGE n re) = List.ofFn re := by
  rw [specialNonceEq, Equiv.trans_apply, Equiv.trans_apply, ofFn_arrowCongr_finCongr,
    NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn, NUPPT.coinsCongr_ofFn]

/-- **The frozen Claim 157.a (i) from the joint lemma** [PS10, §6.2.2, Definition 93.1]: if the
length-doubling family `G` is slice multi-message secure, then `specialScheme G E hE hGE` is
multi-message secure. With `sliceMultiMessageSecure_of_prfOut` this gives
`specialScheme_multiMessageSecure`.

**Proof sketch.** Take every slice to be `(0, n)`; it fits, as `0 + n + n ≤ 2n`. Relabel the
coins of `Gen` and `Enc` as an `n`-bit key and `n`-bit nonces, keeping their strings. Under this
bijection the scheme's multi-message sampler is the slice sampler pointwise: `Gen` outputs its
coins (`runAt_coinKey`), `Enc` is `spEncStr E` (`runAt_spEnc`), and a slice from offset `0` is
`spEncStr E` (`sliceEnc_eq_spEncStr`). Acceptance probabilities are invariant under relabelling
the seed (`acceptProb_comp_equiv`), so the slice bound applies verbatim. -/
theorem specialScheme_multiMessageSecure_of_joint (h : SliceMultiMessageSecure G) :
    (specialScheme G E hE hGE).MultiMessageSecure := by
  rw [PrivateKeyScheme.multiMessageSecure_iff]
  intro D q
  obtain ⟨ε, hε, hb⟩ := (sliceMultiMessageSecure_iff G).mp h D q
  refine ⟨ε, hε, fun n m m' => ?_⟩
  let e : (specialScheme G E hE hGE).gen.Coins n ×
      (Fin (q.eval n + 1) → (specialScheme G E hE hGE).enc.Coins n) ≃
      (Fin n → Bool) × (Fin (q.eval n + 1) → Fin n → Bool) :=
    (specialKeyEq G E hE hGE n).prodCongr
      (Equiv.piCongrRight fun _ => specialNonceEq G E hE hGE n)
  have hX : ∀ v : Fin (q.eval n + 1) → Fin n → Bool,
      (specialScheme G E hE hGE).multiEncDist n (q.eval n) v =
        fun t => sliceMultiEncDist G n (q.eval n) (fun _ => 0) (fun _ => n) v (e t) := by
    intro v
    funext t
    rw [PrivateKeyScheme.multiEncDist_apply, sliceMultiEncDist_apply]
    refine congrArg PrivateKeyScheme.encodeList (congrArg List.ofFn (funext fun i => ?_))
    rw [specialScheme_gen_runAt, specialScheme_enc_runAt, sliceEnc_eq_spEncStr hGE]
    simp only [e, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.piCongrRight_apply,
      Pi.map_apply, List.drop_zero, ofFn_specialKeyEq, ofFn_specialNonceEq]
  rw [distAdv_def, hX m, hX m', acceptProb_comp_equiv, acceptProb_comp_equiv, ← distAdv_def]
  exact hb n (fun _ => 0) (fun _ => n) (fun _ => by show 0 + n + n ≤ n + n; omega) m m'

end Corollary

end TCSlib.Cryptography.SecureComputation

## ===== TCSlib/Cryptography/SecureComputation.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Defs
import TCSlib.Cryptography.SecureComputation.ObliviousTransfer
import TCSlib.Cryptography.SecureComputation.SpecialEncryption
import TCSlib.Cryptography.SecureComputation.SpecialEncryptionSecurity
import TCSlib.Cryptography.SecureComputation.SpecialEncryptionMulti
import TCSlib.Cryptography.SecureComputation.Garbling
import TCSlib.Cryptography.SecureComputation.GarblingSpecial
import TCSlib.Cryptography.SecureComputation.GarblingSecurity
import TCSlib.Cryptography.SecureComputation.Hybrid
import TCSlib.Cryptography.SecureComputation.Compose
import TCSlib.Cryptography.SecureComputation.ComposePhases
import TCSlib.Cryptography.SecureComputation.ComposeSecurity
import TCSlib.Cryptography.SecureComputation.Yao
import TCSlib.Cryptography.SecureComputation.YaoReal

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Secure two-party computation

The definitions, constructions and theorem statements of [PS10, §6.2] and [Gol04, §7.3].
The individual modules record deviations, proof sketches and outstanding admissions.

## Main definitions

See the definitions and construction modules listed below.

## Main results

See the theorem statements and correctness results in the constituent modules.

## Contents

* `Defs` — honest-but-curious security with efficient parties and bounded messages.
* `ObliviousTransfer` — five-message oblivious transfer from trapdoor permutations.
* `SpecialEncryption` — the nested special-encryption construction and correctness.
* `SpecialEncryptionSecurity` — special-encryption security statements.
* `SpecialEncryptionMulti` — joint, length-generic multi-message security of special encryption.
* `Garbling` — deterministic garbling and correctness.
* `GarblingSpecial` — garbling with the special-encryption construction.
* `GarblingSecurity` — the probabilistic garbling-security statement.
* `Hybrid` — the OT-hybrid computation model.
* `Compose` — sequential composition of a hybrid protocol with an implementation.
* `ComposePhases` — the phase identities for sequential composition.
* `ComposeSecurity` — the composition security statement.
* `Yao` — Yao’s protocol in the OT-hybrid model.
* `YaoReal` — the real protocol and its security statement by composition.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, 3rd ed., January 2010.
* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2*, Cambridge University Press, 2004.
-/

## ===== TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.SpecialEncryption
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRG
import TCSlib.Cryptography.Pseudorandom.Generators.Asymptotic.FromPermutation
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Run
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The special encryption scheme of Yao's protocol: security (statement phase)

[PS10, Algorithm 157.2] as a `PrivateKeyScheme`, and Claim 157.a (inventory): the scheme is
multi-message secure, and a ciphertext decrypted under an independent key gives `⊥` except with
negligible probability ([PS10, §6.2.2], "the extra property"). The algorithms are in
`SpecialEncryption.lean`.

**The length-doubling PRF.** It is a keyed family with `n`-bit keys and inputs and `2n`-bit
outputs, pseudorandom as an oracle ensemble against random functions with `2n`-bit outputs
(`PRFOut`). This is the ch. 2–4 layer's Definition 96.2 (`PRF`) with the output length a
parameter; `OracleEnsemble.keyed` already allows any output length.

## Main definitions

* `SecureComputation.PRFOut`: a pseudorandom function family with `ℓ₂(n)`-bit outputs.
* `SecureComputation.specialScheme`: Algorithm 157.2 as a `PrivateKeyScheme` (`n`-bit messages),
  correctness proved.

## Main results

* `SecureComputation.specialScheme_multiMessageSecure`, `spDecStr_wrongKey`,
  `specialScheme_wrongKey` (Claim 157.a, stated; `sorry`s under sketches).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2.2, Algorithm 157.2 (book pp. 156–157), and Definitions 93.1 and 96.2.
-/

namespace TCSlib.Cryptography.SecureComputation

open Complexity Turing TCSlib.Cryptography

/-! ### Pseudorandom functions with any output length -/

/-- **A pseudorandom function family with `ℓ₂(n)`-bit outputs** [PS10, Definition 96.2, with the
output length a parameter]: keys and inputs of `n` bits. (1) A polynomial-time evaluator `E`
computes `f_s(x)` from `⟨s, x⟩`. (2) The keyed ensemble `{s ← U_n : f_s}` is
oracle-indistinguishable from the random functions `{0,1}^n → {0,1}^{ℓ₂(n)}`. With `ℓ₂ = n + n`
it is the source's length-doubling family. -/
structure PRFOut (ℓ₂ : PolyExpr)
    (G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (ℓ₂.eval n) → Bool)) : Prop where
  /-- Clause (1): `f_s(x)` is polynomial-time computable from `⟨s, x⟩`. -/
  easy : ∃ E : List Bool → List Bool, PolyTimeComputable E ∧
    ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G n s x)
  /-- Clause (2): `{s ← U_n : f_s} ≈ {F ← RF : F}` as oracle ensembles. -/
  pseudorandom : (OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := ℓ₂) G).Indist
    (OracleEnsemble.random .var ℓ₂)

/-- With `n`-bit outputs, `PRFOut` is the ch. 2–4 layer's `PRF` (duplication-ledger item DL-8:
`PRFOut` generalizes `PRF`, and agrees with it at `ℓ₂ = n`). -/
theorem prfOut_var_iff (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)) :
    PRFOut .var F ↔ PRF F :=
  ⟨fun h => ⟨h.easy, h.pseudorandom⟩, fun h => ⟨h.easy, h.pseudorandom⟩⟩

variable (G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (n + n) → Bool))
  (E : List Bool → List Bool) (hE : PolyTimeComputable E)
  (hGE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (G n s x))

/-- **The special encryption scheme** [PS10, Algorithm 157.2] as a `PrivateKeyScheme` with
`n`-bit messages, for a length-doubling family `G` with evaluator `E`: the key is `Gen`'s `n`
coins, `Enc` draws `r` as its `n` coins, and `Dec` is deterministic. -/
@[simps (config := { isSimp := false }) gen enc dec]
noncomputable def specialScheme : PrivateKeyScheme where
  gen := NUPPT.ofPolyTimeUniform polyTimeComputable_pairSndD .var
  enc := NUPPT.ofPolyTimeUniform (polyTimeComputable_spEncFun hE) .var
  dec := NUPPT.ofPolyTimeUniform (polyTimeComputable_spDecFun hE) (.const 0)
  gen_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  enc_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  dec_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  correct := by
    intro n m rg re rd
    rw [runAt_coinKey, runAt_spEnc hE, runAt_spDec hE]
    have hk : (List.ofFn rg).length = n := by
      rw [List.length_ofFn, NUPPT.coinLen_eq, NUPPT.coins_ofPolyTimeUniform,
        PolyExpr.eval_var]
    have hr : (List.ofFn re).length = n := by
      rw [List.length_ofFn, NUPPT.coinLen_eq, NUPPT.coins_ofPolyTimeUniform,
        PolyExpr.eval_var]
    have hp : (E (pairEncode (List.ofFn rg) (List.ofFn re))).length = n + n := by
      have hrg := (List.length_ofFn (f := rg)).symm.trans hk
      have hre := (List.length_ofFn (f := re)).symm.trans hr
      rw [List.ofFn_congr hrg rg, List.ofFn_congr hre re, hGE, List.length_ofFn]
    rw [spDecStr_spEncStr E hk (by simp) hr hp, Option.getD_some]
    exact decodeFin_ofFn m

/-! ### Claim 157.a -/

/-- **Claim 157.a (i): the special scheme is multi-message secure** [PS10, §6.2.2, "it is easy to
modify construction 99.1"] when `G` is a length-doubling PRF.

**Proof sketch.** As [PS10, Theorem 99.2] for Algorithm 99.1 (`prfScheme_multiMessageSecure`):
replace `f_k` by a random function with `2n`-bit outputs (PRF security, one oracle query per
ciphertext); then the pads of distinct `r`'s are independent uniform `2n`-bit strings, so the
ciphertexts are independent of the messages unless two `r`'s collide, with probability at most
`C(q(n)+1, 2) · 2^{-n}`. The zero prefix `0^n` is masked like the message. -/
theorem specialScheme_multiMessageSecure (hG : PRFOut (.add .var .var) G) :
    (specialScheme G E hE hGE).MultiMessageSecure := by
  sorry

/-- **Claim 157.a (ii), on strings: a wrong key gives `⊥`** [PS10, §6.2.2, "the extra property"]
for any polynomial message length `ℓ`: for `G` a PRF with `n + ℓ(n)`-bit outputs and every
`ℓ(n)`-bit message, encrypting under `k` and decrypting under an independent `k'` gives `⊥`
except with negligible probability.

**Proof sketch.** Decryption under `k'` succeeds only if `f_k(r)_{<n} = f_{k'}(r)_{<n}`. The
distinguisher with oracle `O` samples `k'` and `r`, queries `O(r)`, and accepts iff the first `n`
bits agree with `f_{k'}(r)`. Against a random function this has probability `2^{-n}`, so against
`f_k` it has probability at most `2^{-n}` plus the PRF advantage: negligible. The guard does not
fire on honest ciphertexts. -/
theorem spDecStr_wrongKey (ℓ : PolyExpr)
    (G' : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin ((PolyExpr.add .var ℓ).eval n) → Bool))
    (E' : List Bool → List Bool)
    (hGE' : ∀ n (s x : Fin n → Bool), E' (pairEncode (List.ofFn s) (List.ofFn x)) =
      List.ofFn (G' n s x))
    (hG' : PRFOut (.add .var ℓ) G') :
    ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n (m : Fin (ℓ.eval n) → Bool),
      1 - ε n < uprob (fun t : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
        spDecStr E' n (ℓ.eval n) (List.ofFn t.2.1)
          (spEncStr E' (List.ofFn t.1) (List.ofFn m) (List.ofFn t.2.2)) = none) := by
  sorry

/-- **Claim 157.a (ii) for the scheme**: under an independent key, `Dec` returns `⊥` (an output
that decodes to no `n`-bit message) except with negligible probability, the source's
`Pr[k, k' ← Gen(1^n), c ← Enc_k(m) : Dec_{k'}(c) = ⊥] > 1 − ε(n)`.

**Proof sketch.** `runAt_spEnc` and `runAt_spDec` reduce it to `spDecStr_wrongKey` at `ℓ = n`;
the `⊥` string `1^{n+1}` decodes to no `n`-bit message, and a `some` output has `n` bits. -/
theorem specialScheme_wrongKey (hG : PRFOut (.add .var .var) G) :
    ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n (m : Fin n → Bool),
      1 - ε n < uprob (fun t : (specialScheme G E hE hGE).gen.Coins n ×
          (specialScheme G E hE hGE).gen.Coins n × (specialScheme G E hE hGE).enc.Coins n ×
          (specialScheme G E hE hGE).dec.Coins n =>
        decodeFin n ((specialScheme G E hE hGE).dec.runAt n
          (pairEncode ((specialScheme G E hE hGE).gen.runAt n [] t.2.1)
            ((specialScheme G E hE hGE).enc.runAt n
              (pairEncode ((specialScheme G E hE hGE).gen.runAt n [] t.1) (List.ofFn m)) t.2.2.1))
          t.2.2.2) = none) := by
  sorry

end TCSlib.Cryptography.SecureComputation

## ===== TCSlib/Cryptography/SecureComputation/SpecialEncryption.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Complexity.Randomized.PPT
import TCSlib.Complexity.Randomized.Closure
import TCSlib.Complexity.Randomized.Primitives
import TCSlib.Complexity.Randomized.Repetition
import TCSlib.Cryptography.Asymptotic.Adversary

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The special encryption scheme of Yao's protocol: the algorithms (statement phase)

[PS10, Algorithm 157.2]: for a length-doubling pseudorandom function family
`{f_s : {0,1}^{|s|} → {0,1}^{2|s|}}`:
- `Gen(1^n)` outputs `k ← U_n`;
- `Enc_k(m)` outputs `(r, 0^n ‖ m ⊕ f_k(r))` for `r ← U_n`;
- `Dec_k(c₁, c₂)` computes `m₀ ‖ m₁ = c₂ ⊕ f_k(c₁)` with `|m₀| = n`, and outputs `m₁` if
  `m₀ = 0^n`, and `⊥` otherwise.

This module has the algorithms, on strings and as machines, with their correctness. The scheme
as a `PrivateKeyScheme` and Claim 157.a are in `SpecialEncryptionSecurity.lean`. The garbling of
Yao's protocol nests two encryptions (`GarblingSpecial.lean`), so the string-level scheme
(`spEncStr`, `spDecStr`) takes any message length `ℓ`, with a pad of `n + ℓ` bits.

**Deviations.**
- `x` for `m`: a source typo, read as `m`.
- `(0^n ‖ m) ⊕ p` is computed as `p_{<n} ‖ (m ⊕ p_{≥n})` for the pad `p = f_k(r)`. The test
  "`m₀ = 0^n`" is computed as `c₂,_{<n} = p_{<n}`. Both are equalities of strings.
- `Dec` checks the key, nonce-component and body-component lengths before evaluating `E`,
  then checks the pad prefix. It uses total pair projections and does not separately require
  successful pair parsing. At `n = ℓ = 0`, the malformed empty ciphertext with an empty key
  therefore returns `some []`. The length checks protect the stated `n`-bit evaluator domain;
  universal malformed-input rejection is not claimed.
- `⊥` of the machine `Dec` is the `(n + 1)`-bit string `1^{n+1}`, which decodes to no message.

## Main definitions

* `SecureComputation.spEncStr`, `spDecStr`: Algorithm 157.2 on strings, for any message length.
* `SecureComputation.spEncFun`, `spDecFun`: the algorithms on the machine layout (`n`-bit
  messages).

## Main results

* `SecureComputation.spDecStr_spEncStr`, `length_spEncStr`: decryption inverts encryption, and the
  ciphertext length.
* `SecureComputation.polyTimeComputable_spEncFun`, `polyTimeComputable_spDecFun`, `runAt_spEnc`,
  `runAt_spDec`: the machines.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2.2, Algorithm 157.2 (book pp. 156–157).
-/

namespace TCSlib.Cryptography.SecureComputation

open Complexity Turing TCSlib.Cryptography

/-! ### The scheme on strings -/

/-- **`Enc_k(m)` with coins `r`** [PS10, Algorithm 157.2], `n = |r|`: the pad `p = E(⟨k, r⟩)`
and the ciphertext `⟨r, p_{<n} ‖ (m ⊕ p_{≥n})⟩`, that is `⟨r, (0^n ‖ m) ⊕ p⟩`. -/
def spEncStr (E : List Bool → List Bool) (k m r : List Bool) : List Bool :=
  pairEncode r ((E (pairEncode k r)).take r.length ++
    List.zipWith xor m ((E (pairEncode k r)).drop r.length))

/-- Encryption pairs the nonce with a pad prefix and the XOR-masked message. -/
theorem spEncStr_eq (E : List Bool → List Bool) (k m r : List Bool) :
    spEncStr E k m r = pairEncode r ((E (pairEncode k r)).take r.length ++
      List.zipWith xor m ((E (pairEncode k r)).drop r.length)) := rfl

/-- **`Dec_k(c)`** [PS10, Algorithm 157.2] at parameter `n` for `ℓ`-bit messages: `none` (`⊥`)
unless `k` and `r` have `n` bits and `c₂` has `n + ℓ`; then, with the pad `p = E(⟨k, r⟩)`, the
message `c₂,_{≥n} ⊕ p_{≥n}` if `c₂,_{<n} = p_{<n}` ("`m₀ = 0^n`"), and `⊥` otherwise.
Here `r` and `c₂` are the total pair projections; successful parsing is not an additional
test. In particular `n = ℓ = 0`, `k = c = []` returns `some []`. -/
def spDecStr (E : List Bool → List Bool) (n ℓ : ℕ) (k c : List Bool) : Option (List Bool) :=
  if k.length = n ∧ (pairFstD c).length = n ∧ (pairSndD c).length = n + ℓ then
    if (pairSndD c).take n = (E (pairEncode k (pairFstD c))).take n then
      some (List.zipWith xor ((pairSndD c).drop n) ((E (pairEncode k (pairFstD c))).drop n))
    else none
  else none

/-- Decryption checks the key, nonce and ciphertext lengths and the pad prefix, returning
only the unmasked suffix when every check succeeds. -/
theorem spDecStr_eq (E : List Bool → List Bool) (n ℓ : ℕ) (k c : List Bool) :
    spDecStr E n ℓ k c =
      if k.length = n ∧ (pairFstD c).length = n ∧ (pairSndD c).length = n + ℓ then
        if (pairSndD c).take n = (E (pairEncode k (pairFstD c))).take n then
          some (List.zipWith xor ((pairSndD c).drop n)
            ((E (pairEncode k (pairFstD c))).drop n))
        else none
      else none := rfl

/-- XOR-ing twice with the same pad, at least as long as the message, is the identity. -/
private theorem zipWith_xor_xor_self : ∀ (m p : List Bool), m.length ≤ p.length →
    List.zipWith xor (List.zipWith xor m p) p = m
  | [], _, _ => by simp
  | _ :: _, [], h => by simp at h
  | a :: m, b :: p, h => by
    simp only [List.zipWith_cons_cons, List.cons.injEq]
    exact ⟨by cases a <;> cases b <;> rfl, zipWith_xor_xor_self m p (by simpa using h)⟩

/-- **Decryption inverts encryption**: for an `n`-bit key and coins, an `ℓ`-bit message, and a
pad of `n + ℓ` bits, `Dec_k(Enc_k(m; r)) = m`. -/
theorem spDecStr_spEncStr (E : List Bool → List Bool) {n ℓ : ℕ} {k m r : List Bool}
    (hk : k.length = n) (hm : m.length = ℓ) (hr : r.length = n)
    (hp : (E (pairEncode k r)).length = n + ℓ) :
    spDecStr E n ℓ k (spEncStr E k m r) = some m := by
  subst hr
  have h1 : ((E (pairEncode k r)).take r.length).length = r.length := by
    rw [List.length_take, hp]; omega
  have h2 : ((E (pairEncode k r)).drop r.length).length = ℓ := by
    rw [List.length_drop, hp]; omega
  have hz : (List.zipWith xor m ((E (pairEncode k r)).drop r.length)).length = ℓ := by
    rw [List.length_zipWith, hm, h2]; omega
  unfold spDecStr spEncStr
  simp only [pairFstD_pairEncode, pairSndD_pairEncode]
  rw [if_pos ⟨hk, trivial, by rw [List.length_append, h1, hz]⟩, List.take_left' h1, if_pos rfl,
    List.drop_left' h1, zipWith_xor_xor_self _ _ (by rw [hm, h2])]

/-! ### The scheme as a `PrivateKeyScheme` -/

/-- `Enc` on the machine layout `⟨⟨⟨1^n, ⟨k, m⟩⟩, α⟩, r⟩`: `spEncStr` with the coin string as
`r`. -/
def spEncFun (E : List Bool → List Bool) (z : List Bool) : List Bool :=
  spEncStr E (pairFstD (NUPPT.inArg z)) (pairSndD (NUPPT.inArg z)) (NUPPT.inCoins z)

/-- The encryption adapter reads the key and message from its argument and its nonce from
its machine coin word. -/
theorem spEncFun_eq (E : List Bool → List Bool) (z : List Bool) :
    spEncFun E z = spEncStr E (pairFstD (NUPPT.inArg z))
      (pairSndD (NUPPT.inArg z)) (NUPPT.inCoins z) := rfl

/-- `Dec` on the layout `⟨⟨⟨1^n, ⟨k, c⟩⟩, α⟩, r'⟩` for `n`-bit messages: the message, or `⊥` as
the `(n + 1)`-bit string `1^{n+1}`. -/
def spDecFun (E : List Bool → List Bool) (z : List Bool) : List Bool :=
  (spDecStr E (NUPPT.inParam z).length (NUPPT.inParam z).length (pairFstD (NUPPT.inArg z))
    (pairSndD (NUPPT.inArg z))).getD (true :: NUPPT.inParam z)

/-- The decryption adapter reads both lengths from the unary parameter and returns the
specified overlong failure word if string decryption fails. -/
theorem spDecFun_eq (E : List Bool → List Bool) (z : List Bool) :
    spDecFun E z = (spDecStr E (NUPPT.inParam z).length (NUPPT.inParam z).length
      (pairFstD (NUPPT.inArg z)) (pairSndD (NUPPT.inArg z))).getD
        (true :: NUPPT.inParam z) := rfl

/-- The string-level `Enc` is polynomial-time on the layout when `E` is. -/
theorem polyTimeComputable_spEncFun {E : List Bool → List Bool} (hE : PolyTimeComputable E) :
    PolyTimeComputable (spEncFun E) := by
  have hk := polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg
  have hm := polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg
  have hr := NUPPT.polyTimeComputable_inCoins
  have hp := hE.comp (hk.pairEncode hr)
  have ht := (polyTimeComputable_pairTakePoly .var).comp (hr.pairEncode hp)
  have hd := (polyTimeComputable_pairDropPoly .var).comp (hr.pairEncode hp)
  have hx := polyTimeComputable_pairXor.comp (hm.pairEncode hd)
  have h := hr.pairEncode (ht.append hx)
  refine (congrArg PolyTimeComputable (?_ : spEncFun E = _)).mpr h
  funext z
  simp only [spEncFun, spEncStr, Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
    PolyExpr.eval_var]

/-- The guard of `Dec` (`n`-bit key and `r`, `2n`-bit `c₂`) is polynomial-time.

**Proof sketch.** Obtain the key, nonce, ciphertext body and unary parameter by polynomial-time
projections. Compare the key and nonce lengths with the parameter length. Compare the body's
length with twice that length, represented by appending the parameter word to itself. Each
comparison is a polynomial-time length test, and two Boolean conjunctions combine the three
tests into the guard. -/
private theorem polyTimeComputable_spDecGuard :
    PolyTimeComputable fun z =>
      [decide ((pairFstD (NUPPT.inArg z)).length = (NUPPT.inParam z).length ∧
        (pairFstD (pairSndD (NUPPT.inArg z))).length = (NUPPT.inParam z).length ∧
        (pairSndD (pairSndD (NUPPT.inArg z))).length =
          (NUPPT.inParam z).length + (NUPPT.inParam z).length)] := by
  have hP := NUPPT.polyTimeComputable_inParam
  have hl : ∀ g h : List Bool → List Bool, PolyTimeComputable g → PolyTimeComputable h →
      PolyTimeComputable (fun z => [decide ((g z).length = (h z).length)]) := by
    intro g h hg hh
    have h' := polyTimeComputable_lenEq.comp (hg.pairEncode hh)
    refine (congrArg PolyTimeComputable
      (?_ : (fun z => [decide ((g z).length = (h z).length)]) = _)).mpr h'
    funext z
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hArg := NUPPT.polyTimeComputable_inArg
  have h1 := hl _ _ (polyTimeComputable_pairFstD.comp hArg) hP
  have h2 := hl _ _ ((polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD).comp hArg) hP
  have h3 := hl _ _ ((polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD).comp hArg)
    (hP.append hP)
  have h := polyTimeComputable_and h1 (polyTimeComputable_and h2 h3)
  refine (congrArg PolyTimeComputable (?_ : (fun z =>
    [decide ((pairFstD (NUPPT.inArg z)).length = (NUPPT.inParam z).length ∧
      (pairFstD (pairSndD (NUPPT.inArg z))).length = (NUPPT.inParam z).length ∧
      (pairSndD (pairSndD (NUPPT.inArg z))).length =
        (NUPPT.inParam z).length + (NUPPT.inParam z).length)]) = _)).mpr h
  funext z
  simp only [Function.comp_apply, List.length_append, Bool.decide_and]

/-- The string-level `Dec` is polynomial-time on the layout when `E` is: the guard, the
comparison of the first `n` bits (`polyTimeComputable_pairEq`), and the masked tail.

**Proof sketch.** Compute the pad by applying the polynomial-time evaluator to the key and
nonce. Polynomial-time prefix and suffix operations split both the pad and ciphertext body
after `n` bits. Compare their prefixes, and XOR their suffixes to recover the candidate message.
Use the shape guard and prefix comparison to select this message when both tests pass;
otherwise return a `true` bit followed by the unary parameter, the designated failure word.
Composition and conditional selection preserve polynomial time. -/
theorem polyTimeComputable_spDecFun {E : List Bool → List Bool} (hE : PolyTimeComputable E) :
    PolyTimeComputable (spDecFun E) := by
  have hP := NUPPT.polyTimeComputable_inParam
  have hArg := NUPPT.polyTimeComputable_inArg
  have hk := polyTimeComputable_pairFstD.comp hArg
  have hr := (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD).comp hArg
  have hc := (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD).comp hArg
  have hp := hE.comp (hk.pairEncode hr)
  have hct := (polyTimeComputable_pairTakePoly .var).comp (hP.pairEncode hc)
  have hpt := (polyTimeComputable_pairTakePoly .var).comp (hP.pairEncode hp)
  have hcd := (polyTimeComputable_pairDropPoly .var).comp (hP.pairEncode hc)
  have hpd := (polyTimeComputable_pairDropPoly .var).comp (hP.pairEncode hp)
  have heq := polyTimeComputable_pairEq.comp (hct.pairEncode hpt)
  have hx := polyTimeComputable_pairXor.comp (hcd.pairEncode hpd)
  have hbot := (polyTimeComputable_const [true]).append hP
  have h := polyTimeComputable_ite polyTimeComputable_spDecGuard
    (polyTimeComputable_ite heq hx hbot) hbot
  refine (congrArg PolyTimeComputable (?_ : spDecFun E = _)).mpr h
  funext z
  simp only [spDecFun, spDecStr, Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
    PolyExpr.eval_var, decide_eq_true_eq]
  split_ifs <;> rfl

/-- The activation of the encryption machine on `⟨k, m⟩` with coins `r` is `spEncStr`. -/
theorem runAt_spEnc {E : List Bool → List Bool} (hE : PolyTimeComputable E) (coins : PolyExpr)
    (n : ℕ) (k m : List Bool)
    (r : (NUPPT.ofPolyTimeUniform (polyTimeComputable_spEncFun hE) coins).Coins n) :
    (NUPPT.ofPolyTimeUniform (polyTimeComputable_spEncFun hE) coins).runAt n (pairEncode k m) r =
      spEncStr E k m (List.ofFn r) := by
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
  simp [spEncFun, NUPPT.inArg_eq, NUPPT.inCoins_eq, NUPPT.advInput_eq]

/-- The activation of the decryption machine on `⟨k, c⟩` is `spDecStr` at `ℓ = n`, with `⊥` as
`1^{n+1}`. -/
theorem runAt_spDec {E : List Bool → List Bool} (hE : PolyTimeComputable E) (coins : PolyExpr)
    (n : ℕ) (k c : List Bool)
    (r' : (NUPPT.ofPolyTimeUniform (polyTimeComputable_spDecFun hE) coins).Coins n) :
    (NUPPT.ofPolyTimeUniform (polyTimeComputable_spDecFun hE) coins).runAt n (pairEncode k c) r' =
      (spDecStr E n n k c).getD (true :: List.replicate n true) := by
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
  simp [spDecFun, NUPPT.inArg_eq, NUPPT.inParam_eq, NUPPT.advInput_eq]

/-- The length of a special ciphertext: `2|r| + 2` for `r`, then `|r| + |m|` when the pad has at
least `|r| + |m|` bits. -/
theorem length_spEncStr (E : List Bool → List Bool) {k m r : List Bool}
    (hp : r.length + m.length ≤ (E (pairEncode k r)).length) :
    (spEncStr E k m r).length = 2 * r.length + 2 + (r.length + m.length) := by
  unfold spEncStr
  rw [length_pairEncode, List.length_append, List.length_take, List.length_zipWith,
    List.length_drop]
  omega

end TCSlib.Cryptography.SecureComputation

## ===== TCSlib/Cryptography/SecureComputation/GarblingSpecial.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Garbling
import TCSlib.Cryptography.SecureComputation.SpecialEncryption
import Mathlib.Tactic.Ring

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Garbled circuits from the special encryption scheme (statement phase)

[PS10, §6.2.2–6.2.3]: the garbled rows are encrypted with Algorithm 157.2, "doubly encrypting each
row". This module instantiates the multi-key encryption interface of `Garbling.lean` with nested
special encryption, and proves it correct. Its wrong-key property and the combination with
Claim 159.a are in `GarblingSecurity.lean`.

**Nesting and lengths.** A row with two inputs encrypts the output key (`n` bits) under the
second input's key, then encrypts that ciphertext under the first input's key. The inner
ciphertext `⟨r, c⟩` has `2n + 2 + 2n = 4n + 2` bits (`length_spEncStr`), so the outer layer encrypts
`(4n + 2)`-bit messages, with a pad of `n + (4n + 2)` bits. [PS10] encrypts
`n`-bit messages only and leaves the nesting's lengths implicit; this is a declared deviation. A
single-input row is singly encrypted, and a constant gate's row is in the clear.

## Main definitions

* `SecureComputation.innerLen`: the inner ciphertext length `4n + 2`.
* `SecureComputation.nestedSpecial`: nested special encryption as a `MultiEnc` at parameter `n`.

## Main results

* `SecureComputation.nestedSpecial_decCorrect` (proved): nested special encryption is correct.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2.2–6.2.3 (book pp. 156–160).
-/

namespace TCSlib.Cryptography.SecureComputation

open Complexity Turing TCSlib.Cryptography BoolCircuit

/-- The inner ciphertext length `4n + 2` of a nested row. -/
def innerLen : PolyExpr := .add (.mul (.const 4) .var) (.const 2)

/-- The inner ciphertext length expression is `4n+2`. -/
theorem innerLen_eq : innerLen = .add (.mul (.const 4) .var) (.const 2) := rfl

/-- **Nested special encryption at parameter `n`**: no key, the plaintext; one key,
Algorithm 157.2 with the pad `E₁` (`2n` bits); two keys, Algorithm 157.2 under the second key
with `E₁`, then under the first key with `E₂` (`n + (4n + 2)` bits). Longer key lists are
unused. -/
@[simps (config := { isSimp := false }) enc dec]
def nestedSpecial (E₁ E₂ : List Bool → List Bool) (n : ℕ) :
    MultiEnc (Fin n → Bool) (List Bool) ((Fin n → Bool) × (Fin n → Bool)) where
  enc ks o r := match ks with
    | [] => List.ofFn o
    | [k] => spEncStr E₁ (List.ofFn k) (List.ofFn o) (List.ofFn r.1)
    | [k₁, k₂] => spEncStr E₂ (List.ofFn k₁)
        (spEncStr E₁ (List.ofFn k₂) (List.ofFn o) (List.ofFn r.2)) (List.ofFn r.1)
    | _ => []
  dec ks c := match ks with
    | [] => decodeFin n c
    | [k] => (spDecStr E₁ n n (List.ofFn k) c).bind (decodeFin n)
    | [k₁, k₂] => (spDecStr E₂ n (innerLen.eval n) (List.ofFn k₁) c).bind fun c' =>
        (spDecStr E₁ n n (List.ofFn k₂) c').bind (decodeFin n)
    | _ => none

variable (G₁ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (n + n) → Bool))
  (G₂ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin ((PolyExpr.add .var innerLen).eval n) → Bool))
  (E₁ E₂ : List Bool → List Bool)
  (hGE₁ : ∀ n (s x : Fin n → Bool), E₁ (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (G₁ n s x))
  (hGE₂ : ∀ n (s x : Fin n → Bool), E₂ (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (G₂ n s x))

include hGE₁ hGE₂ in
/-- **Nested special encryption is correct**: decryption under at most two keys inverts
encryption under them (`spDecStr_spEncStr` at each layer, with the inner ciphertext's length
`4n + 2`).

**Proof sketch.** Split by the number of keys. With no key, decoding the encoded plaintext
returns the plaintext. With one key, the evaluator specification gives a pad of length `2n`,
so special-encryption correctness removes the encryption before decoding. With two keys, the
inner ciphertext has length `4n + 2`; the second evaluator provides the pad of length
`n + (4n + 2)` required by the outer layer. Remove the outer layer, then the inner layer, and
decode the original plaintext. Longer key lists are excluded by the correctness contract. -/
theorem nestedSpecial_decCorrect (n : ℕ) : (nestedSpecial E₁ E₂ n).DecCorrect := by
  rw [MultiEnc.decCorrect_iff]
  intro ks hks o r
  have hlen : ∀ v : Fin n → Bool, (List.ofFn v).length = n := fun v => List.length_ofFn
  match ks, hks with
  | [], _ =>
    show decodeFin n (List.ofFn o) = some o
    exact decodeFin_ofFn o
  | [k], _ =>
    show (spDecStr E₁ n n (List.ofFn k)
      (spEncStr E₁ (List.ofFn k) (List.ofFn o) (List.ofFn r.1))).bind (decodeFin n) = some o
    have hp : (E₁ (pairEncode (List.ofFn k) (List.ofFn r.1))).length = n + n := by
      rw [hGE₁ n k r.1, List.length_ofFn]
    rw [spDecStr_spEncStr E₁ (hlen k) (hlen o) (hlen r.1) hp]
    exact decodeFin_ofFn o
  | [k₁, k₂], _ =>
    show (spDecStr E₂ n (innerLen.eval n) (List.ofFn k₁)
      (spEncStr E₂ (List.ofFn k₁) (spEncStr E₁ (List.ofFn k₂) (List.ofFn o) (List.ofFn r.2))
        (List.ofFn r.1))).bind (fun c' =>
          (spDecStr E₁ n n (List.ofFn k₂) c').bind (decodeFin n)) = some o
    have hp₁ : (E₁ (pairEncode (List.ofFn k₂) (List.ofFn r.2))).length = n + n := by
      rw [hGE₁ n k₂ r.2, List.length_ofFn]
    have hc : (spEncStr E₁ (List.ofFn k₂) (List.ofFn o) (List.ofFn r.2)).length =
        innerLen.eval n := by
      rw [length_spEncStr E₁ (by rw [hp₁, hlen, hlen]), hlen, hlen]
      simp only [innerLen, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const,
        PolyExpr.eval_var]
      ring
    have hp₂ : (E₂ (pairEncode (List.ofFn k₁) (List.ofFn r.1))).length =
        n + innerLen.eval n := by
      rw [hGE₂ n k₁ r.1, List.length_ofFn]
      simp only [PolyExpr.eval_add, PolyExpr.eval_var]
    rw [spDecStr_spEncStr E₂ (hlen k₁) hc (hlen r.1) hp₂, Option.bind_some,
      spDecStr_spEncStr E₁ (hlen k₂) (hlen o) (hlen r.2) hp₁]
    exact decodeFin_ofFn o
  | _ :: _ :: _ :: _, h => exact absurd h (by simp)

end TCSlib.Cryptography.SecureComputation

## ===== TCSlib/Cryptography/SecureComputation/Yao.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Hybrid
import TCSlib.Cryptography.SecureComputation.GarblingSecurity
import TCSlib.Complexity.CircuitComplexity.Uniform
import TCSlib.Complexity.ClassP.BinaryArith.Words
import TCSlib.Cryptography.Foundations.BitLists

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Yao's protocol in the OT-hybrid model (statement phase)

[PS10, Protocol 162.6]: Alice garbles a circuit for `f` and sends it with the keys of her input
bits; for each of Bob's input bits the parties run an oblivious transfer in which Bob obtains the
key of his bit; Bob evaluates the garbled circuit, sends the result to Alice, and both output it.
[PS10, Theorem 163.7]: the protocol is honest-but-curious secure. By the ruling of 2026-11-05,
both are stated here in the OT-hybrid model of [Gol04, §7.3] (`HybridProtocol otFunctionality`,
`Hybrid.lean`); the real protocol follows by composition with Protocol 160.4, which is not in
this file.

**The circuits** (`YaoCircuit`). The source garbles "a canonical circuit representation of `f`".
Here that is a uniform family of fan-in-two circuits `C_n` (`DAGCircuit`) of polynomial size, on
`inA(n) + inB(n)` inputs, with a list of `outLen(n)` output vertices. Alice's input bits are
vertices `0, …, inA − 1`, Bob's are vertices `inA, …, inA + inB − 1`. Uniformity (a
polynomial-time map from `1^n` to the description `encodeCircuit`) is what lets Alice, Bob and
the simulators build the circuit in polynomial time. The functionality gives both parties the
values of `C_n(x, y)` at the output vertices (`yaoFunctionality`).

**The garbling** is Construction 158.a of `Garbling.lean` with nested special encryption
(`GarblingSpecial.lean`), keys of `n` bits, and the randomness read from fixed blocks of Alice's
coins (`yaoSeed`): the keys, `2n` coins per row, and a shift `λ_i` per gate.

**The protocol** (`yaoHybrid`). `inB(n) · n` ideal bit-OTs, then two messages:
- call `(i, t)` gives Bob bit `t` of the key of his wire `inA + i` for his bit `y_i`;
- Alice sends the garbled tables, the keys of her input bits, and the key pair `(k⁰, k¹)` of every
  output vertex;
- Bob evaluates the garbled circuit with `runWith` and `evalGate`, decodes each output key by
  comparison with its pair, and sends the bits; under D8 the last mover's message is its output,
  and Alice outputs the message she received.

**Deviations from [PS10].**
- **The OT-hybrid model** (ruling of 2026-11-05), with the ideal calls first (`Hybrid.lean`). The
  source's proof simulates the OT transcripts with Proposition 161.5's simulators; here a party's
  view holds its OT outputs instead, and the composition theorem supplies the rest.
- **Bit OTs.** `otFunctionality` transfers one bit, so the source's OT of a key pair `(k_{i,0},
  k_{i,1})` is `n` bit OTs with the same choice bit `y_i` (the source: "it is straightforward to
  generalize this construction to handle `n`-bit values").
- **The row order: a random XOR shift.** Row `a` of gate `i` sits at the position of `a ⊕ λ_i`
  in a fixed enumeration of the assignments, for a uniform `λ_i` (`xorShift`). The source shuffles
  each table uniformly, but the `24` orders of four rows cannot be sampled exactly from a fixed
  number of coin bits. A uniform shift makes the position of the row that opens uniform and
  independent of the inputs, which is what the simulation uses (the point-and-permute idea of
  [BMR90]).
- **Output decoding.** The source does not say how Bob reads the output from the output keys.
  Here Alice sends each output vertex's key pair, and Bob maps `k⁰ ↦ 0`, `k¹ ↦ 1` (`decodeOut`).
- **Output vertices are sinks** (`YaoCircuit.outs_sink`). The decoding pairs reveal both keys of
  every output vertex, so if a gate read an output vertex `o`, Bob could open its table on both
  values of `o`. For `f(x) = (x₀, x₀ ∧ x₁)` with output vertices `x₀` and `g = x₀ ∧ x₁`, Bob
  holds both keys of `x₀`, opens the row `(1, x₁)` of `g`, and decodes `x₁` even when `x₀ = 0`.
  One identity gate per output brings any circuit to this form.
- **Lengths.** Inputs and outputs have polynomial lengths `inA(n)`, `inB(n)`, `outLen(n)` (the
  source: `x, y ∈ {0,1}^n`); the security parameter `n` is the key length.
- **Correctness** needs, besides a good garbling, distinct keys on each output vertex
  (`yaoHybrid_correct`); both hold except with negligible probability (`yaoSeed_good_whp`).
- **A joint PRF.** The two encryption layers use two PRFs `G₁`, `G₂` (`GarblingSpecial.lean`), and
  a wire's key can key both. The security theorem assumes the pair is pseudorandom under one key
  (`yaoHybrid_simulators`); the source uses one scheme for both layers.

## Main definitions

* `SecureComputation.encodeCircuit`: the description of a circuit with an output list.
* `SecureComputation.YaoCircuit`, `YaoCircuit.output`, `yaoFunctionality`: the circuit family and
  the functionality it computes.
* `SecureComputation.readBits`, `assignIdx`, `xorShift`, `yaoCoins`, `yaoSeed`: the garbling's
  randomness from Alice's coins.
* `SecureComputation.decodeMsgs`: the inverse of `Strategy.encodeMsgs`.
* `SecureComputation.yaoTables`, `yaoKeysA`, `yaoPairs`, `yaoMsg`: Alice's message.
* `SecureComputation.yaoBobTables`, `yaoBobInit`, `yaoBobValues`, `decodeOut`, `yaoBobOut`: Bob's
  evaluation.
* `SecureComputation.yaoAlice`, `yaoBob`, `yaoMain`, `yaoCall`, `yaoHybrid`: Protocol 162.6 in the
  OT-hybrid model.

## Main results

* `SecureComputation.encodeCircuit_injective`, `decodeMsgs_encodeMsgs` (proved): the encodings.
* `SecureComputation.yaoBobOut_yaoMsg` (proved): Bob's evaluation of a good garbling with distinct
  output keys gives `f(x, y)`.
* `SecureComputation.yaoHybrid_answersB_getD` (proved): Bob's OT answers are his keys.
* `SecureComputation.yaoHybrid_correct` (proved): both parties output `f(x, y)` in the hybrid
  execution when the garbling is good with distinct output keys.
* `SecureComputation.yaoSeed_good_whp`, `yaoHybrid_polyTime`, `yaoHybrid_simulators` (stated;
  `sorry`s under sketches): the garbling is good w.h.p., the protocol is efficient, and the
  simulators of Theorem 163.7.
* `SecureComputation.yaoHybrid_hbcSecure` (Theorem 163.7 in the OT-hybrid model, proved from the
  two previous results).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2, Protocol 162.6 and Theorem 163.7 (book pp. 156–164).
* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2*, Cambridge University Press,
  2004, §7.3 (oracle-aided protocols and their composition).
* [BMR90] D. Beaver, S. Micali, P. Rogaway, *The round complexity of secure protocols*, STOC 1990,
  pp. 503–513 (the point-and-permute row order).
* [LP09] Y. Lindell, B. Pinkas, *A proof of security of Yao's protocol for two-party computation*,
  Journal of Cryptology 22(2), 2009, pp. 161–188 (the simulator with one active key per wire).
-/

namespace TCSlib.Cryptography.SecureComputation

open Complexity Turing TCSlib.Cryptography BoolCircuit

/-! ### Circuit descriptions with an output list -/

/-- **The description of a circuit with an output list** [PS10, Protocol 162.6, "a canonical
circuit representation of `f`"]: the pair of the circuit's description `DAGCircuit.encode` (the
number of inputs, the gates and the output vertex, numbers in unary) and the encoded list of the
output vertices in unary, `⟨C, ⟨o₀, ⟨o₁, …⟩⟩⟩`. The gates are encoded by `DAGGate.encode`. -/
def encodeCircuit {m k : ℕ} (C : DAGCircuit m) (outs : Fin k → ℕ) : List Bool :=
  pairEncode C.encode (Strategy.encodeMsgs (List.ofFn fun j => encodeNat (outs j)))

/-- The description of a circuit with an output list is
`⟨encode C, encodeMsgs [encodeNat o₀, …, encodeNat o_{k−1}]⟩`. -/
theorem encodeCircuit_eq {m k : ℕ} (C : DAGCircuit m) (outs : Fin k → ℕ) :
    encodeCircuit C outs =
      pairEncode C.encode (Strategy.encodeMsgs (List.ofFn fun j => encodeNat (outs j))) := rfl

/-- Encoded message lists of equal length are equal only if the lists are. -/
private theorem encodeMsgs_inj : ∀ {l l' : List (List Bool)}, l.length = l'.length →
    Strategy.encodeMsgs l = Strategy.encodeMsgs l' → l = l'
  | [], [], _, _ => rfl
  | a :: l, b :: l', hlen, h => by
    rw [Strategy.encodeMsgs_cons, Strategy.encodeMsgs_cons] at h
    have h₁ := congrArg pairFstD h
    have h₂ := congrArg pairSndD h
    rw [pairFstD_pairEncode, pairFstD_pairEncode] at h₁
    rw [pairSndD_pairEncode, pairSndD_pairEncode] at h₂
    rw [h₁, encodeMsgs_inj (by simpa using hlen) h₂]

/-- The unary code is injective (`decodeNat_encodeNat`). -/
private theorem encodeNat_inj {a b : ℕ} (h : encodeNat a = encodeNat b) : a = b := by
  have ha := decodeNat_encodeNat a []
  have hb := decodeNat_encodeNat b []
  rw [h, hb] at ha
  exact (Prod.mk.inj (Option.some.inj ha)).1.symm

/-- **The description of a circuit with an output list is injective**: equal descriptions come
from equal circuits and equal output lists (`DAGCircuit.encode_injective`, the injectivity of the
pairing and of the unary code). -/
theorem encodeCircuit_injective {m k : ℕ} {C C' : DAGCircuit m} {outs outs' : Fin k → ℕ}
    (h : encodeCircuit C outs = encodeCircuit C' outs') : C = C' ∧ outs = outs' := by
  have h₁ := congrArg pairFstD h
  have h₂ := congrArg pairSndD h
  rw [encodeCircuit_eq, encodeCircuit_eq, pairFstD_pairEncode, pairFstD_pairEncode] at h₁
  rw [encodeCircuit_eq, encodeCircuit_eq, pairSndD_pairEncode, pairSndD_pairEncode] at h₂
  refine ⟨DAGCircuit.encode_injective m h₁, funext fun j => encodeNat_inj ?_⟩
  have h₃ := List.ofFn_injective (encodeMsgs_inj (by simp) h₂)
  exact congrFun h₃ j

/-! ### Uniform circuit families with output lists -/

/-- **A uniform circuit family for Yao's protocol** [PS10, Protocol 162.6, "a canonical circuit
representation of `f`"; §6.2.1, fan-in two]: for each `n`, a fan-in-two circuit `C_n` on
`inA(n) + inB(n)` inputs (Alice's input bits first, then Bob's) with `outLen(n)` output vertices,
none of them read by a gate, of size at most `sizeBound(n)`; and a polynomial-time map sends `1^n`
to the description of `C_n` with its output list. The circuit's own `output` field is not used.

**Deviations.** The output vertices must be sinks (see the module docstring: the decoding pairs
reveal both keys of an output vertex). Uniformity makes the parties efficient; the source fixes a
circuit for `f` without discussing how it is computed. -/
structure YaoCircuit where
  /-- Alice's input length. -/
  inA : PolyExpr
  /-- Bob's input length. -/
  inB : PolyExpr
  /-- The output length. -/
  outLen : PolyExpr
  /-- A polynomial bound on the circuits' sizes. -/
  sizeBound : PolyExpr
  /-- The circuit at parameter `n`: Alice's inputs are vertices `0, …, inA − 1`, Bob's follow. -/
  circ : ∀ n, DAGCircuit (inA.eval n + inB.eval n)
  /-- The output vertices at parameter `n`. -/
  outs : ∀ n, Fin (outLen.eval n) → ℕ
  /-- The output vertices are vertices of the circuit. -/
  outs_lt : ∀ n j, outs n j < (circ n).size
  /-- No gate reads an output vertex. -/
  outs_sink : ∀ n j, ∀ g ∈ (circ n).gates, outs n j ∉ g.args
  /-- The circuits have fan-in two (and are well formed). -/
  fanin : ∀ n, (circ n).IsFaninTwo
  /-- The circuits have polynomial size. -/
  size_le : ∀ n, (circ n).size ≤ sizeBound.eval n
  /-- The family is uniform: a polynomial-time map sends `1^n` to the description of `C_n`. -/
  uniform : ∃ E : List Bool → List Bool, PolyTimeComputable E ∧
    ∀ n, E (List.replicate n true) = encodeCircuit (circ n) (outs n)

namespace YaoCircuit

variable (Y : YaoCircuit)

/-- **The function computed by the family**: on Alice's input `x` and Bob's input `y`, bit `j` is
the value of `C_n(x, y)` at the output vertex `o_j`. -/
def output (n : ℕ) (x : Fin (Y.inA.eval n) → Bool) (y : Fin (Y.inB.eval n) → Bool) :
    Fin (Y.outLen.eval n) → Bool :=
  fun j => ((Y.circ n).values (Fin.append x y)).getD (Y.outs n j) false

/-- Bit `j` of the output is the value of `C_n(x, y)` at the output vertex `o_j`. -/
theorem output_apply (n : ℕ) (x : Fin (Y.inA.eval n) → Bool) (y : Fin (Y.inB.eval n) → Bool)
    (j : Fin (Y.outLen.eval n)) :
    Y.output n x y j = ((Y.circ n).values (Fin.append x y)).getD (Y.outs n j) false := rfl

end YaoCircuit

/-- **The functionality of a Yao circuit family** [PS10, Protocol 162.6, "A and B output the
result `f(x, y)`"]: Alice's input has `inA(n)` bits, Bob's `inB(n)`, and both parties receive the
`outLen(n)` bits `C_n(x, y)` at the output vertices. Its field equations are
`yaoFunctionality_inA`, …, `yaoFunctionality_f`. -/
def yaoFunctionality (Y : YaoCircuit) : Functionality where
  inA := Y.inA
  inB := Y.inB
  outA := Y.outLen
  outB := Y.outLen
  f n x y := (Y.output n x y, Y.output n x y)

attribute [simps (config := { isSimp := false }) inA inB outA outB f] yaoFunctionality

/-! ### The garbling from Alice's coins -/

/-- **`len` bits of a string from position `off`**: bit `t` is the string's bit `off + t`, or
`false` past its end. -/
def readBits (w : List Bool) (off len : ℕ) : Fin len → Bool := fun t => w.getD (off + t) false

/-- Bit `t` of `readBits w off len` is bit `off + t` of `w` (`false` past its end). -/
theorem readBits_apply (w : List Bool) (off len : ℕ) (t : Fin len) :
    readBits w off len t = w.getD (off + t) false := rfl

/-- **The index of an assignment**: the assignment `a` of `len` positions read as a binary number,
position `0` the least significant bit, `Σ_t a_t · 2^t`. It is below `4` for at most two
positions. -/
def assignIdx {len : ℕ} (a : Fin len → Bool) : ℕ :=
  (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0

/-- The index of an assignment is the fold `b₀ + 2 (b₁ + 2 (⋯))` of its bits. -/
theorem assignIdx_eq {len : ℕ} (a : Fin len → Bool) :
    assignIdx a = (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0 := rfl

/-- **The XOR shift by `λ`**: the permutation `a ↦ a ⊕ λ` of the assignments of `len` positions,
an involution. It is the row order of the garbled tables ([BMR90]'s point-and-permute; declared
deviation from [PS10, §6.2.3]'s uniform shuffle, see the module docstring). -/
def xorShift {len : ℕ} (l : Fin len → Bool) : Equiv.Perm (Fin len → Bool) :=
  Function.Involutive.toPerm (fun a p => xor (a p) (l p)) fun a => funext fun p => by
    show xor (xor (a p) (l p)) (l p) = a p
    rw [Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

/-- The XOR shift by `λ` maps `a` to `a ⊕ λ`, position by position. -/
theorem xorShift_apply {len : ℕ} (l a : Fin len → Bool) :
    xorShift l a = fun p => xor (a p) (l p) := rfl

/-- The inverse XOR shift is the same pointwise XOR operation. -/
theorem xorShift_symm_apply {len : ℕ} (l a : Fin len → Bool) :
    (xorShift l).symm a = fun p => xor (a p) (l p) := rfl

/-- **Alice's number of coins**: `10 · S(n) · n + 2 · S(n)` for the size bound `S`; `2 · S(n) · n`
for the keys, `8 · S(n) · n` for the row coins (at most four rows of `2n` coins per gate), and
`2 · S(n)` for the shifts. -/
def yaoCoins (Y : YaoCircuit) : PolyExpr :=
  .add (.mul (.mul (.const 10) Y.sizeBound) .var) (.mul (.const 2) Y.sizeBound)

/-- Alice's coin-count expression is `10 S(n)n + 2 S(n)` syntactically. -/
theorem yaoCoins_eq (Y : YaoCircuit) :
    yaoCoins Y = .add (.mul (.mul (.const 10) Y.sizeBound) .var)
      (.mul (.const 2) Y.sizeBound) := rfl

/-- Alice has `10 · S(n) · n + 2 · S(n)` coins. -/
theorem yaoCoins_eval (Y : YaoCircuit) (n : ℕ) :
    (yaoCoins Y).eval n = 10 * Y.sizeBound.eval n * n + 2 * Y.sizeBound.eval n := rfl

/-- **The garbling's randomness from Alice's coins** [PS10, §6.2.2–6.2.3: random key pairs,
encryption coins, shuffled rows], at key length `n`, with `S = sizeBound(n)`:
- the key of vertex `v` for the bit `b`: the `n` coins from `(b · S + v) · n`;
- the coins of row `a` of gate `i`: the `2n` coins from `2 S n + (4 i + idx(a)) · 2n`, split in
  halves (the outer and inner layer's coins);
- the row order of gate `i`: the XOR shift by the coins from `10 S n + 2 i`.

For a fan-in-two circuit of size at most `S` these blocks are disjoint, so uniform coins give
independent uniform keys and row coins, and uniform shifts.

**Deviation.** The row order is a uniform XOR shift, not a uniform permutation (module docstring).
-/
def yaoSeed (Y : YaoCircuit) (n : ℕ) (r : List Bool) :
    GarbleSeed (Y.circ n) (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)) :=
  (fun v b => readBits r ((b.toNat * Y.sizeBound.eval n + v) * n) n,
    fun i a => (readBits r (2 * Y.sizeBound.eval n * n + (4 * i + assignIdx a) * (2 * n)) n,
      readBits r (2 * Y.sizeBound.eval n * n + (4 * i + assignIdx a) * (2 * n) + n) n),
    fun i => xorShift (readBits r (10 * Y.sizeBound.eval n * n + 2 * i) _))

/-- The key of vertex `v` for the bit `b` is the `n` coins from `(b · S + v) · n`. -/
theorem yaoSeed_fst (Y : YaoCircuit) (n : ℕ) (r : List Bool) (v : Fin (Y.circ n).size)
    (b : Bool) :
    (yaoSeed Y n r).1 v b = readBits r ((b.toNat * Y.sizeBound.eval n + v) * n) n := rfl

/-- The coins of row `a` of gate `i` are the two `n`-bit halves of the `2n` coins from
`2 S n + (4 i + idx(a)) · 2n`. -/
theorem yaoSeed_snd_fst (Y : YaoCircuit) (n : ℕ) (r : List Bool)
    (i : Fin (Y.circ n).gates.length) (a : Fin ((Y.circ n).gates[i]).args.length → Bool) :
    (yaoSeed Y n r).2.1 i a =
      (readBits r (2 * Y.sizeBound.eval n * n + (4 * i + assignIdx a) * (2 * n)) n,
        readBits r (2 * Y.sizeBound.eval n * n + (4 * i + assignIdx a) * (2 * n) + n) n) := rfl

/-- The row order of gate `i` is the XOR shift by the coins from `10 S n + 2 i`. -/
theorem yaoSeed_snd_snd (Y : YaoCircuit) (n : ℕ) (r : List Bool)
    (i : Fin (Y.circ n).gates.length) :
    (yaoSeed Y n r).2.2 i = xorShift (readBits r (10 * Y.sizeBound.eval n * n + 2 * i) _) := rfl

/-- The key of a vertex `v` of the circuit for the bit `b` is the `n` coins from
`(b · S + v) · n`. -/
theorem keyAt_yaoSeed (Y : YaoCircuit) (n : ℕ) (r : List Bool) {v : ℕ}
    (hv : v < (Y.circ n).size) (b : Bool) :
    keyAt (Y.circ n) (yaoSeed Y n r) v b =
      readBits r ((b.toNat * Y.sizeBound.eval n + v) * n) n := by
  rw [keyAt_eq, dif_pos hv, yaoSeed_fst]

/-! ### Message lists -/

/-- **Decoding a message list**, the inverse of `Strategy.encodeMsgs`: the first component of the
string, then the decoding of the second, until the empty string (at most `|w|` components).
Delegates to the public word-list decoder, including on malformed words. -/
def decodeMsgs (w : List Bool) : List (List Bool) := BinArith.decWords w

/-- Decoding any word gives `[]` when the word is empty, and otherwise its first pair
component followed by the decoding of its second component, including on malformed words.

**Proof sketch.** Apply the public empty or nonempty equation of `BinArith.decWords`, according
to whether the input word is empty. -/
theorem decodeMsgs_eq (w : List Bool) :
    decodeMsgs w = if w = [] then [] else pairFstD w :: decodeMsgs (pairSndD w) :=
  if hw : w = [] then
    (congrArg decodeMsgs hw).trans (BinArith.decWords_nil.trans (if_pos hw).symm)
  else
    (BinArith.decWords_of_ne hw).trans (if_neg hw).symm

/-- **Decoding inverts the message-list encoding**: `decodeMsgs (encodeMsgs l) = l`.

**Proof sketch.** The public nil and cons equations identify `Strategy.encodeMsgs` with
`BinArith.encWords` by list recursion. Apply `BinArith.decWords_encWords`. -/
theorem decodeMsgs_encodeMsgs (l : List (List Bool)) :
    decodeMsgs (Strategy.encodeMsgs l) = l := by
  have henc : ∀ ms : List (List Bool), Strategy.encodeMsgs ms = BinArith.encWords ms :=
    List.rec (motive := fun ms : List (List Bool) =>
      Strategy.encodeMsgs ms = BinArith.encWords ms)
      (Strategy.encodeMsgs_nil.trans BinArith.encWords_nil.symm)
      (fun m ms ih => (Strategy.encodeMsgs_cons m ms).trans
        ((congrArg (pairEncode m) ih).trans (BinArith.encWords_cons m ms).symm))
  exact (congrArg BinArith.decWords (henc l)).trans (BinArith.decWords_encWords l)

/-- The empty string decodes to the empty list. -/
theorem decodeMsgs_nil : decodeMsgs [] = [] := BinArith.decWords_nil

/-! ### Alice's message -/

variable (Y : YaoCircuit) (E₁ E₂ : List Bool → List Bool)

/-- **The garbled tables** [PS10, Protocol 162.6, "A generates a garbled circuit … and sends the
circuit"]: gate by gate, the garbled table of `yaoSeed` with nested special encryption, each
table an encoded list of rows, and the tables an encoded list. -/
noncomputable def yaoTables (n : ℕ) (r : List Bool) : List Bool :=
  Strategy.encodeMsgs (List.ofFn fun i : Fin (Y.circ n).gates.length =>
    Strategy.encodeMsgs (garbledTable (nestedSpecial E₁ E₂ n) (Y.circ n) (yaoSeed Y n r) i))

/-- The garbled tables are the encoded list of the encoded garbled tables. -/
theorem yaoTables_eq (n : ℕ) (r : List Bool) :
    yaoTables Y E₁ E₂ n r = Strategy.encodeMsgs (List.ofFn fun i : Fin (Y.circ n).gates.length =>
      Strategy.encodeMsgs (garbledTable (nestedSpecial E₁ E₂ n) (Y.circ n) (yaoSeed Y n r) i)) :=
  rfl

/-- **Alice's input keys** [PS10, Protocol 162.6, "the input keys corresponding to the bits of
`x`"]: the encoded list of the keys `k_v^{x_v}` of her input vertices `v < inA(n)`, for her
input `xs`. -/
def yaoKeysA (n : ℕ) (xs r : List Bool) : List Bool :=
  Strategy.encodeMsgs (List.ofFn fun v : Fin (Y.inA.eval n) =>
    List.ofFn (keyAt (Y.circ n) (yaoSeed Y n r) v (xs.getD v false)))

/-- Alice's input keys are the encoded list of `k_v^{x_v}` for `v < inA(n)`. -/
theorem yaoKeysA_eq (n : ℕ) (xs r : List Bool) :
    yaoKeysA Y n xs r = Strategy.encodeMsgs (List.ofFn fun v : Fin (Y.inA.eval n) =>
      List.ofFn (keyAt (Y.circ n) (yaoSeed Y n r) v (xs.getD v false))) := rfl

/-- **The decoding pairs**: for each output index `j`, the pair `⟨k_{o_j}^0, k_{o_j}^1⟩` of the
keys of the output vertex `o_j`, as an encoded list.

**Deviation.** Not in [PS10], which does not say how Bob reads the output (module docstring). -/
def yaoPairs (n : ℕ) (r : List Bool) : List Bool :=
  Strategy.encodeMsgs (List.ofFn fun j : Fin (Y.outLen.eval n) =>
    pairEncode (List.ofFn (keyAt (Y.circ n) (yaoSeed Y n r) (Y.outs n j) false))
      (List.ofFn (keyAt (Y.circ n) (yaoSeed Y n r) (Y.outs n j) true)))

/-- The decoding pairs are the encoded list of `⟨k_{o_j}^0, k_{o_j}^1⟩`. -/
theorem yaoPairs_eq (n : ℕ) (r : List Bool) :
    yaoPairs Y n r = Strategy.encodeMsgs (List.ofFn fun j : Fin (Y.outLen.eval n) =>
      pairEncode (List.ofFn (keyAt (Y.circ n) (yaoSeed Y n r) (Y.outs n j) false))
        (List.ofFn (keyAt (Y.circ n) (yaoSeed Y n r) (Y.outs n j) true))) := rfl

/-- **Alice's message** [PS10, Protocol 162.6, first step]: `⟨tables, ⟨her input keys, decoding
pairs⟩⟩`, for her input `xs` and her coins `r`. -/
noncomputable def yaoMsg (n : ℕ) (xs r : List Bool) : List Bool :=
  pairEncode (yaoTables Y E₁ E₂ n r) (pairEncode (yaoKeysA Y n xs r) (yaoPairs Y n r))

/-- Alice's message is `⟨tables, ⟨input keys, decoding pairs⟩⟩`. -/
theorem yaoMsg_eq (n : ℕ) (xs r : List Bool) :
    yaoMsg Y E₁ E₂ n xs r =
      pairEncode (yaoTables Y E₁ E₂ n r) (pairEncode (yaoKeysA Y n xs r) (yaoPairs Y n r)) := rfl

/-! ### Bob's evaluation -/

/-- **The tables Bob reads**: at a gate vertex `v ≥ inA + inB`, the decoded list of rows of the
`(v − inA − inB)`-th encoded table of the message; none at an input vertex. -/
def yaoBobTables (n : ℕ) (msg : List Bool) (v : ℕ) : List (List Bool) :=
  if Y.inA.eval n + Y.inB.eval n ≤ v then
    decodeMsgs ((decodeMsgs (pairFstD msg)).getD (v - (Y.inA.eval n + Y.inB.eval n)) [])
  else []

/-- Bob's table at `v` is the decoded `(v − inA − inB)`-th table at a gate vertex, and empty at
an input vertex. -/
theorem yaoBobTables_eq (n : ℕ) (msg : List Bool) (v : ℕ) :
    yaoBobTables Y n msg v = if Y.inA.eval n + Y.inB.eval n ≤ v then
      decodeMsgs ((decodeMsgs (pairFstD msg)).getD (v - (Y.inA.eval n + Y.inB.eval n)) [])
    else [] := rfl

/-- **Bob's input keys** [PS10, Protocol 162.6, "using the keys for all input wires"]: at Alice's
vertex `v < inA(n)`, the `v`-th key of the message; at his vertex `inA(n) + i`, bits `i · n` to
`i · n + n − 1` of his OT answers `ans`. -/
def yaoBobInit (n : ℕ) (msg ans : List Bool) : List (Fin n → Bool) :=
  List.ofFn fun v : Fin (Y.inA.eval n + Y.inB.eval n) =>
    if (v : ℕ) < Y.inA.eval n then padFin n ((decodeMsgs (pairFstD (pairSndD msg))).getD v [])
    else readBits ans (((v : ℕ) - Y.inA.eval n) * n) n

/-- Bob's input keys: Alice's `v`-th key from the message at `v < inA`, his answer bits from
`(v − inA) · n` otherwise. -/
theorem yaoBobInit_eq (n : ℕ) (msg ans : List Bool) :
    yaoBobInit Y n msg ans = List.ofFn fun v : Fin (Y.inA.eval n + Y.inB.eval n) =>
      if (v : ℕ) < Y.inA.eval n then padFin n ((decodeMsgs (pairFstD (pairSndD msg))).getD v [])
      else readBits ans (((v : ℕ) - Y.inA.eval n) * n) n := rfl

/-- **Bob's garbled evaluation** [PS10, Protocol 162.6, "B evaluates the circuit"; §6.2.3, "attempt
to decrypt all four rows"]: `runWith` over the gates of `C_n` from his input keys, each gate opened
by `evalGate` on the table he read at its vertex. -/
def yaoBobValues (n : ℕ) (msg ans : List Bool) : List (Fin n → Bool) :=
  runWith (fun g vs => evalGate (nestedSpecial E₁ E₂ n) (yaoBobTables Y n msg) vs.length g vs)
    (Y.circ n).gates (yaoBobInit Y n msg ans)

/-- Bob's garbled evaluation is `runWith` of `evalGate` on his tables from his input keys. -/
theorem yaoBobValues_eq (n : ℕ) (msg ans : List Bool) :
    yaoBobValues Y E₁ E₂ n msg ans =
      runWith (fun g vs => evalGate (nestedSpecial E₁ E₂ n) (yaoBobTables Y n msg) vs.length g vs)
        (Y.circ n).gates (yaoBobInit Y n msg ans) := rfl

/-- **Decoding an output key** by its pair `p = ⟨k⁰, k¹⟩`: `k⁰ ↦ false`, `k¹ ↦ true`, anything
else `↦ false`.

**Deviation.** Not in [PS10] (module docstring). -/
def decodeOut (k p : List Bool) : Bool :=
  if k = pairFstD p then false else decide (k = pairSndD p)

/-- Decoding an output key: `false` if it is the first key of the pair, otherwise whether it is
the second. -/
theorem decodeOut_eq (k p : List Bool) :
    decodeOut k p = if k = pairFstD p then false else decide (k = pairSndD p) := rfl

/-- The first key of a pair decodes to `false`. -/
theorem decodeOut_fst (k₀ k₁ : List Bool) : decodeOut k₀ (pairEncode k₀ k₁) = false := by
  rw [decodeOut, pairFstD_pairEncode, if_pos rfl]

/-- The second key of a pair of distinct keys decodes to `true`. -/
theorem decodeOut_snd (k₀ k₁ : List Bool) (h : k₁ ≠ k₀) :
    decodeOut k₁ (pairEncode k₀ k₁) = true := by
  rw [decodeOut, pairFstD_pairEncode, pairSndD_pairEncode, if_neg h, decide_eq_true rfl]

/-- **Bob's result** [PS10, Protocol 162.6, last step]: for each output index `j`, the key his
evaluation reaches at the output vertex `o_j`, decoded by the `j`-th pair of the message. -/
def yaoBobOut (n : ℕ) (msg ans : List Bool) : List Bool :=
  List.ofFn fun j : Fin (Y.outLen.eval n) =>
    decodeOut (List.ofFn ((yaoBobValues Y E₁ E₂ n msg ans).getD (Y.outs n j) default))
      ((decodeMsgs (pairSndD (pairSndD msg))).getD j [])

/-- Bob's result: bit `j` decodes the key at `o_j` by the `j`-th decoding pair. -/
theorem yaoBobOut_eq (n : ℕ) (msg ans : List Bool) :
    yaoBobOut Y E₁ E₂ n msg ans = List.ofFn fun j : Fin (Y.outLen.eval n) =>
      decodeOut (List.ofFn ((yaoBobValues Y E₁ E₂ n msg ans).getD (Y.outs n j) default))
        ((decodeMsgs (pairSndD (pairSndD msg))).getD j []) := rfl

/-! ### The protocol -/

/-- **Alice in Protocol 162.6** [PS10] (the prover's role, `Defs.lean`'s convention), on common
input `1^n`, private input `⟨x, answers⟩` (her answers are empty: OT gives the sender `⊥`) and
coins `r`: on the empty history, her message `yaoMsg`; on a nonempty history, its first message,
which is her output ("A and B output the result"). Her coins are `yaoCoins`. -/
noncomputable def yaoAlice : Strategy where
  next x z r hist := match hist with
    | [] => yaoMsg Y E₁ E₂ x.length (pairFstD z) r
    | m :: _ => m
  coins := yaoCoins Y

/-- On the empty history Alice sends `yaoMsg` at `|x|` for her input `pairFstD z`. -/
theorem yaoAlice_next_nil (x z r : List Bool) :
    (yaoAlice Y E₁ E₂).next x z r [] = yaoMsg Y E₁ E₂ x.length (pairFstD z) r := rfl

/-- On a nonempty history Alice returns its first message. -/
theorem yaoAlice_next_cons (x z r m : List Bool) (hist : List (List Bool)) :
    (yaoAlice Y E₁ E₂).next x z r (m :: hist) = m := rfl

/-- Alice's coin polynomial is `yaoCoins`. -/
theorem yaoAlice_coins : (yaoAlice Y E₁ E₂).coins = yaoCoins Y := rfl

/-- **Bob in Protocol 162.6** [PS10] (the verifier's role), on common input `1^n` and private
input `⟨y, answers⟩`: his result `yaoBobOut` on the first message received and his answers. He
moves last, so his message is also his output. He uses no coins. -/
def yaoBob : Strategy where
  next x z _ hist := yaoBobOut Y E₁ E₂ x.length (hist.headD []) (pairSndD z)
  coins := .const 0

/-- Bob's message is `yaoBobOut` at `|x|` on the first message received and his answers. -/
theorem yaoBob_next (x z r : List Bool) (hist : List (List Bool)) :
    (yaoBob Y E₁ E₂).next x z r hist =
      yaoBobOut Y E₁ E₂ x.length (hist.headD []) (pairSndD z) := rfl

/-- Bob uses no coins. -/
theorem yaoBob_coins : (yaoBob Y E₁ E₂).coins = .const 0 := rfl

/-- **The message phase of Protocol 162.6** [PS10]: two messages, Alice first; Alice sends the
garbled circuit and her keys, Bob returns `f(x, y)`. Its fields are `yaoMain_P`, …,
`yaoMain_verifierFirst`. -/
noncomputable def yaoMain : Protocol where
  P := yaoAlice Y E₁ E₂
  V := yaoBob Y E₁ E₂
  rounds := .const 2
  verifierFirst := false

attribute [simps (config := { isSimp := false }) P V rounds verifierFirst] yaoMain

/-- **Bob's output in the message phase**: Bob's result on Alice's message and his answers. -/
theorem yaoMain_outV (w zA zB : List Bool)
    (r : (yaoMain Y E₁ E₂).ExecCoins (yaoMain Y E₁ E₂).P w) :
    (yaoMain Y E₁ E₂).outV (yaoMain Y E₁ E₂).P w zA zB r =
      yaoBobOut Y E₁ E₂ w.length (yaoMsg Y E₁ E₂ w.length (pairFstD zA) (List.ofFn r.1))
        (pairSndD zB) := by
  simp [Protocol.outV_eq, Protocol.transcriptWith_eq, yaoMain_P, yaoMain_V,
    yaoMain_rounds, yaoMain_verifierFirst, PolyExpr.eval_const, exec_succ, exec_zero,
    moverIsV_false, yaoAlice_next_nil, yaoBob_next]

/-- **Alice's output in the message phase**: the message Bob sent, his result. -/
theorem yaoMain_outP (w zA zB : List Bool)
    (r : (yaoMain Y E₁ E₂).ExecCoins (yaoMain Y E₁ E₂).P w) :
    (yaoMain Y E₁ E₂).outP w zA zB r =
      yaoBobOut Y E₁ E₂ w.length (yaoMsg Y E₁ E₂ w.length (pairFstD zA) (List.ofFn r.1))
        (pairSndD zB) := by
  simp [Protocol.outP_eq, Protocol.transcriptWith_eq, yaoMain_P, yaoMain_V,
    yaoMain_rounds, yaoMain_verifierFirst, PolyExpr.eval_const, exec_succ, exec_zero,
    moverIsV_false, yaoAlice_next_nil, yaoAlice_next_cons, yaoBob_next]

/-- **The OT call index**: call `j < inB(n) · n` transfers bit `t` of the keys of Bob's wire
`inA + i`, for `(i, t) = finProdFinEquiv⁻¹ j`, that is `j = i · n + t`. -/
def yaoCall (n : ℕ) (j : Fin (Y.inB.eval n * n)) : Fin (Y.inB.eval n) × Fin n :=
  finProdFinEquiv.symm j

/-- The OT call index is `finProdFinEquiv⁻¹`. -/
theorem yaoCall_eq (n : ℕ) (j : Fin (Y.inB.eval n * n)) :
    yaoCall Y n j = finProdFinEquiv.symm j := rfl

/-- Call `finProdFinEquiv (i, t)` (that is `i · n + t`) has index `(i, t)`. -/
theorem yaoCall_finProdFinEquiv (n : ℕ) (i : Fin (Y.inB.eval n)) (t : Fin n) :
    yaoCall Y n (finProdFinEquiv (i, t)) = (i, t) := by
  rw [yaoCall, Equiv.symm_apply_apply]

/-- **Protocol 162.6 in the OT-hybrid model** [PS10, Protocol 162.6; Gol04, §7.3]: `inB(n) · n`
ideal bit OTs, then `yaoMain`. In call `(i, t)` Alice's input is bit `t` of the two keys of
Bob's wire `inA + i` (from her coins, through `yaoSeed`), Bob's is his bit `y_i`. Its fields are
`yaoHybrid_main`, `yaoHybrid_calls`, `yaoHybrid_callA`, `yaoHybrid_callB`.

**Deviation.** The source's OT of a key pair is `n` bit OTs with the same choice bit (module
docstring). -/
noncomputable def yaoHybrid : HybridProtocol otFunctionality where
  main := yaoMain Y E₁ E₂
  calls := .mul Y.inB .var
  callA n _ r j c := keyAt (Y.circ n) (yaoSeed Y n r) (Y.inA.eval n + (yaoCall Y n j).1)
    (decide ((c : ℕ) = 1)) (yaoCall Y n j).2
  callB n y _ j _ := y.getD (yaoCall Y n j).1 false

attribute [simps (config := { isSimp := false }) main calls] yaoHybrid

/-- Alice's input to call `j = (i, t)` is `c ↦ k_{inA + i}^{c = 1}[t]`. -/
theorem yaoHybrid_callA (n : ℕ) (xs r : List Bool) (j : Fin (Y.inB.eval n * n)) (c : Fin 2) :
    (yaoHybrid Y E₁ E₂).callA n xs r j
        (Fin.cast ((congrArg (fun p : PolyExpr => p.eval n) otFunctionality_inA).trans
          (PolyExpr.eval_const 2 n)).symm c) =
      keyAt (Y.circ n) (yaoSeed Y n r) (Y.inA.eval n + (yaoCall Y n j).1) (decide ((c : ℕ) = 1))
        (yaoCall Y n j).2 := rfl

/-- Bob's input to call `j = (i, t)` is his bit `y_i`. -/
theorem yaoHybrid_callB (n : ℕ) (ys r : List Bool) (j : Fin (Y.inB.eval n * n)) (c : Fin 1) :
    (yaoHybrid Y E₁ E₂).callB n ys r j
        (Fin.cast ((congrArg (fun p : PolyExpr => p.eval n) otFunctionality_inB).trans
          (PolyExpr.eval_const 1 n)).symm c) = ys.getD (yaoCall Y n j).1 false := rfl

/-! ### Correctness -/

/-- Reading a list of a function at an index of the function's domain. -/
private theorem getD_ofFn' {α : Type} {k : ℕ} (f : Fin k → α) (i : Fin k) (d : α) :
    (List.ofFn f).getD i d = f i := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

/-- **Bob reads the garbled tables**: on Alice's message, the tables Bob reads are the garbled
tables `tableAt` of her garbling, at every vertex. -/
theorem yaoBobTables_yaoMsg (n : ℕ) (xs r : List Bool) :
    yaoBobTables Y n (yaoMsg Y E₁ E₂ n xs r) =
      tableAt (nestedSpecial E₁ E₂ n) (Y.circ n) (yaoSeed Y n r) := by
  funext v
  rw [tableAt_eq, yaoBobTables_eq, yaoMsg_eq, yaoTables_eq, pairFstD_pairEncode,
    decodeMsgs_encodeMsgs]
  by_cases h1 : Y.inA.eval n + Y.inB.eval n ≤ v
  · rw [if_pos h1]
    by_cases h2 : v - (Y.inA.eval n + Y.inB.eval n) < (Y.circ n).gates.length
    · rw [dif_pos ⟨h1, h2⟩, List.getD_eq_getElem _ _ (by simpa using h2), List.getElem_ofFn,
        decodeMsgs_encodeMsgs]
    · rw [dif_neg (fun h => h2 h.2), List.getD_eq_default _ _ (by simp; omega), decodeMsgs_nil]
  · rw [if_neg h1, dif_neg (fun h => h1 h.1)]

/-- **Bob's input keys are the input keys of `(x, y)`**: on Alice's message for `x`, and answers
that hold, at bits `i · n + t`, the bits of the keys `k_{inA + i}^{y_i}`, Bob's input keys are
`inputKeys` of `x ‖ y`.

**Proof sketch.** Vertex by vertex. At Alice's vertex `v < inA`, the second component of the
message decodes to her keys (`decodeMsgs_encodeMsgs`), and its `v`-th entry is `k_v^{x_v}`
(`padFin_ofFn`), with `x_v = (x ‖ y)_v` (`Fin.append_left`). At Bob's vertex `inA + i`, the
answer bits `i · n + t` are the bits of `k_{inA + i}^{y_i}` by hypothesis, with
`y_i = (x ‖ y)_{inA + i}` (`Fin.append_right`). -/
theorem yaoBobInit_yaoMsg (n : ℕ) (x : Fin (Y.inA.eval n) → Bool) (y : Fin (Y.inB.eval n) → Bool)
    (r ans : List Bool)
    (hans : ∀ (i : Fin (Y.inB.eval n)) (t : Fin n), ans.getD (i * n + t) false =
      keyAt (Y.circ n) (yaoSeed Y n r) (Y.inA.eval n + i) (y i) t) :
    yaoBobInit Y n (yaoMsg Y E₁ E₂ n (List.ofFn x) r) ans =
      inputKeys (Y.circ n) (yaoSeed Y n r) (Fin.append x y) := by
  rw [inputKeys_eq, yaoBobInit_eq]
  congr 1
  funext v
  rw [yaoMsg_eq, pairSndD_pairEncode, pairFstD_pairEncode, yaoKeysA_eq, decodeMsgs_encodeMsgs]
  by_cases hv : (v : ℕ) < Y.inA.eval n
  · rw [if_pos hv, getD_ofFn' _ ⟨v, hv⟩, padFin_ofFn, getD_ofFn' x ⟨v, hv⟩]
    have hx := Fin.append_left x y ⟨v, hv⟩
    rw [show Fin.castAdd (Y.inB.eval n) ⟨(v : ℕ), hv⟩ = v from Fin.ext rfl] at hx
    rw [hx]
  · rw [if_neg hv]
    have hi : (v : ℕ) - Y.inA.eval n < Y.inB.eval n := by omega
    have hy := Fin.append_right x y ⟨v - Y.inA.eval n, hi⟩
    rw [show Fin.natAdd (Y.inA.eval n) ⟨(v : ℕ) - Y.inA.eval n, hi⟩ = v from
      Fin.ext (by simp; omega)] at hy
    rw [hy]
    funext t
    have hv' : Y.inA.eval n + ((v : ℕ) - Y.inA.eval n) = v := by omega
    rw [readBits_apply, hans ⟨v - Y.inA.eval n, hi⟩ t, Fin.val_mk, hv']

/-- **Bob's evaluation is the garbled evaluation**: on Alice's message and answers holding the
keys of Bob's bits, Bob's values are `garbledValues` of her garbling from the input keys of
`x ‖ y`. -/
theorem yaoBobValues_yaoMsg (n : ℕ) (x : Fin (Y.inA.eval n) → Bool)
    (y : Fin (Y.inB.eval n) → Bool) (r ans : List Bool)
    (hans : ∀ (i : Fin (Y.inB.eval n)) (t : Fin n), ans.getD (i * n + t) false =
      keyAt (Y.circ n) (yaoSeed Y n r) (Y.inA.eval n + i) (y i) t) :
    yaoBobValues Y E₁ E₂ n (yaoMsg Y E₁ E₂ n (List.ofFn x) r) ans =
      garbledValues (nestedSpecial E₁ E₂ n) (Y.circ n) (yaoSeed Y n r)
        (inputKeys (Y.circ n) (yaoSeed Y n r) (Fin.append x y)) := by
  rw [yaoBobValues_eq, yaoBobTables_yaoMsg, yaoBobInit_yaoMsg Y E₁ E₂ n x y r ans hans,
    garbledValues_eq]

/-- **Bob computes `f(x, y)`** [PS10, Protocol 162.6, "B evaluates the circuit to compute the
output `f(x, y)`"; Claim 159.a]: on Alice's message for `x`, with answers holding the keys of
Bob's bits `y`, if the garbling is good and every output vertex has two distinct keys, Bob's
result is `C_n(x, y)` at the output vertices.

**Proof sketch.** Bob's tables are the garbled tables and his input keys those of `x ‖ y`
(`yaoBobTables_yaoMsg`, `yaoBobInit_yaoMsg`), so his evaluation is `garbledValues`
(`yaoBobValues_yaoMsg`). By `garbledValues_getD` it reaches the key `k_o^{v_o}` of each output
vertex `o`'s value. The `j`-th decoding pair is `⟨k_o^0, k_o^1⟩`, and with distinct keys
`decodeOut` returns `v_o` (`decodeOut_fst`, `decodeOut_snd`). -/
theorem yaoBobOut_yaoMsg (n : ℕ) (x : Fin (Y.inA.eval n) → Bool)
    (y : Fin (Y.inB.eval n) → Bool) (r ans : List Bool)
    (hans : ∀ (i : Fin (Y.inB.eval n)) (t : Fin n), ans.getD (i * n + t) false =
      keyAt (Y.circ n) (yaoSeed Y n r) (Y.inA.eval n + i) (y i) t)
    (hgood : Good (nestedSpecial E₁ E₂ n) (Y.circ n) (yaoSeed Y n r))
    (hdist : ∀ j, keyAt (Y.circ n) (yaoSeed Y n r) (Y.outs n j) false ≠
      keyAt (Y.circ n) (yaoSeed Y n r) (Y.outs n j) true) :
    yaoBobOut Y E₁ E₂ n (yaoMsg Y E₁ E₂ n (List.ofFn x) r) ans = List.ofFn (Y.output n x y) := by
  rw [yaoBobOut_eq, yaoBobValues_yaoMsg Y E₁ E₂ n x y r ans hans]
  congr 1
  funext j
  rw [garbledValues_getD _ _ _ hgood _ _ (Y.outs_lt n j), yaoMsg_eq, pairSndD_pairEncode,
    pairSndD_pairEncode, yaoPairs_eq, decodeMsgs_encodeMsgs, getD_ofFn', YaoCircuit.output_apply]
  cases ((Y.circ n).values (Fin.append x y)).getD (Y.outs n j) false
  · exact decodeOut_fst _ _
  · exact decodeOut_snd _ _ fun h => hdist j (List.ofFn_injective h).symm

/-- **Bob's OT answers are the keys of his bits**: in the hybrid execution, bit `i · n + t` of
Bob's answers is bit `t` of the key `k_{inA + i}^{y_i}` of his wire `inA + i` for his bit `y_i`
(`otFunctionality_f_snd`). -/
theorem yaoHybrid_answersB_getD (n : ℕ) (xs ys rA rB : List Bool) (i : Fin (Y.inB.eval n))
    (t : Fin n) :
    ((yaoHybrid Y E₁ E₂).answersB n xs ys rA rB).getD (i * n + t) false =
      keyAt (Y.circ n) (yaoSeed Y n rA) (Y.inA.eval n + i) (ys.getD i false) t := by
  have h := flatten_ofFn_one (k := Y.inB.eval n * n) (l := otFunctionality.outB.eval n)
    ((congrArg (fun p : PolyExpr => p.eval n) otFunctionality_outB).trans
      (PolyExpr.eval_const 1 n))
    fun j => (otFunctionality.f n ((yaoHybrid Y E₁ E₂).callA n xs rA j)
      ((yaoHybrid Y E₁ E₂).callB n ys rB j)).2
  have hj : i * n + t = (finProdFinEquiv (i, t) : ℕ) := by
    rw [finProdFinEquiv_apply_val]; ring
  rw [HybridProtocol.answersB_eq]
  -- Normalize the owner-local hybrid call count in the list binder before using `h`.
  change (List.ofFn (fun j : Fin (Y.inB.eval n * n) =>
    List.ofFn ((otFunctionality.f n ((yaoHybrid Y E₁ E₂).callA n xs rA j)
      ((yaoHybrid Y E₁ E₂).callB n ys rB j)).2))).flatten.getD (i * n + t) false = _
  rw [h, hj, getD_ofFn', otFunctionality_f_snd_apply,
    yaoHybrid_callA, yaoHybrid_callB, yaoCall_finProdFinEquiv]
  cases ys.getD i false <;> rfl

/-- `yaoBobOut_yaoMsg` at a parameter `L` equal to `n` (for the common input `1^n`, whose length
is `n` only propositionally). -/
private theorem yaoBobOut_yaoMsg_of_eq {L n : ℕ} (hL : L = n) (x : Fin (Y.inA.eval n) → Bool)
    (y : Fin (Y.inB.eval n) → Bool) (r ans : List Bool)
    (hans : ∀ (i : Fin (Y.inB.eval n)) (t : Fin n), ans.getD (i * n + t) false =
      keyAt (Y.circ n) (yaoSeed Y n r) (Y.inA.eval n + i) (y i) t)
    (hgood : Good (nestedSpecial E₁ E₂ n) (Y.circ n) (yaoSeed Y n r))
    (hdist : ∀ j, keyAt (Y.circ n) (yaoSeed Y n r) (Y.outs n j) false ≠
      keyAt (Y.circ n) (yaoSeed Y n r) (Y.outs n j) true) :
    yaoBobOut Y E₁ E₂ L (yaoMsg Y E₁ E₂ L (List.ofFn x) r) ans = List.ofFn (Y.output n x y) := by
  subst hL
  exact yaoBobOut_yaoMsg Y E₁ E₂ L x y r ans hans hgood hdist

/-- **Correctness of Protocol 162.6 in the OT-hybrid model** [PS10, Protocol 162.6, "A and B
output the result `f(x, y)`"; the output clause of Theorem 163.7]: in the hybrid execution with
common input `1^n`, inputs `x`, `y` and coins `r`, if Alice's garbling is good and every output
vertex has two distinct keys, Bob's output and Alice's output are both `f(x, y)`.

**Deviation.** The source needs no hypothesis on the output keys, since it does not say how Bob
decodes them. Equal keys on an output vertex (probability `2^{-n}` each) make the decoding
ambiguous; `yaoSeed_good_whp` bounds both failure events.

**Proof sketch.** Bob's answers hold the keys of his bits (`yaoHybrid_answersB_getD`), and his
private input decodes to them (`HybridProtocol.pairSndD_privB`), Alice's to `x`. The message
phase gives Bob the output `yaoBobOut` on Alice's message (`yaoMain_outV`), which is `f(x, y)`
(`yaoBobOut_yaoMsg`, transported along `|1^n| = n`), and Alice outputs what Bob sent
(`yaoMain_outP`). -/
theorem yaoHybrid_correct (n : ℕ) (x : Fin ((yaoFunctionality Y).inA.eval n) → Bool)
    (y : Fin ((yaoFunctionality Y).inB.eval n) → Bool) (r : (yaoHybrid Y E₁ E₂).Coins n)
    (hgood : Good (nestedSpecial E₁ E₂ n) (Y.circ n) (yaoSeed Y n (List.ofFn r.1)))
    (hdist : ∀ j, keyAt (Y.circ n) (yaoSeed Y n (List.ofFn r.1)) (Y.outs n j) false ≠
      keyAt (Y.circ n) (yaoSeed Y n (List.ofFn r.1)) (Y.outs n j) true) :
    (yaoHybrid Y E₁ E₂).main.outV (yaoHybrid Y E₁ E₂).main.P (List.replicate n true)
        ((yaoHybrid Y E₁ E₂).privA n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
        ((yaoHybrid Y E₁ E₂).privB n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
        r = List.ofFn ((yaoFunctionality Y).f n x y).2 ∧
      (yaoHybrid Y E₁ E₂).main.outP (List.replicate n true)
        ((yaoHybrid Y E₁ E₂).privA n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
        ((yaoHybrid Y E₁ E₂).privB n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
        r = List.ofFn ((yaoFunctionality Y).f n x y).1 := by
  have key := yaoBobOut_yaoMsg_of_eq Y E₁ E₂ (List.length_replicate (n := n) (a := true)) x y
    (List.ofFn r.1)
    ((yaoHybrid Y E₁ E₂).answersB n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
    (fun i t => by rw [yaoHybrid_answersB_getD, getD_ofFn']) hgood hdist
  refine ⟨?_, ?_⟩
  · show (yaoMain Y E₁ E₂).outV (yaoMain Y E₁ E₂).P (List.replicate n true) _ _ r = _
    rw [yaoMain_outV, HybridProtocol.pairFstD_privA, HybridProtocol.pairSndD_privB]
    exact key
  · show (yaoMain Y E₁ E₂).outP (List.replicate n true) _ _ r = _
    rw [yaoMain_outP, HybridProtocol.pairFstD_privA, HybridProtocol.pairSndD_privB]
    exact key

/-! ### Theorem 163.7 in the OT-hybrid model -/

section Security

variable (G₁ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (n + n) → Bool))
  (G₂ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin ((PolyExpr.add .var innerLen).eval n) → Bool))
  (hGE₁ : ∀ n (s x : Fin n → Bool), E₁ (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (G₁ n s x))
  (hGE₂ : ∀ n (s x : Fin n → Bool), E₂ (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (G₂ n s x))

include hGE₁ hGE₂ in
/-- **Alice's garbling is good, with distinct output keys, with high probability** [PS10, §6.2.3,
"all but one row will evaluate to `⊥`" (Claim 159.a)]: with nested special encryption from two
PRFs `G₁`, `G₂` evaluated by `E₁`, `E₂`, there is a negligible `δ` such that for every `n`, on
uniform coins for Alice, the garbling `yaoSeed` fails to be good, or gives some output vertex two
equal keys, with probability at most `δ(n)`.

**Proof sketch.** Write `S = sizeBound(n)`.
1. *The coin blocks are disjoint.* Vertices are below `size(C_n) ≤ S`, gates below `S`, and a
   fan-in-two gate has at most four assignments, with indices below `4` (`assignIdx`). So the
   keys, the row coins and the shifts of `yaoSeed` read disjoint blocks of Alice's coins: the keys
   and row coins are independent and uniform, and independent of the shifts.
2. *Goodness.* The argument of `uprob_not_good_le` applies to this distribution. At gate `i` and
   assignment `a`, the row of `a` decrypts under `a`'s keys to the right key
   (`nestedSpecial_decCorrect`), so `Good` fails there only if the row of some `a'' ≠ a`
   decrypts under `a`'s keys. The arguments are distinct vertices below the gate's own, so that
   row's keys, plaintext and coins are independent and uniform. By `nestedSpecial_wrongKeyBot`
   the event has probability at most `δ₀(n)`, whatever the row order. At most `12` such events
   per gate and `S` gates give `12 · S · δ₀(n)`.
3. *Distinct output keys.* The two keys of an output vertex are independent uniform `n`-bit
   strings, equal with probability `2^{-n}`: at most `outLen(n) · 2^{-n}` in all.
4. `δ(n) = 12 · S(n) · δ₀(n) + outLen(n) · 2^{-n}` is negligible (a polynomial times a negligible
   function, `Negligible.add`). -/
theorem yaoSeed_good_whp (hG₁ : PRFOut (.add .var .var) G₁)
    (hG₂ : PRFOut (.add .var innerLen) G₂) :
    ∃ δ : ℕ → ℝ, Negligible δ ∧ ∀ n, uprob (fun r : Fin ((yaoCoins Y).eval n) → Bool =>
      ¬ (Good (nestedSpecial E₁ E₂ n) (Y.circ n) (yaoSeed Y n (List.ofFn r)) ∧
        ∀ j, keyAt (Y.circ n) (yaoSeed Y n (List.ofFn r)) (Y.outs n j) false ≠
          keyAt (Y.circ n) (yaoSeed Y n (List.ofFn r)) (Y.outs n j) true)) ≤ δ n := by
  sorry

/-- **Protocol 162.6 in the OT-hybrid model runs in polynomial time** (the efficiency clause of
[PS10, Definition 155.1], `HybridProtocol.PolyTime`, ruling of 2026-11-05) when `E₁` and `E₂`
are polynomial-time.

**Proof sketch.** Write `S = sizeBound(n)`.
1. *Alice* (`Strategy.Efficient`). On the empty history: compute the description of `C_n` from
   `1^n` by the uniformity map and decode it; read keys, row coins and shifts from her coins;
   encrypt at most four rows per gate with `E₁` and `E₂`; pair the tables, her input keys and the
   decoding pairs. The enumeration `Finset.univ.toList` of the assignments of at most two
   positions is a constant table. On a nonempty history: copy the first message. A uniform
   machine with coin polynomial `yaoCoins` computes this.
2. *Bob.* Decode the three lists (`decodeMsgs`), recompute `C_n`, and run `runWith` with
   `evalGate`: each decryption checks lengths before calling `E₁` or `E₂` (`spDecStr`), and each
   output key is compared with its pair. This is polynomial in `n` and the message length.
3. *The calls.* Alice's input to call `(i, t)` is two coins at positions computed from `n`,
   `inA(n)` and `S` (`keyAt_yaoSeed`); Bob's is one bit of his input.
4. *The messages.* Whatever `E₁`, `E₂` return, a row has at most `7n + 4` bits (`take` and
   `zipWith` cap the pads), so Alice's message has `O((S + inA(n) + outLen(n)) · n)` bits after
   the pairings; Bob's has `outLen(n)` bits. Neither depends on the answers. -/
theorem yaoHybrid_polyTime (hE₁ : PolyTimeComputable E₁) (hE₂ : PolyTimeComputable E₂) :
    (yaoHybrid Y E₁ E₂).PolyTime (yaoFunctionality Y) := by
  sorry

include hGE₁ hGE₂ in
/-- **The simulators of Theorem 163.7, in the OT-hybrid model** [PS10, Theorem 163.7]: with
nested special encryption from two PRFs `G₁`, `G₂` with polynomial-time evaluators `E₁`, `E₂`,
which are also jointly pseudorandom under one key, there are non-uniform PPT simulators `S_A`,
`S_B` such that for every non-uniform PPT distinguisher there is a negligible `ε` bounding, for
all `n`, `x`, `y`, its advantage between the hybrid real and ideal samplers on both sides.

**Deviation: the joint PRF hypothesis `hG₁₂`** (the pair `k ↦ (G₁(k, ·), G₂(k, ·))` is one PRF;
it implies `hG₁` and `hG₂`). [PS10] doubly encrypts with one scheme. Here the two layers use two
PRFs (`nestedSpecial`), and a wire's key keys `G₂` where the wire is a first argument and `G₁`
where it is a second or only one. The hybrid of step 3 then needs encryptions of both schemes
under one unknown key. A reduction to the security of `G₁` alone cannot produce the `G₂`-pads
under that key, nor conversely; the two separate PRF assumptions do not give their security
under a shared key in general.

**Proof sketch.** Write `f = f(x, y)`. Alice's view in the hybrid execution is
`⟨1^n, ⟨x, []⟩, r_A, [m_B]⟩` (her OT answers are empty), Bob's is `⟨1^n, ⟨y, ans⟩, [], [m_A]⟩`
with `ans` the bits of the keys `k_{inA + i}^{y_i}` (`yaoHybrid_answersB_getD`). Let `Bad` be the
event that the garbling is not good or some output vertex has two equal keys; by
`yaoSeed_good_whp` it has probability at most `δ(n)`, and off `Bad` both outputs are `f`
(`yaoHybrid_correct`).
1. *`S_A(1^n, ⟨x, f⟩)`*, with `yaoCoins(n)` coins `r`: the view `⟨1^n, ⟨x, []⟩, r, [f]⟩`. The
   source's `S_A` also simulates the OT transcripts with Proposition 161.5's simulator; in the
   hybrid model there are none. Off `Bad`, `m_B = f` and Bob outputs `f`, so the real and ideal
   samplers agree outside an event of probability at most `δ(n)`; every distinguisher has
   advantage at most `δ(n)`, for all inputs.
2. *`S_B(1^n, ⟨y, f⟩)`*, with `yaoCoins(n)` coins: read a seed `s = yaoSeed` and let the active
   key of every wire be `k_w = k_w^0`. The fake garbled circuit has the real enumeration and
   shifts, but every row of gate `i` encrypts the active key `k_{inA + inB + i}` under that row's
   argument keys. Alice's input keys are the active keys, and so are Bob's answers. The pair of
   output `j` is `⟨k_o^0, k_o^1⟩` if `f_j = 0` and `⟨k_o^1, k_o^0⟩` otherwise, so the active key
   decodes to `f_j`. This is the source's "garbled circuit that always outputs `f(x, y)`", in the
   one-active-key form of [LP09]. `S_B` outputs `⟨1^n, ⟨y, ans'⟩, [], [m'_A]⟩`.
3. *Bob's side, the hybrid over gates* [PS10, "using a hybrid argument …"].
   - `H₀` is the real sampler.
   - In `H₁`, wire `w` with value `v_w` on `(x, y)` has active key `a_w = k_w^{v_w}` and inactive
     key `ι_w = k_w^{1−v_w}`, and gate `i` the shift `λ_i ⊕ v_{args}`. This is a bijection of
     Alice's coins, so `H₁ = H₀`. In these terms the opened row of every gate is the row of the
     all-active assignment; its position is uniform, given by the shift. Bob holds only active
     keys, and the active key of output `j` decodes to `f_j`.
   - `H₂,ᵢ` makes the rows of the gates below `i` encrypt the active output key. Then
     `H₂,₀ = H₁`, and `H₂,|gates|` is `S_B`'s output up to renaming the keys.
   - `H₂,ᵢ ≈ H₂,ᵢ₊₁`: the rows that change are encrypted under an inactive key `ι_u` of an
     argument `u` of gate `i`: in the outer layer if `u` is the first argument, else in the inner
     one. In `H₂,ᵢ`, `ι_u` is only an encryption key, of rows of the gates that read `u`:
     - it is no plaintext: if `u` is a gate, it precedes gate `i` and its table is already fake;
     - it is in no decoding pair: no gate reads an output vertex (`YaoCircuit.outs_sink`);
     - it is not among Alice's keys or Bob's answers, which are active.

     A distinguisher between the two gives one against the multi-message security of
     Algorithm 157.2 under `ι_u`: the reduction samples everything else and obtains the rows
     under `ι_u` from its challenge, with plaintexts `ι_{inA + inB + i}` versus
     `a_{inA + inB + i}` for the changed rows. For the inner layer this is Claim 157.a (i)
     (`specialScheme_multiMessageSecure`, `n`-bit messages with `G₁`). For the outer layer it is
     the same claim for `(4n + 2)`-bit messages with `G₂`. Since `ι_u` may key both layers, the
     reduction needs the two schemes' ciphertexts under one key: the same proof, with the
     joint PRF `hG₁₂` replaced by a random function (not yet stated in the library).
   - The reductions are non-uniform: their advice at `n` is the worst inputs `(x, y)` and the
     hybrid index. This makes the bound `2 · S(n) · ε_MM(n)` uniform over the inputs.
   - Bob's real output pair adds `Bad`: the total is `δ(n) + 2 · S(n) · ε_MM(n)`, negligible.
4. *Efficiency of the simulators.* `S_A` copies its input and coins. `S_B` builds `C_n` with the
   uniformity map and encrypts with `E₁` and `E₂`; both are uniform PPT machines. -/
theorem yaoHybrid_simulators (hE₁ : PolyTimeComputable E₁) (hE₂ : PolyTimeComputable E₂)
    (hG₁ : PRFOut (.add .var .var) G₁) (hG₂ : PRFOut (.add .var innerLen) G₂)
    (hG₁₂ : PRFOut (.add (.add .var .var) (.add .var innerLen))
      (fun n s x => Fin.append (G₁ n s x) (G₂ n s x))) :
    ∃ SA SB : NUPPT, ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n (x : Fin ((yaoFunctionality Y).inA.eval n) → Bool)
        (y : Fin ((yaoFunctionality Y).inB.eval n) → Bool),
        distAdv ((yaoHybrid Y E₁ E₂).realA (yaoFunctionality Y) n x y)
            ((yaoFunctionality Y).idealA SA n x y) (D.distinguisherL n) ≤ ε n ∧
          distAdv ((yaoHybrid Y E₁ E₂).realB (yaoFunctionality Y) n x y)
            ((yaoFunctionality Y).idealB SB n x y) (D.distinguisherL n) ≤ ε n := by
  sorry

include hGE₁ hGE₂ in
/-- **Theorem 163.7 in the OT-hybrid model** [PS10, Theorem 163.7; Gol04, §7.3]: for a uniform
fan-in-two circuit family whose output vertices are sinks, and nested special encryption from two
pseudorandom function families `G₁`, `G₂` with polynomial-time evaluators `E₁`, `E₂`, jointly
pseudorandom under one key, Protocol 162.6 in the OT-hybrid model is an honest-but-curious secure
protocol for the family's functionality. The real protocol (composition with Protocol 160.4) is
not in this file.

**Deviation.** The joint PRF hypothesis `hG₁₂` (see `yaoHybrid_simulators`).

Proved from `yaoHybrid_polyTime` and `yaoHybrid_simulators`. -/
theorem yaoHybrid_hbcSecure (hE₁ : PolyTimeComputable E₁) (hE₂ : PolyTimeComputable E₂)
    (hG₁ : PRFOut (.add .var .var) G₁) (hG₂ : PRFOut (.add .var innerLen) G₂)
    (hG₁₂ : PRFOut (.add (.add .var .var) (.add .var innerLen))
      (fun n s x => Fin.append (G₁ n s x) (G₂ n s x))) :
    (yaoHybrid Y E₁ E₂).HBCSecure (yaoFunctionality Y) :=
  (HybridProtocol.hbcSecure_iff (yaoHybrid Y E₁ E₂) (yaoFunctionality Y)).mpr
    ⟨yaoHybrid_polyTime Y E₁ E₂ hE₁ hE₂,
      yaoHybrid_simulators Y E₁ E₂ G₁ G₂ hGE₁ hGE₂ hE₁ hE₂ hG₁ hG₂ hG₁₂⟩

end Security

end TCSlib.Cryptography.SecureComputation
