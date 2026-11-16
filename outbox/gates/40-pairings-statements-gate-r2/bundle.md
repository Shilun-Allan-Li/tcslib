## ===== briefs/pairings/gates/40-pairings-statements/pack-r2.md (records, at b356e50b1b908b26c1379f2fa9e53d604dabfe41) =====

# Gate 40 · Pairing campaign statements: bilinear groups, Joux, Boneh–Boyen BB1 (statement) · round 2

The auditor is Codex, under the standing ruling of 2026-11-11. Round 1 was **HOLD** (0 blockers, 2 majors, 4 minors,
0 notes); its findings are `findings/gate40-pairings-statements-findings.md` (SHA-256 `ceb63bfc…`). This round
re-audits the fixes of G40-01 to G40-06, checks the evidence of those fixes, the merge of the records tip into the PR
and one later docstring edit, and checks that nothing regressed and nothing new is undisclosed. The round-1 pack
(`pack.md`) still defines the scope; its questions stand for anything round 1 left unverified.

- **PR:** draft [PR #331](https://github.com/Shilun-Allan-Li/tcslib/pull/331), now at
  `9e7a96481785d6cac4dea3b2e990c49ac278b060` (branch `stmt/pairings`, tree `338335013c86f6014c7f617b5cfd3f30f2aabbee`).
  Round 1 audited `110c2f9db810d243693b9a5e8976a5ad205f1bab`.
- **Base.** The merge base with the records branch is now `673a27158338437896c624df32bf5421c6ba45cf`, the tip parent
  of the merge below (round 1: `523d80d2`). The PR diff `origin/cryptography/pass-shelat-ch2-4...9e7a9648` equals
  `673a2715..9e7a9648` byte for byte: the same 13 paths as round 1, 2293 insertions, 0 deletions (`pr.diff-r2.txt`,
  `checks/series.txt`). **No rebase:** `110c2f9d` is an ancestor of the head.
- **The tip** at staging was `e2f5850fcd1b38738f7ad2f2cd413c840803ef90`. From `673a2715` to it, 13 records commits
  changed no code path (`TCSlib`, `TCSlib.lean`, `audits`, `scripts`, lake files: 0 paths). It holds #332 (DAGCircuit
  readers) and #333 (GSW statements), both merged before the merge below; #327 and #324 are open.
- **New since round 1:** four commits on the first-parent chain, all by the maintainer (author and committer Claude,
  each with an SSH `gpgsig` header; `checks/series.txt` prints them with their messages):

  | Commit | What | Size |
  |---|---|---|
  | `3f9c49e5` | **LE-gate40**: G40-01 fields and BB1 proofs; G40-03, G40-04, G40-05 docstrings | 5 files, +187/−28 |
  | `70c1f444` | LE-gate40 proof fix (`dsimp only at h` in two of the new BB1 lemmas) | +2 |
  | `39d42e23` | merge of the records tip `673a2715` (with #332, #333) into `70c1f444`; facades by union | § 5 |
  | `9e7a9648` | **LE-doc-abs**: one module docstring ([BB04, §3.1] writes an absolute value) | 1 file, +3/−3 |

- **Resolutions:** `resolutions-r1.md`, and the decision-log rows of 2026-11-16 in `PairingCryptographyPlan.md`
  (bundle; ruling G40-01, LE-gate40 pushed, the merge, the DW-7 correction, #331 updated).
- **Not round-2 items.** The two Gate 40 notes for the later fills, T2's relational simulation step (a common augmented
  state or a shared relational lemma in `Games`) and the T4 fill route, are carried to those fill briefs. G40-03 here is
  only the T4 docstring.

Lean paths below are under `TCSlib/Cryptography/` unless they start with `TCSlib/`; `IB/` is
`AdvancedEncryption/IdentityBased/`.

## What to check

### 1. G40-01: do the three fields rule out the countermodel, faithfully to BB04's adversary view?

**Ruling G40-01 (Seyoon, 2026-11-16): injectivity fields.** `IBEScheme` gains three `Prop` fields: `encPP` injective on
the parameters of setup outputs; `encSK` and `encCT` injective on the keys and ciphertexts reachable under one setup
output. They are proved for `bb1Scheme` in this PR, with no new admission; efficiency stays deferred (Q5). The fields,
verbatim (`IB/Defs.lean:142–159`, docstrings omitted here):

```lean
  encPP_inj : ∀ κ, (setup κ).AllOutputs fun k => (setup κ).AllOutputs fun k' =>
    encPP κ k.1 = encPP κ k'.1 → k.1 = k'.1
  encSK_inj : ∀ κ, (setup κ).AllOutputs fun k => ∀ id id',
    (keyGen κ k.2 id).AllOutputs fun d => (keyGen κ k.2 id').AllOutputs fun d' =>
      encSK κ d = encSK κ d' → d = d'
  encCT_inj : ∀ κ, (setup κ).AllOutputs fun k => ∀ id id' m m',
    (enc κ k.1 id m).AllOutputs fun c => (enc κ k.1 id' m').AllOutputs fun c' =>
      encCT κ c = encCT κ c' → c = c'
```

- **The countermodel.** In round 1's instance the unique setup output admits both ciphertexts: `enc` returns `pure m`
  for the messages `0` and `1`, and `encCT` sends both to the zero bit. `encCT_inj` at `c = 0`, `c' = 1` fails, so the
  instance is no longer an `IBEScheme`. In general the fields make the adversary's wire view of each object it is given
  ([BB04, §2.1]: `params`, the private keys `d_i`, the challenge ciphertext `C`) an injective image of the typed
  object, among the objects the algorithms can output. They do not ask for efficient decoding (Q5), nor for injectivity
  on all of `PP κ`, `SK κ`, `CT κ`: round 1 advised against global injectivity, because BB1's key and ciphertext
  encodings omit the description and `PP κ` contains unreachable descriptions of any length.
- **The disclosure.** The structure docstring's **Deviation** paragraph (`IB/Defs.lean:98–105`), its list of
  components (`:94–96`) and the module docstring (`:28–33`) state the fields and their scope. The plan's deviation list
  (§ Sources, nine items) was not extended; the ruling row records the choice.
- **Scope details to rate.** `encSK_inj` quantifies over every identity, including `ID*` (whose key the game refuses),
  and `encCT_inj` over every message string `m, m'`, including strings outside `MsgSpace`, which the game never
  encrypts. Both are stronger than the game uses. Is that acceptable for the interface, or should the fields be
  restricted?
- **BB1** (`IB/BonehBoyen.lean`, section `Encodings`, `:231–324`): `bb1_encPP_inj` (`:243`; parameters whose
  descriptions have `descLen(κ)` bits), `bb1_encSK_inj` (`:277`) and `bb1_encCT_inj` (`:302`; keys and ciphertexts in
  one group), each with a `**Proof sketch.**`; the three `bb1Scheme` fields (`:369–384`) discharge the `AllOutputs`
  binds and apply them, `encPP_inj` with `G.length_desc` for both setup outputs, the other two under the description of
  the one setup output (`Sigma.mk k.2.1`, `Sigma.mk k.1.1`). The `bb1Scheme` docstring (`:333–338`) says why the
  encodings are injective where the interface asks.
- **What else changed** (`checks/legate40.txt`). With every comment removed, the code diff of LE-gate40 is a pure
  insertion: the three fields in `Defs`, and in `BonehBoyen` the `Encodings` section and the three `bb1Scheme` fields.
  `Group`, `Assumptions` and `BonehBoyenMachine` are code-identical. Declarations against round 1: 3 ADDED (the BB1
  lemmas), 0 REMOVED; `IBEScheme` and `bb1Scheme` change by those fields only (17 → 20 each, the round-1 fields in
  order); decls2 against round 1 lists only the 3 additions (`checks/decls2-110c2f9d-vs-9e7a9648.tsv`), and against
  the base 144 ADDED. The headers of T1–T4 and `bb1_sidSecure` are identical at `110c2f9d`, `70c1f444` and the head.
  `bb1Scheme` is the only `IBEScheme` in the tree, and nothing else uses the new names.
- **Axioms** (the integration probe on the merged tree, § 7): `bb1_encPP_inj`, `bb1_encSK_inj`, `bb1_encCT_inj`
  (closures 1530, 1526, 1531) and `bb1_correct` (whose closure, 8663, contains `bb1Scheme`) use `[propext,
  Classical.choice, Quot.sound]` with no `sorryAx` in their closures. LE-gate40's census: 384 constants, 12 new, no
  changed axiom set.

Do the fields close G40-01 under the ruling, and are they faithful to [BB04, §2.1]'s adversary view?

### 2. G40-02: the canonical seal suite on 10 owners (`landing-r1/`, LE-gate40)

The owners (`rule10/modules.txt`) are the eight substantive modules `Pairing/Group`, `Pairing/Assumptions`,
`Pairing/Operations`, `KeyExchange/Joux`, `IB/Defs`, `IB/BonehBoyen`, `IB/BonehBoyenMachine`, `IB/BonehBoyenSecurity`,
and the facades `AdvancedEncryption/IdentityBased` and `AdvancedEncryption`. The other three changed files,
`Pairing.lean`, `KeyExchange.lean` and the root `TCSlib.lean`, contain imports and options only
(`checks/sealbinding.txt`). Every probe ran with `-DmaxErrors=0` on the LE-gate40 worktree at `70c1f444`.

- **Seals** (term-collected, closure-complete; the archived Gate 06/10 instrumenter): strict A/B and coe A/B, **40
  probes = 4 × 10 owners**: rc 0, 0 errors, install and EOF records present, no failing declaration; requests 567–1101,
  of which 92–186 matchers and 24–61 instances. `checks/sealbinding.txt` re-derives each of the 40: the probe file
  hashes to its recorded `probe_sha256`; removing the recorded insertions (each checked against its own hash) gives back
  the owner's source, which equals its blob at `70c1f444`; the run record of that probe has the probe's hash and rc 0.
  **40/40.**
- **Paired controls**, strict and coe, 9 sealed and 9 unsealed probes each: **43 sealed negatives** (`rfl`/`Iff.rfl`
  unfoldings of `PolyExpr.eval`, `padFin`, `OracleComp.AllOutputs`, `BilinearGen.desc`, `DBDHAssumption`,
  `IBEScheme.Correct`, `IBEScheme.sidImpl` and `BB1.F`, in each owner whose request set contains the name) each fail
  exactly once; the 43 paired readers (`eval_const`, `padFin_def`, `allOutputs_pure`, `desc_eq`, `dbdhAssumption_iff`,
  `correct_iff`, `sidImpl_init_none`, `F_eq`) pass; every unsealed probe passes. **ALL_OK True** for both. Attempt
  1's `sidImpl` row was restated (LE README) and is kept in `rule10/controls-attempt1/`.
- **Explicit-unfold scan** of the 13 files: 164 items, 116 THEOREM, 40 LOCAL_OR_UNRESOLVED (local hypotheses,
  dot-notation theorems and fields), 8 OWNED_DEFINITION (same-file `simp [sidImpl]`, `simp [bb1SimKeyQ]`,
  `simp [bb1SimChal]`), **0 foreign**.
- **Binding to the head** (`checks/sealbinding.txt`). Eight owner sources are byte-identical at the head;
  `Assumptions` differs in its module docstring only (LE-doc-abs, § 6); the `AdvancedEncryption` facade gains the
  `Homomorphic` import (the merge, § 5). The seals ran on the closure of `70c1f444`, based on `523d80d2`. At the head
  the owners' closures have the same modules except the `AdvancedEncryption` facade (82 → 106: GSW and its imports), and
  three closure modules changed: `Complexity/ClassP/DTIME` and `Complexity/Randomized/Build/IterateFind` (#326; in the
  closures of `Operations`, `BonehBoyenMachine`, `BonehBoyenSecurity` and both facades) and `Pairing/Assumptions`
  (docstring only). **The seals were not re-run on the merged tree.** The integration build (§ 7) rebuilt every owner
  there, rc 0.

Is this the required Rule 10 evidence for every module with a proof or a definition? Is the evidence at `70c1f444`
sufficient for the head, given the binding above, or is a re-run on the merged tree necessary (a major if necessary
evidence is missing)?

### 3. G40-03, G40-04, G40-05: the docstring fixes

All in LE-gate40; `Group`, `Assumptions` and `BonehBoyenMachine` are code-identical (`checks/strip-verify.txt` in the
evidence; `checks/legate40.txt`), and `BonehBoyen`'s only code changes are those of § 1.

- **G40-03** (`IB/BonehBoyenMachine.lean:56–78`, T4's sketch): `n = κ + wG(κ) + 1`; each of `α_1` and the `r`s is
  `(Candidates.sampleBelowL p (Nat.size p) n n w).getD 0` on its own block `w` of `n²` fresh coin bits; `p ≤ 2^{wG(κ)} <
  2^n` and `0 < p`, so `statClose_sampleBelowL` gives `(1/2)^n ≤ 2^{−κ}` per draw; at most `q(κ) + 1` draws from
  independent blocks, `σ(κ) = (q(κ) + 1) · 2^{−κ}`. It also spells out modular negation and subtraction through `H`'s
  natural-number functions (truncated subtraction alone is not modular subtraction), the inverse by `xgcdStr` with
  `0⁻¹ = 0`, and `Games.exists_toCompOn_of_toComp` for the handler theorem's interface (round 1's T4 paragraph).
- **G40-04.** T4 now carries [BB04, §4.2, the algorithm `B` in the proof of Theorem 4.1, whose cost is the theorem's
  `Θ(τ ℓ q_S)` with the paper's hierarchy depth `ℓ = 1`] (`:56–58`). T1's **Source** (`Pairing/Assumptions.lean:
  203–205`): "not stated in [BB04] or [Jou00], which define the two problems ([BB04, §3.1]). The implication is
  independently derived here: the folklore fact that deciding is no harder than computing." `Pairing/Group.lean`: the
  module docstring (`:28–29`), `BilinearGroup`'s **Deviation** (`:85–88`) and `bilinear_pow` (`:149–151`) now say that
  the reader is the natural-exponent case and that the paper's `a, b ∈ ℤ` law follows from the homomorphism fields
  (`map_zpow` in each argument).
- **G40-05.** `BB1.decrypt_encrypt` (`IB/BonehBoyen.lean:182`) and `bb1_correct` (`:392`) mark their existing proof
  paragraphs `**Proof sketch.**`; the prose is unchanged apart from line breaks.

Do the texts now meet the findings' proposed fixes, and are they accurate?

### 4. G40-06: the README and the PR description

- **README** (`briefs/pairings/README.md`, bundle). Its current checkpoint was refreshed for G40-06 at records
  `4f416a8f`: #331 at `110c2f9d`, base `523d80d2`, the Gate 40 hold and ruling G40-01, and the seal coverage stated
  explicitly (12 canonical probes over three modules; six modules on hand-list probes until LE-gate40). Historical
  entries are kept. It now lags the head: it still names `110c2f9d` and calls LE-gate40 "in progress" (a known slip, see
  below).
- **PR description.** The live description is still round 1's (it names `110c2f9d`, "the whole-file seals pass
  12/12"; `pr-description.md`, fetched again at staging, unchanged). Its replacement is `pr-description-r2.md` (bundle):
  the head and base, the history since round 1, the Gate 40 status, and the checks of § 2 and § 7 with the coverage
  stated per module. The maintainer applies it to the PR before this round is dispatched; if the live description
  differs from `pr-description-r2.md` when you audit, say so.

Are the current summaries now accurate, with the historical entries preserved?

### 5. The merge onto the tip (`39d42e23`): the facade union and nothing else

`checks/merge.txt`; `merge-r2.diff.txt` shows the combined diff and the diff against each parent.

- **Parents:** `70c1f444` (#331 after LE-gate40) and the records tip `673a2715`; their merge base is `523d80d2`. The
  commit is signed. Its message names the union.
- **Every path, three ways** (merge base, parent 1, parent 2, merge): 11 paths taken from #331 alone (= parent 1); 177
  from the tip alone (= parent 2; 52 `.lean`: #318, #319, #323, #326, #332, #333 and records); **`TCSlib.lean`**,
  changed on both sides, equals parent 1: the tip's one added line, `import TCSlib.Cryptography.AdvancedEncryption`, is
  already in #331's version, so the union is #331's file; **`AdvancedEncryption.lean`**, added on both sides, differs
  from both: every line of each parent is kept and every line comes from a parent (both imports, both Contents entries,
  both references). No other path differs from both parents.
- Both shared files are byte-identical to the union filed with the integration of 2026-11-16
  (`briefs/pass-shelat-ch5-8/maintainer/int-stmt-331-333-2026-11-16/resolved/`, in `verification-r2.zip`).
- **Against the tip parent** the merge changes exactly #331's own 13 paths (`523d80d2..70c1f444`); the 11 non-facade
  files are blob-equal to `70c1f444`. **Against that integration's scratch merge C4** (`cbfa9d85`: tip, #332, #333 and
  #331 at `110c2f9d`), the code trees differ in exactly the 5 files of LE-gate40.
- **Against the current tip** `e2f5850f`, the head's code paths differ in the 13 PR files only, and `git merge-tree`
  with the tip is clean with the head's `TCSlib`, `TCSlib.lean`, `audits` and `scripts` subtrees.

This discharges round 1's merge conditions: #333 merged first, so #331 took the union, and the merged tree was rebuilt
(§ 7). Is the merge a pure union, with no other change?

### 6. LE-doc-abs against the DW-7 BB04 transcription

`ledocabs.diff.txt` (= `git diff 39d42e23 9e7a9648`, 1 file, +3/−3); `checks/ledocabs.txt`.

- The edit is inside `Pairing/Assumptions.lean`'s module docstring (lines 15–65; the hunk at 37), code-identical with
  comments removed. Old: "the paper writes the difference of the probabilities of output `0`, without absolute value;
  the two are equivalent for the assumption since the negated machine is a PPT". New: "The decision advantage is the
  absolute difference of acceptance probabilities; the paper writes the absolute difference of the probabilities of
  output `0` [BB04, §3.1], which is the same number, since outputs `0` and `1` are complementary."
- **The reference:** `blueprint/src/references/boneh-boyen-2004-selective-id-ibe.md` §3 (bundle; added by records
  `6078f369`, DW-7). Its §3.1 has `|Pr[B(g, g^a, g^b, g^c, e(g, g)^{abc}) = 0] − Pr[B(g, g^a, g^b, g^c, T) = 0]| ≥ ε`,
  with a transcription note: the `-layout` extraction drops the bars and the page image shows them. The file's header
  says "scoped transcription for DW-7; awaiting Codex source review": the transcription is the reference here, not an
  audit object of this gate.
- The other advantage texts of the 13 files (`checks/ledocabs.txt`): `dbdhAdv` is `|Pr[D(P_BDH) = 1] −
  Pr[D(R_BDH) = 1]|` [BB04, §3.1]; the IBE advantage is the two-experiment difference, "twice" [BB04, §2.1]'s
  `|Pr[b = b'] − 1/2|`; Joux's eavesdropper advantage is an absolute difference.
- Round 1's pack called the absolute value of `dbdhAdv` a deviation from "[BB04, §3.1]'s signed difference
  (deviation 6)". The DW-7 transcription corrects that record: it is not a deviation.

Does the new text match [BB04, §3.1]? Is any other text of the 13 files inconsistent with the transcription?

### 7. The build evidence

**(a) LE-gate40** (`landing-r1/gate40-le-evidence.zip`, on the base `523d80d2`, olean tree `dl-oleans`):
- the 20-module closure of the changed modules (8 base + 12 pairing): **20/20 rc 0**, 0 `error:`, 0 `error(`; sorry
  warnings only T1 (`Assumptions` 1), T4 (`BonehBoyenMachine` 1) and T2/T3 (`BonehBoyenSecurity` 2). `BonehBoyen` failed
  twice before the `dsimp` fix (`build/closure-attempt1/`); the fix is `70c1f444`. All 20 sources equal their blobs at
  `70c1f444` (`build/source-binding.txt`). The root was not rebuilt there (disk); (b) covers it.
- the axiom census: 384 constants (372 at round 1's evidence, +12, none removed, no changed axiom set); `sorryAx`
  only in T1–T4 and `bb1_sidSecure`. Lint: § 8. The olean tree was restored (`457ba704…`, SNAPSHOT EQUAL).

**(b) The merge on the tip** (`integration-tip/int-331-tip-evidence.zip`, `39d42e23` on `dl-oleans`):
- the closure of root `TCSlib` and both `audits/*/Checks`: 1299 modules; **661 rebuilt** (the downstream of every
  module changed since the olean tree's base `eff2dcd0`: 561 oleans overwritten, 100 new; 638 reused), **661/661
  rc 0**, 0 `error:`, 0 `error(`, substring "error" 0; 103 sorry warnings; 463 warnings. All 661 built sources equal
  their blobs at `39d42e23`, and every one of the 1299 modules has a record with the merge's source
  (`checks/srcequality.txt`). Whole-tree check (every olean = its record, none missing, no stray): **RESULT OK**.
- **Admissions** (`sorry` warnings over the closure): tip `673a2715` **237** → head **241**: the 11 new modules add
  T1 (`Assumptions` 1), T2/T3 (`BonehBoyenSecurity` 2) and T4 (`BonehBoyenMachine` 1); no existing module changes.
- **Axioms** (`import TCSlib` probe): `bb1_correct`, `joux_correct`, `jouxKeyIndist_of_dbdhAssumption` and the three
  `bb1_enc*_inj` standard, with no `sorryAx` user in their closures; T1–T4 each the only direct `sorryAx` user in its
  closure; `bb1_sidSecure` inherits exactly T2–T4 (T1 is not in its closure). `GSW.eval_encrypts` is the tip's own
  GSW admission, unchanged.
- **Incident.** About 08:59:50–09:00:25 UTC a full `git archive` during the lint step filled the disk and stopped
  another job's build. This build's 31 modules from that window were rechecked: identical oleans, logs, sorry and
  warning counts (the ZIP's `checks/incident-*`). Restore: SNAPSHOT EQUAL `457ba704…`.
- **The head** differs from `39d42e23` only by LE-doc-abs: one module docstring, code-identical. It was not rebuilt
  after that edit.

Is the evidence sufficient for the head, and does it show no regression?

### 8. Lint

`scripts/campaign_style_lint.py TCSlib/Cryptography --check8b`: tip 92 FAIL / 101 WARN, head 92 / 103. The two new
lines are check-8 WARNs, unchanged since round 1 (round 1's pack: "2 check-8 acronym WARNs"):
`IB/Defs.lean` (`SIDSecure`) and `Pairing/Assumptions.lean` (`BDHAssumption`, `DBDHAssumption`). Each definition has
an `Iff.rfl` reader with its formula in the docstring: `sidSecure_iff` (`IB/Defs.lean:426`), `dbdhAssumption_iff`
(`Pairing/Assumptions.lean:154`), `bdhAssumption_iff` (`:196`). Check 8 accepts a lemma named `<Name>_…` or with only
the first letter lowered (`sIDSecure_`, `dBDHAssumption_`); the campaign names acronym readers in lower camel case
(precedent `dlweAssumption_iff`). `checks/lint.txt` prints the lines, the readers and the heuristic. No new FAIL.

### 9. Duplication and the round-1 confirmations

- **New public names since round 1:** the three BB1 lemmas and the three fields. No other file mentions them. A
  statement scan (decls2 normalisation, name removed) of the three lemmas against all 15,610 theorems of `TCSlib` at
  the head has **0 hits**. The proofs use public lemmas: `ofFn_padFin_of_length` (`Asymptotic/Adversary.lean`),
  `List.append_inj'`, `List.ofFn_inj`, `encG_injective`, `encT_injective` and `BilinearGen.length_desc`
  (`checks/dupscan.txt` also lists the other `padFin` lemmas of the tree). **Any undisclosed duplicate of a public
  lemma is a major.**
- **Unchanged since round 1:** `Pairing/Operations`, `KeyExchange/Joux`, `IB/BonehBoyenSecurity` (T2, T3 and the proof
  of `bb1_sidSecure`) and the `IdentityBased`, `Pairing` and `KeyExchange` facades are byte-identical; `TCSlib.lean`
  too. Round 1 confirmed the truth of T1–T4 on their routes, the sufficiency of T2–T4 for `bb1_sidSecure` (`2δ + 4σ +
  dbdhAdv D₀ + dbdhAdv D₁`), the completed proofs (group facts, Joux, `decrypt_encrypt`, `bb1_correct`, the case
  readers), the setup order, the simulator, the fill-unit split, the layout and the facades. Is any of these affected by
  the new fields (for example `bb1_correct` or the simulator's use of `bb1Scheme`), by the merge or by LE-doc-abs?

## Merge interaction (maintainer merge conditions, not audit items)

`checks/mergetrees.txt`: `git merge-tree --write-tree` of the head with each of these is clean, and no path is shared
with #331's 13 files.

| With | Head | Own paths | Modules whose closure meets both sides' Lean changes |
|---|---|---|---|
| the records tip | `e2f5850f` | 31 (records only, since `673a2715`) | none; merged code subtrees = the head's |
| #327 seq-zk | `a94ba750` | 41 `.lean` | root `TCSlib` only |
| #324 sc-compose | `4bd2d80b` | 16 `.lean` | root `TCSlib` only |

#327 and #324 were marked clear to merge on 2026-11-16 (their cross-build). Whichever lands before #331, the maintainer
updates #331 and re-checks the root on the merged tree; that is a merge condition, not an audit item.

## Known dispositions and slips (not findings)

- **`landing-r1/` ZIP and its manifest.** The manifest lists 453 paths; the ZIP holds 448 of them, all matching, plus
  `SHA256SUMS` (byte-equal to the manifest). The 5 absent paths are runner bookkeeping files `current.pid` (one line,
  the PID and module of the runner's last Lean process; see the integration ZIP's `build/current.pid` for the format)
  under `build/closure/`, `rule10/{seal-runs,control-runs-r2,probe-runs}/` and `scan/runs/`. They carry no result. The
  ZIP's `README.md` is its provenance (it has no separate `PROVENANCE.txt`).
- **The README** names `110c2f9d` and LE-gate40 "in progress" (§ 4). The maintainer refreshes it to this head.
- **The plan.** § Sources item 6 still says [BB04, §3.1] "is written without an absolute value"; the decision-log row
  "DW-7 ingests" records the correction. The plan's identity table and the statement-phase `EVIDENCE.md` name earlier
  heads; they are historical. This staging did not edit the plan.
- **The transcription note's last sentence** says the draft "takes the signed form as a deviation". It does not: the
  Lean takes the absolute form (`Pairing/Assumptions.lean:36–39`, `dbdhAdv`). The note is a DW-7 records text, left to
  the DW-7 source review.
- **`findings/README.md`** still says "Nothing is filed yet"; the findings file is beside it.
- **`%G?` prints N** for every commit: this machine has no `gpg.ssh.allowedSignersFile`; each commit carries one SSH
  `gpgsig` header.
- **The `jouxMsg` control row** is not exercised: no sealed owner other than `Joux` itself requests `jouxMsg`.
- **LE-gate40's first background run** of the Rule 10 driver was stopped by a 30-minute limit after 41 of 76 probes;
  the rest ran from the resume script with the same runner, appending to the same records (LE README).
- **Job-local names.** The evidence refers to `$SP` paths and the `wt-gate40` worktree; the records copies have the same
  bytes.

## Evidence files

- **`resolutions-r1.md`** and **`findings/`**: the round-1 dispositions and findings.
- **`le-gate40.diff.txt`**: `git diff 110c2f9d 70c1f444` (5 files, +189/−28), SHA-256 `5094bec0…`.
- **`merge-r2.diff.txt`**: the merge `39d42e23`: its combined diff (`git show --cc`), and against each parent the
  stat and the diff of the two shared files, SHA-256 `ad93d4ab…`.
- **`ledocabs.diff.txt`**: `git diff 39d42e23 9e7a9648`, SHA-256 `ad773858…`.
- **`pr.diff-r2.txt`**: `git diff origin/cryptography/pass-shelat-ch2-4...9e7a9648`, which equals `673a2715..9e7a9648`
  byte for byte (13 paths, 2293 insertions), SHA-256 `8cc4afd1…`.
- **`source-head-r2.json`**: hashes, line counts and over-width counts of the 13 files at the head (no line over 100
  characters; the largest file is `IB/BonehBoyen.lean`, 677 lines).
- **`sources-r2.zip`**: the import closure at the head of every changed module, 110 files (round 1: 86; the
  `AdvancedEncryption` facade now also imports `Homomorphic`, the GSW modules). The root `TCSlib.lean` is included as a
  file, not as a closure root.
- **`verification-r2.zip`**: `SHA256SUMS` lists every other entry, and `PROVENANCE.txt` gives each source.
  - `evidence/landing-r1/`: `gate40-le-evidence.zip` (SHA-256 `5be013be…`, 486 entries) and its manifest;
  - `evidence/integration-tip/`: `int-331-tip-evidence.zip` (SHA-256 `3227f70b…`, 821 entries), its manifest and
    `PROVENANCE.txt`;
  - `records/`: the plan, and the integration of 2026-11-16 that produced the union (PROVENANCE and the two resolved
    files);
  - `checks/`, generated from git objects and the two evidence ZIPs (nothing was built): `series`, `legate40`,
    `decls2-*`, `merge`, `ledocabs`, `mergetrees`, `srcequality`, `sealbinding`, `evidence` (both ZIPs against their
    manifests and every entry this pack cites), `lint`, `dupscan`, `facades`, with their scripts.
- **`pr-description-r2.md`**: the replacement PR description (§ 4).
- **Round 1:** `outbox/gates/40-pairings-statements-gate/` on the exchange at
  `870bed6ca6d79f43599ab2972f74834137672b2a`, with records `356321accdd29b9ec73391b1c7b211b7d4cabf0f`; `pack.md` here is
  its pack. `policy.md` and the source excerpts are unchanged since that records pin.

## Findings delivery

Return `gate40-pairings-statements-r2-findings.md` as Markdown in this chat. If you have several evidence files, return
a ZIP. Use the same table and severities as round 1, and say for each round-1 finding whether it is closed. Report the
audited head and the counts by severity. The gate closes at zero blockers and zero majors.

## ===== briefs/pairings/gates/40-pairings-statements/resolutions-r1.md (records, at b356e50b1b908b26c1379f2fa9e53d604dabfe41) =====

# Gate 40 · resolutions, round 1 · HOLD → round 2 staged

Codex's verdict is **HOLD**: 0 blockers, 2 majors, 4 minors, 0 notes.
- **Findings:** `findings/gate40-pairings-statements-findings.md`, SHA-256
  `ceb63bfc9c309eca34d3aef1f57cae0e636082a3b7d7ec2aeef99d4f06edd670`.
- **Audited head:** `110c2f9db810d243693b9a5e8976a5ad205f1bab`, records `356321ac`, exchange `870bed6c`, PR merge base
  `523d80d2`.

Codex found no mathematical defect in the completed proofs and no counterexample to T1–T4. It confirmed:
- T1–T4 are true on their sketched routes, and T2–T4 imply `bb1_sidSecure` with exactly its stated hypotheses (`H`,
  `O`, `hN`, `h`): the nine-game chain gives `2δ + 4σ + dbdhAdv D₀ + dbdhAdv D₁`; T1 is not used.
- The bundle, the generator, BDH and DBDH, the selective-ID handler, BB1 and the simulator agree with [BB04] and
  [Jou00] under rulings Q1–Q13 and the location ruling; sampling `Setup` before the run is distributionally valid for
  every adversary.
- The completed proofs are correct: the group facts, Joux correctness, `jouxGame_eq_dbdhGame` (its final `rfl` reads
  only the local `jouxMsg`), `jouxKeyIndist_of_dbdhAssumption`, `BB1.decrypt_encrypt`, `bb1_correct`, the 21 case
  readers and `bb1_sidSecure` from T2–T4.
- Every public definition has a reader; no new `@[simp]`. The layering, the three fill units (disjoint owned files),
  the facades, widths and imports satisfy the rulings and policy. No duplicate public result.

| # | Severity | Disposition |
|---|---|---|
| G40-01 | major | **Fixed by LE-gate40** under **ruling G40-01 (Seyoon, 2026-11-16): injectivity fields.** `IBEScheme` gains `encPP_inj` (the parameter encoding is injective on the parameters of setup outputs), `encSK_inj` and `encCT_inj` (the key and ciphertext encodings are injective on the keys and ciphertexts reachable under one setup output), with a **Deviation** sentence in the structure docstring: fidelity is injectivity on reachable objects, not efficient decoding (Q5) and not global injectivity. Round 1's countermodel violates `encCT_inj` (its two reachable ciphertexts share the encoding), so it is no longer an `IBEScheme`. `bb1Scheme` proves the three fields from the new public lemmas `bb1_encPP_inj`, `bb1_encSK_inj`, `bb1_encCT_inj` (each with a proof sketch; standard axioms); no new admission, and T1–T4 and `bb1_sidSecure` are unchanged. Commits `3f9c49e573fe56ac72c33a3f960f4229a29a9a5e` and `70c1f44432a41bcdb6f6d8602d957d2fc68ce0da` (a two-line proof fix). Evidence: `landing-r1/gate40-le-evidence.zip` (SHA-256 `5be013be1aeb4dd8feb0f3f1f458b1fd0bbab882df80048e2bd043eadbb1d7d5`): 20/20 modules rc 0 on the base; 384 constants in the axiom census, `sorryAx` only in T1–T4 and `bb1_sidSecure`; and the build of the head on the tip (below). |
| G40-02 | major | **Fixed by LE-gate40** (evidence only). The canonical suite was run at `70c1f444` on 10 owners: `Pairing/Group`, `Pairing/Assumptions`, `Pairing/Operations`, `KeyExchange/Joux`, `IdentityBased/Defs`, `IdentityBased/BonehBoyen`, `IdentityBased/BonehBoyenMachine`, `IdentityBased/BonehBoyenSecurity`, and the `IdentityBased` and `AdvancedEncryption` facades. The other three changed files (`Pairing.lean`, `KeyExchange.lean`, `TCSlib.lean`) contain imports only. Term-collected, closure-complete seals strict A/B and coe A/B: 40/40 probes rc 0, 0 errors, install and EOF records, no failing declaration. Paired controls, strict and coe: 43 sealed negatives each fail exactly once, 43 readers pass, unsealed probes pass, ALL_OK True. Explicit-unfold scan: 164 items, 0 foreign (8 same-file definitions). Same evidence ZIP. |
| G40-03 | minor | **Fixed by LE-gate40** (docstring only, code-identical). T4's sketch gives `n = κ + wG(κ) + 1`, draws by `(sampleBelowL p (Nat.size p) n n w).getD 0` on independent `n²`-bit blocks, `p ≤ 2^{wG} < 2^n` and `0 < p`, error `(1/2)^n ≤ 2^{−κ}` per draw and `σ = (q + 1) · 2^{−κ}`; it also states the modular arithmetic through `H` and `exists_toCompOn_of_toComp`. T4's statement is unchanged. |
| G40-04 | minor | **Fixed by LE-gate40** (docstrings only, code-identical). T4 tagged [BB04, §4.2, the algorithm `B` in the proof of Theorem 4.1]; T1's source line now describes the implication as independently derived folklore, with [BB04, §3.1] defining the two problems; `Group.lean` (module, `BilinearGroup`, `bilinear_pow`) distinguishes the natural-exponent reader from the signed-exponent law, which follows from the homomorphism fields. |
| G40-05 | minor | **Fixed by LE-gate40.** `BB1.decrypt_encrypt` and `bb1_correct` mark their proof paragraphs `**Proof sketch.**`. |
| G40-06 | minor | **Fixed in the records; the PR-description part is drafted.** The pairings README's current checkpoint was refreshed at records `4f416a8f6f8381fb48aee44b4d7670a135e7fa7d` (head `110c2f9d`, base `523d80d2`, the hold and ruling, the seal coverage stated explicitly); historical entries are kept. The replacement PR description `pr-description-r2.md` states the head, the history and the coverage per module; the maintainer applies it to #331 before round 2 is dispatched. The README's checkpoint has to be refreshed again to the round-2 head (`pack-r2.md`, known slips). |

Since LE-gate40 the head also took a signed merge of the records tip, `39d42e235a62b7085ffc19b01f371015c20d7795` (#332
and #333 merged; the shared facades `TCSlib.lean` and `AdvancedEncryption.lean` resolved by the filed union; diff
against the tip = #331's 13 files), and **LE-doc-abs** `9e7a96481785d6cac4dea3b2e990c49ac278b060` (docstring only:
[BB04, §3.1] writes the decision advantage with an absolute value, per the DW-7 transcription). The build of the merge
on the tip (`integration-tip/int-331-tip-evidence.zip`, SHA-256
`3227f70b77ce455994efe86c90f2fb6b2e3bf8b16a2fffa7508f1a87a6662eb8`): 661/661 rc 0 over the 1299-module closure,
admissions 237 → 241 (T1–T4 only), standard axioms for the proved results and the three new lemmas, whole-tree check
OK. This discharges round 1's merge conditions (#333 merged first; #331 took the union; the merged tree was rebuilt).

**Notes carried to the fill briefs (not round-2 items).** T2 (`bb1-sim`): `ProbComp.expect_simulate_congr` has one
state type, so the fill reduces to a common augmented state with the existing abstraction and eager-sampling APIs, or
requests a shared relational lemma in `Games` (not a private BB1 host). T4 (`bb1-machine`): the sampler parameters of
G40-03, modular negation and subtraction through `ArithmeticFP`'s natural-number functions, `xgcd` with `0⁻¹ = 0`, and
`exists_toCompOn_of_toComp` for the handler theorem.

**Round 2 staged:** `pack-r2.md` and the round-2 files beside it (`SHA256SUMS-r2`); the Codex prompt is
`dispatch-r2.md`.

**Next:** Gate 40 round 2 (Codex) at `9e7a96481785d6cac4dea3b2e990c49ac278b060`.

## ===== briefs/pairings/gates/40-pairings-statements/findings/gate40-pairings-statements-findings.md (records, at b356e50b1b908b26c1379f2fa9e53d604dabfe41) =====

# Gate 40 — pairing campaign statement audit

**HOLD. Counts: 0 blockers, 2 majors, 4 minors, 0 notes.**

The four target statements have sound mathematical routes, and T2–T4 suffice for the stated
BB1 security theorem with its existing hypotheses. The hold concerns an unfaithful generic
serialization interface and missing required Rule 10 evidence. No mathematical error was found
in the completed Joux/group/BB1 proofs. Their Rule 10 clearance remains qualified below.

| Audited item | Pin |
|---|---|
| Repository / draft PR | [Shilun-Allan-Li/tcslib #331](https://github.com/Shilun-Allan-Li/tcslib/pull/331) |
| Lean head | `110c2f9db810d243693b9a5e8976a5ad205f1bab` |
| Campaign records | `356321accdd29b9ec73391b1c7b211b7d4cabf0f` |
| Exchange | `870bed6ca6d79f43599ab2972f74834137672b2a` |
| PR merge base | `523d80d2d4dd8e4ed6799358831e5b3806c6187b` |
| Pack | `outbox/gates/40-pairings-statements-gate/` |

The live GitHub metadata confirmed the requested draft/head. This audit made no repository
changes, dispatches, reviews, or merges. The shared-facade conflict and the listed merged-tree
rebuilds are maintainer merge conditions, outside the audit verdict.

## Findings

All Lean paths below are relative to `TCSlib/Cryptography/` at the audited head.

| ID | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|
| G40-01 | **major** | `AdvancedEncryption/IdentityBased/Defs.lean:99–136,161–170,233–256` · `IBEScheme`, `Correct`, `sidImpl` | Arbitrary lossy encodings can make a plaintext-revealing, typed-correct scheme satisfy `SIDSecure`. | Exact countermodel below; no encoding inverse, injectivity, or compatibility law is present. | Add a faithful serialization contract on reachable, context-valid objects and instantiate it for BB1. Preserve Q5's deferral of efficiency. |
| G40-02 | **major** | `verification/round1/tools/seal.py`; `evidence-extracts/rule10/modules.txt` | The hand-list seals do not meet the campaign's required Rule 10 coverage for the other substantive modules. | The canonical suite covers three modules, including one declaration-free facade. The four other modules containing completed proofs have only hand-picked lists. | Run the term-collected, closure-complete owner seals and explicit-unfold scan on the missing substantive modules, with verified source binding and controls. |
| G40-03 | minor | `AdvancedEncryption/IdentityBased/BonehBoyenMachine.lean:61–71` · T4 sketch | The sampler parameters do not justify the claimed error from the stated width bound alone. | `statClose_sampleBelowL` requires `p < 2^n` and uses `Nat.size p` bits inside each block; neither a trial count nor a sufficient block width is specified here. | Give explicit parameters as below. No change to T4's statement is needed. |
| G40-04 | minor | `BonehBoyenMachine.lean:54–71`; `Pairing/Assumptions.lean:200–205`; `Pairing/Group.lean:84–85,146–150` | Some declaration-level source text is missing or inaccurate. | T4 has no declaration-level source tag; T1 attributes an implicit “stronger assumption” assertion absent from the excerpt; `bilinear_pow` quantifies over naturals, although the bundle docstring says it derives the integer formula. | Add T4's source tag; describe T1 solely as the independently derived folklore implication; distinguish the natural-exponent reader from the signed-exponent consequence of the homomorphism fields. |
| G40-05 | minor | `AdvancedEncryption/IdentityBased/BonehBoyen.lean:173–198,264–293` · `decrypt_encrypt`, `bb1_correct` | The two substantive BB1 correctness proofs have prose sketches but omit the policy's standard sketch marker. | Both docstrings already explain the actual proof. | Mark those existing paragraphs `**Proof sketch.**`. No mathematical rewrite is required. |
| G40-06 | minor | `briefs/pairings/README.md` current checkpoint; current identity/status summaries; PR description checks | Current status and seal coverage are not presented accurately enough. | The current checkpoint still names `ce9c3728` and “not pushed”; the PR's “12/12” is a probe count for three modules, not full campaign coverage. | Refresh current summaries to the pinned head/base and state the three-module coverage explicitly. Preserve genuinely historical decision-log and provenance entries. |

### G40-01: the typed IBE game can hide the entire ciphertext

This is a fidelity defect in the generic interface, separate from the approved absence of an
efficiency field. Q5 does not authorize losing the objects supplied to the adversary.

Consider the following instance, at every security parameter:

1. All five length polynomials are the constant `1`. The identity and message sets are
   one-bit strings. Parameters, master keys, and private keys are singletons. Ciphertexts
   are one-bit strings. Every message is in `MsgSpace`.
2. `setup` and `keyGen` return the unique values. Define

   $$
   \operatorname{enc}(\kappa,\ast,ID,m)=\operatorname{pure}(m),
   \qquad
   \operatorname{dec}(\kappa,\ast,c)=\operatorname{some}(c).
   $$

3. Set all three wire encodings, particularly `encCT`, to the constant zero bit:

   $$
   \operatorname{encCT}(\kappa,c)=0
   \quad\text{for both }c=0,1.
   $$

The interface permits this instance. Its typed correctness is immediate:

$$
\operatorname{dec}(\kappa,\ast,\operatorname{enc}(\kappa,\ast,ID,m))
=\operatorname{some}(m)
$$

where the deterministic `pure` computation is identified with its returned value.

In the encoded `sidGame`, couple the two experiments using the same adversary coins.
Induct on the remaining query budget. Before `Init` both return zero on the other oracles;
`Init` returns the same zero parameter encoding; `KeyGen` returns either the same bottom
or the same validity-bit/key encoding. A first challenge records zero in both games, and
every later challenge returns that recorded zero. Thus identical query histories yield
identical next answers and identical next histories. Return and timeout also agree. Consequently,
for every adversary, budget, and parameter,

$$
\operatorname{advantage}
  (\operatorname{sidGame}(A,q,0,\kappa),
   \operatorname{sidGame}(A,q,1,\kappa))=0.
$$

The instance satisfies `Correct` and `SIDSecure` with error function identically zero.
In BB04's typed experiment the adversary instead receives the ciphertext `m_b` itself.
Choosing messages `0,1` and returning that ciphertext gives distinguishing advantage `1`,
or guess advantage `1/2`. It is a constant-time plaintext encryption example, so honest
efficiency would not repair the discrepancy.

**Required repair.** Relate the wire views to the typed objects. One sufficient formulation
provides decoding left inverses on reachable public parameters and on keys/ciphertexts in
the context of those parameters. Another formulation makes the honest operations, including
correct decryption, factor through the advertised encodings. Do not demand global injectivity
on BB1's unrestricted dependent-pair types: its key and ciphertext encodings intentionally omit
the description, which is known from the parameters, and its public-parameter type also
contains unreachable descriptions of arbitrary length.

For BB1 the intended contextual contract is available: generated descriptions have their exact
advertised length, and each fixed-description group encoding is injective. Concatenation at the
advertised widths loses no component on those reachable objects. The missing point is a
published contract linking that fact to the generic interface and security claim. This finding
does not supply a counterexample to T1–T4 or to BB1's particular algebra.

### G40-02: necessary seal evidence is missing

The pinned `briefs/pass-shelat-ch5-8/MAINTAINER-HANDOFF.md` `3 requires seals collected from
elaborated terms, including matchers, rather than hand-picked names; its tooling section also
requires the statement/definition-body sweep, whole-file proof seal, controls, and explicit
unfold scan. This is a pre-existing acceptance requirement, not a newly imposed test.

The twelve canonical probes are genuine source-preserving probes of:

- `BonehBoyenMachine`;
- `BonehBoyenSecurity`;
- the `IdentityBased` facade.

I reconstructed every original source by removing the manifest's recorded insertions, verified
the insertion/probe/source hashes, and matched the results to the pinned source bytes.
The supplied summaries report successful install/EOF checks for all twelve probes.
That establishes the reported coverage, not coverage of the imported proofs.

`Group`, `Joux`, `Defs`, and `BonehBoyen` contain completed proofs but have only the round-1
hand-list probes. `Assumptions` and `Operations` also need the applicable declaration/body
coverage. The “unknown constant” messages in three round-1 logs really concern names outside
the relevant closure; I do not misclassify them as failed theorem proofs. However, ignoring those
messages does not turn an incomplete name list into the required collected seal.

In particular, the one negative `Correct` control verifies that control, not completeness of
the foreign-definition inventory or protection against instance-related reduction. Canonical
sealing a downstream import does not re-elaborate the imported theorem bodies.

I found no explicit forbidden foreign unfold in the completed proofs on source review.
The `simp [sidImpl]` and `simp [bb1SimKeyQ]` calls unfold definitions in their own files,
which is allowed. The major is the missing required evidence, not an allegation that one of
those proofs is mathematically unsound.

### G40-03: make the sampler route precise

The upper bound from injectivity is only

$$
2\le p\le 2^{G.wG.eval(\kappa)}.
$$

Reading the entire advertised width on each rejection trial can have very poor acceptance
when encodings are padded. For example, `p = 3` and `wG(κ) = κ+2` give acceptance
`3/2^(κ+2)` per such trial. Polynomially many such trials need not sample nearly uniformly.
Also, `p ≤ 2^wG` is insufficient for the strict premise of the cited sampler theorem;
the equality case `p=2, wG=1` is allowed.

A uniform repair using the existing lemma is to take

$$
n=\kappa+G.wG.eval(\kappa)+1
$$

and use `sampleBelowL p (Nat.size p) n n`, with fallback `0`, on `n²` fresh coin bits.
Then `0 < p < 2^n`, and the existing bound is

$$
(1/2)^n\le 2^{-\kappa}.
$$

Allocate independent blocks for at most `q(κ)+1` draws. The statistical error is at most
`(q(κ)+1)2^(-κ)`, as claimed. This also handles small-order and residue-collision instances:
the arithmetic implementation must return the field inverse of zero as zero.

## Definitions and source fidelity

| Surface | Audit conclusion |
|---|---|
| Bilinear bundle | Equal prime orders, a nonidentity source generator, a bimultiplicative pairing, nondegeneracy, and injective element encodings match BB04 `2.2. Prime order supplies cyclicity; the homomorphism fields also imply the signed-exponent law. G40-04 concerns the reader's advertised domain only. |
| Generator | Uniform `NUPPT` generation, exact polynomial description lengths, total description interpretation, and explicit exceptional-order hypotheses implement Q1. Group-operation efficiency is separated as ruled, rather than silently assumed in the abstract bundle. |
| BDH / DBDH | The public generator is uniform in `G∖{1}`; exponents are independent uniform residues; random `T` is uniform in the target group. Generator coins are sampled first, so there is no dependent-seed weighting distortion. Nested input pairing and exact encoded BDH success match D3. Absolute decision advantage is disclosed and harmless under complement closure. |
| IBE interface | Four typed algorithms, parameter-dependent messages, fixed polynomial wire widths, and the two-experiment quantifiers implement Q5/Q9. G40-01 is the additional, undisclosed loss of serialization fidelity. |
| Selective-ID handler | The first `Init` fixes the target; later `Init` queries repeat parameters. Pre-init and forbidden-key queries return bottom; permitted keys use fresh coins. The first valid challenge is recorded, all later challenge calls repeat it, and invalid pre-challenge messages are refused. The nine case readers and three handler readers describe the code accurately. |
| Setup order | Before the first `Init` every answer is independent of setup coins, and all lengths depend only on the security parameter. Conditioning on adversary coins and the pre-init history therefore leaves the setup distribution unchanged. Sampling setup early is distributionally valid, including adversaries that never initialize, query before initializing, or initialize repeatedly. |
| Identity/message conventions | Binary identities are injective modulo `p` on the good-order event. The range starting at zero and the weak threshold `2^ℓ≤p` are mathematically valid for this fixed-length embedding. Message validity depends only on the description, not the BB1 random parameters. The off-space `decodeT=1` branch is never used for a fresh accepted challenge. |
| BB1 | Setup, its sample order, `F`, private keys, encryption, decryption, and description mismatch handling agree with the ruled depth-one BB04 construction. Uniform `h,g₂∈G`, including the identity, is faithful to the excerpt. |
| Simulator | Parameters, inverse-difference keys, and `(M_b T,Z,Z^α₁)` match BB04's proof of Theorem 4.1 at depth one. The target is compared as a string before residue arithmetic. For distinct strings with equal residues, the simulator remains a defined, generally incorrect key; T2 charges the bad-order event and T4 must implement that same value. |
| Joux | This is the explicitly ruled abstract single-point variant, not a claim to formalize the paper's alternating Weil pairing on one point. Key indistinguishability under DBDH is correctly identified as a new formalization of the `5 security discussion, not a security theorem stated by Jou00. |

Bottom on `KeyGen` is distinguished by its validity bit. The challenge uses the explicitly
chosen all-zero wire convention, with no separate validity bit; no argument here assumes
that all-zero strings cannot encode honest ciphertexts. Recording the first valid challenge
is what prevents fresh encryption on repeated calls.

The nine declared source deviations and Q1–Q13/location rulings are otherwise respected.
The source excerpts are the fidelity material authorized by Q12; this audit did not independently
obtain or authenticate the original PDFs. Their reported PDF hashes are provenance claims,
whereas the excerpt bytes and repository bindings were independently checked.

## Truth and sufficiency of T1–T4

These are mathematical statement-audit conclusions, not completed Lean proofs of the four
admissions.

**T1 is true with its stated hypotheses.** Parse and re-pair the encoded input, run the BDH
solver, and compare its output with the target encoding. No group operation or decoding is
needed. The nested `pairEncode` format permits polynomial-time projections and reassembly.
On a real tuple acceptance equals solver success; on a random tuple injectivity gives acceptance
at most `1/p`. Thus

$$
\Pr[\operatorname{bdhGame}(A,\kappa)=1]
\le G.dbdhAdv(D,\kappa)+\mathbb E_r[1/p]
\le G.dbdhAdv(D,\kappa)+2^{-\kappa}+\delta(\kappa).
$$

This proves the intended asymptotic implication. The exponential-order hypothesis is sufficient;
it is not claimed to be the weakest possible order condition. `Ops` is unnecessary.

**T2 is true for every adversary, budget, bit, and parameter.** On good generator coins,
distinct identity strings have distinct residues. For each committed target, replacing uniform
`h` by `X^(-ID*)g^α₁` is a bijection in `α₁`. For a permitted key, all exponents below are in
the prime field, and BB04's change of variables gives

$$
\begin{aligned}
F(ID)&=g^{a(ID-ID^*)+\alpha_1},\\
Y^{-1/(ID-ID^*)}g^r&=g^{\,r-b'/(ID-ID^*)},\\
Y^{-\alpha_1/(ID-ID^*)}F(ID)^r
 &=g^{ab'}F(ID)^{\,r-b'/(ID-ID^*)}.
\end{aligned}
$$

The shift of `r` is a bijection separately at each adaptive query. At the challenge,
`F(ID*)=g^α₁` and the real target supplies exactly the BB1 encryption mask. Refusal and
repeat branches agree. Hence the output laws agree conditional on every good description;
the unconditional gap costs only `Pr_r[p<2^ℓ]`, not that probability times the query count.

The cited `ProbComp.expect_simulate_congr` has a **single common state type**. It does not
directly establish the advertised relation between `SidState` and `BB1SimState`.
`simulate_eq_of_abs` supplies structural state abstraction, but not arbitrary distributional
re-randomization. The fill should first reduce to a common augmented state using the existing
abstraction/eager-sampling APIs, or request a shared relational-expectation lemma in `Games`.
A generic relation lemma must not become a private BB1 host or an undisclosed copied induction.
This is proof infrastructure work, not a missing mathematical hypothesis of T2.

**T3 is true, exactly.** Conditional on the history immediately before the first valid
challenge, `T` is still independent and uniform: prior initialization, key answers, and
invalid challenge answers never read it. The adaptively chosen messages are then fixed.
Multiplication by either decoded message permutes the target group, so `M_bT` is uniform
for either bit. The recorded ciphertext and every subsequent answer have the same joint law.
Runs without a valid challenge are already bit-independent. This establishes zero advantage;
an unconditional permutation chosen before seeing the adaptive history is not required.

**T4 is true on the sketched machine route, with the sampling clarification in G40-03.**
`Ops` supplies every needed group operation and membership test, while `ArithmeticFP`
supplies the modular arithmetic. Explicit modular negation/subtraction must be implemented
with the natural-number arithmetic APIs; ordinary truncated subtraction alone is insufficient.
`xgcd` supports the field inverse, including the defined zero case. The reduction need not
decode abstract elements: it operates on their encoded products/powers and validates message
encodings. It does not need `pairStr`, `memG`, target-group inversion, or a lower-order hypothesis.

Use `exists_toCompOn_of_toComp` when adapting the no-extra-input adversary to the handler
theorem's `toCompOn` interface. The resulting distinguishers are `NUPPT`, as the statement
says; uniformity of an arbitrary nonuniform adversary is not promised. Polynomial input,
coin, state, and query bounds are available. Off-distribution inputs can be handled with the
same bounded algorithms. No hypothesis that identities are noncolliding is needed in T4.

**T2–T4 imply exactly the stated headline.** The nine edges of the game's chain have bounds

$$
\delta,\quad \sigma,\quad G.dbdhAdv(D_0,\kappa),\quad
\sigma,\quad 0,\quad \sigma,\quad
G.dbdhAdv(D_1,\kappa),\quad \sigma,\quad \delta.
$$

Their sum is

$$
2\delta(\kappa)+4\sigma(\kappa)
+G.dbdhAdv(D_0,\kappa)+G.dbdhAdv(D_1,\kappa).
$$

The two DBDH advantages are negligible by the assumption; the other terms are negligible by
`hN` and T4. The existing code uses the appropriate symmetric orientations and eight triangle
inequalities, then `linarith`. The four `σ` and two `δ` charges are correct. It uses no T1.
The hypotheses `H,O,hN,h` are explicit, sufficient, and authorized by the rulings; the paper's
efficient-group convention is not being silently added to the Lean theorem.

## Completed proofs, reuse, and policy

| Item | Audit result |
|---|---|
| Group facts | `exists_pow_eq` follows from prime cardinality; symmetry follows by expressing both inputs as powers of the generator. `pair_ne_one` correctly rules out a prime dividing the squared exponent without dividing it. `pow_val_bijective` uses exact prime order, residue injectivity, and equal cardinalities. Exponent reduction modulo the common order is valid in both groups. |
| Joux correctness | `pow_val_mul_mul` correctly reduces products of residues. Bilinearity then gives the common key; commutativity of the exponent product gives agreement of all parties. No nonidentity assumption is needed for this algebraic equality. |
| Joux experiment equality | After both game readers and `jouxKey_eq`, the final `rfl` only needs the local `jouxMsg` body. It is not evidence of reading the foreign `tupleStr` body. |
| Joux security | Advantage equality transfers the DBDH assumption through its published predicate reader. It proves precisely the declared eavesdropper goal. |
| `BB1.decrypt_encrypt` | The proof's three pairing equalities give the common mask and cancellation factor; commutativity and division cancel them. It agrees with BB04's displayed computation. |
| `bb1_correct` | The honest-run reader, scheme field equations, setup/key/encryption readers, and `AllOutputs` binds cover every draw. Message-space membership supplies an actual encoded target-group element; `decodeT_encT` and the algebraic theorem finish. The description-equality branch is the honest branch. |
| Handler case readers | The nine real-game cases, three `oracleImpl` cases, and nine simulator cases match the definitions. The same-file simplifications are legitimate. |
| `bb1_sidSecure` | Correct derivation from the three admitted BB1 steps, with exactly the error sum above. It remains admitted-dependent; it is not an admission-free security proof. |

Every public definition has an equation, predicate, case, or structure-field reader; the
`bb1Scheme` field equations are non-simp. No new `@[simp]` API exception was found.
The small Joux experiment equality and its security corollary do not need a new long proof
sketch; the corollary already explains the reduction in prose. G40-05 concerns the two
substantive BB1 correctness proofs.

The source comparison supports the proposed layering:

- `BilinearGen` is a justified abstract sibling of the concrete modular
  `ExpGroupGen`/`SafePrimeGen` interfaces. The existing DDH substrate has no bilinear
  target group or pairing contract to reuse.
- The new BDH/DBDH experiments have different distributions and inputs from DDH;
  they reuse `Games` advantages rather than duplicating their theory.
- The IBE game needs commitment, extraction, and challenge state absent from the
  public-key game. The common codec, bottom/answer conventions, simulation, and triangle
  inequalities are reused. No duplicate proved public theorem was identified.
- `oracleImpl` is a small adapter tied to this scheme's three named lengths and its
  `sidSpec`. It is not a new generic execution host that must move into `Games` now.
  A future generic finite-family handler constructor should be shared rather than copied.
- `Operations` correctly keeps arithmetic dependencies out of `Group`. Its
  `Candidates.Arithmetic` import is broader than the particular `listToNat` and FP
  declarations used; narrowing it to the defining lower layer is a reasonable cleanup,
  not a correctness or modularity hold.

The three fill units own disjoint target files. T2/T3 use scheme/simulator definitions without
requiring a T4 proof; T4 does not depend on T2/T3. `BonehBoyenSecurity` imports the machine
module for the proved-modulo headline, which is consistent with the split. Helper modules
beside each owner suffice; any newly needed shared generic simulation lemma should be
commissioned into the shared layer rather than changing another unit's file.

Layout, namespaces, precise imports, line widths, and facade/root exports satisfy the location
ruling. All four facades list their children. The largest new module is 553 lines; no changed
line exceeds 100 characters. No bare `import Mathlib` occurs.

## Verification and limits

The independent verifier included with this report reads the pack and Git objects; it does
not execute the pack's scripts or invoke Lean.

| Check | Independently verified result |
|---|---|
| Top-level `SHA256SUMS` | 13/13 matching files |
| `verification.zip` manifest | 98/98 matching members |
| Round-1 manifest | 41/41 matching files |
| Round-2 inner manifest | 411/411 matching files; external and internal manifests identical |
| Source closure | All 86 files match blob identities in the pinned Lean Git tree |
| Bundle | All 18 sections match their pinned Lean/records source bytes |
| PR diff | Exact match to Git objects with `--abbrev=9`; the repository's default abbreviation length otherwise changes only index lines |
| Canonical probe reconstruction | All 12 probe/source/insertion hashes verified; reconstructed sources match the head; three distinct modules |
| Supplied replay evidence | Closure summary: 20/20 successful; root summary: 278/278 successful; four target admissions in the new modules |
| Supplied axiom census | 320 declarations + 52 auxiliary constants; `sorryAx` appears only in T1–T4 and `bb1_sidSecure` |

The pre-pin copies of the plan and EVIDENCE inside `verification.zip` were not mistaken for
the records pin. I read the pinned versions; the differences are the disclosed appended
gate/filing entries. The current handoff's Rule 10 requirements were also checked at the
records pin.

No independent Lean elaboration was performed. Compilation and axiom results above describe
the supplied, hash-bound evidence that was inspected. The mathematical countermodel in G40-01
is not presented as a Lean-checked construction. The missing canonical coverage in G40-02
cannot be replaced by this source review.

To close the gate, resolve G40-01 and supply the missing Rule 10 evidence in G40-02.
The four minor documentation corrections should accompany the repaired statement submission.
The user retains dispatch and merge authority.

## Notation glossary

- `S`: the generic IBE scheme in the countermodel; `*`: the unique value of a singleton type.
- `κ`: security parameter; `ℓ`: identity-length polynomial; `q`: query budget or its polynomial;
  `n`: the explicit sampler block width/trial count in G40-03.
- `G`: the bilinear generator; `p`: the generated group's prime order; `G_T`: its target group.
- `A`: an adversary/BDH solver; `D,D₀,D₁`: the reduction distinguishers.
- `b`: challenge bit; `ID,ID*`: queried and committed identities, read as residues in exponent formulas;
  `m,M`: messages; `c`: a ciphertext in the countermodel.
- `g,X,Y,Z,T`: the public generator and DBDH tuple entries, with
  `X=g^a,Y=g^{b'},Z=g^c` in the BB1 discussion; the exponent `c` there is unrelated to
  the countermodel ciphertext.
- `α₁`: simulator setup exponent; `r`: a key-generation exponent, or generator coins where
  explicitly subscripted in a probability/expectation.
- `δ,σ`: exceptional-order and simulation error functions; `H,O`: the arithmetic and group-operation contracts.
- `pure` / `some`: a deterministic probabilistic return / a successful optional result;
  `advantage`: the absolute difference of the games' probabilities of returning one.

## ===== briefs/pairings/gates/40-pairings-statements/pr-description-r2.md (records, at b356e50b1b908b26c1379f2fa9e53d604dabfe41) =====

This is the statement-phase PR of the pairing campaign (`PairingCryptographyPlan.md`). Seyoon ruled Q1–Q13, the location of IBE and G40-01 on 2026-11-16. It formalizes:
- **abstract symmetric bilinear groups** from a uniform PPT generator, with the BDH and decisional BDH (DBDH) assumptions;
- **Joux's one-round tripartite Diffie–Hellman** [Jou00];
- **Boneh–Boyen selective-ID IBE (BB1)** in the standard model [BB04, ePrint 2004/172, §4].

**Head:** `9e7a96481785d6cac4dea3b2e990c49ac278b060`. **Base:** `cryptography/pass-shelat-ch2-4`; the merge base is `673a2715`, and since then the branch has changed records only. The diff is #331's 13 files (+2293/−0).

## Modules
- `Pairing/{Group,Assumptions,Operations}.lean` and the `Pairing.lean` facade.
- `KeyExchange/Joux.lean` and its facade.
- `AdvancedEncryption/IdentityBased/{Defs,BonehBoyen,BonehBoyenSecurity,BonehBoyenMachine}.lean` and the `AdvancedEncryption/IdentityBased.lean` facade. The `AdvancedEncryption.lean` facade, shared with GSW, imports and lists both `Homomorphic` and `IdentityBased`.
- Root exports: `Pairing` and `KeyExchange` (the root already imports `AdvancedEncryption`).

Every file is under 1000 lines (the largest is `BonehBoyen.lean`, 677), and every line is at most 100 characters.

## Proved here
- Bilinearity, symmetry and non-degeneracy readers.
- Joux correctness ([Jou00, p. 388]), and key indistinguishability under DBDH (`jouxGame_eq_dbdhGame`). Joux states no security theorem; this result formalizes his §5 remark.
- BB1 correctness ([BB04, §4.1]).
- The injectivity of BB1's encodings on reachable objects: `bb1_encPP_inj`, `bb1_encSK_inj`, `bb1_encCT_inj`, which give `bb1Scheme`'s fields `encPP_inj`, `encSK_inj`, `encCT_inj` (ruling G40-01).
- `bb1_sidSecure` ([BB04, Theorem 4.1] at depth 1), derived from the targets below.

## Targets (`sorry`, with proof sketches)
- **T1** `bdhAssumption_of_dbdhAssumption`, a folklore result.
- **T2** `bb1_sim_real`.
- **T3** `bb1_sim_random`.
- **T4** `exists_bb1_distinguisher`, in its own module `BonehBoyenMachine.lean` (ruling Q11).

The fill units are `pair-bdh` (T1), `bb1-sim` (T2 and T3) and `bb1-machine` (T4). The last two own disjoint files and can run in parallel.

## History since Gate 40 round 1 (at `110c2f9d`)
- **LE-gate40** `3f9c49e5`, with the proof fix `70c1f444`:
  - **G40-01** (ruling: injectivity fields): `IBEScheme` gains `encPP_inj`, `encSK_inj` and `encCT_inj`. They state that the wire encodings are injective on the parameters of setup outputs, and on the keys and ciphertexts reachable under one setup output. This is not efficient decoding (Q5) and not global injectivity. BB1 proves them.
  - **G40-03, G40-04, G40-05**, docstrings only: explicit sampler parameters in the T4 sketch; T4's source tag; T1 described as independently derived folklore; `bilinear_pow` as the natural-exponent reader; `**Proof sketch.**` markers on `decrypt_encrypt` and `bb1_correct`.
- **Merge** `39d42e23` (signed) of the branch tip `673a2715`, which contains #332 and #333. The shared `TCSlib.lean` and `AdvancedEncryption.lean` are resolved by their union, and nothing else changes.
- **LE-doc-abs** `9e7a9648`, docstring only: [BB04, §3.1] writes the decision advantage with an absolute value (per the DW-7 transcription).

## Checks
- **Build of the head on the branch tip** (merge `39d42e23`; LE-doc-abs is docstring only):
  - the closure of root `TCSlib` and both `Checks` is 1299 modules; **661/661** rebuilt modules give rc 0 with 0 errors, and the whole-tree check passes;
  - admissions go **237 → 241**: T1–T4 only.
- **LE-gate40 build:** the 20-module pairing closure gives **20/20** rc 0.
- **Axioms:** Joux's results, `bb1_correct` and the three `bb1_enc*_inj` use the standard axioms only. Each of T1–T4 is the only `sorryAx` user in its closure, and `bb1_sidSecure` inherits exactly T2–T4.
- **Rule 10:** the canonical suite was run on **10** owners: the 8 modules with declarations (`Group`, `Assumptions`, `Operations`, `Joux`, `Defs`, `BonehBoyen`, `BonehBoyenMachine`, `BonehBoyenSecurity`) and the `IdentityBased` and `AdvancedEncryption` facades. The other three changed files (`Pairing.lean`, `KeyExchange.lean` and the root) contain imports only.
  - Seals strict A/B and coe A/B: **40/40** probes pass.
  - Paired controls: 43 sealed negatives each fail exactly once, and their readers pass (ALL_OK).
  - Explicit-unfold scan: 0 foreign unfolds.
  - In round 1 the canonical suite covered only 3 modules (12 probes); the other modules had hand-list probes.
- **Lint:** no FAIL. There are two check-8 WARNs, `SIDSecure` and `BDHAssumption`/`DBDHAssumption`. They are false positives of the acronym heuristic: the readers `sidSecure_iff`, `bdhAssumption_iff` and `dbdhAssumption_iff` exist.

**Disclosed deviations from the papers** (see the plan, § Sources, and the docstrings):
- the single-point Joux form, which non-degeneracy permits;
- BB1 is the depth-1 instance of BB04's HIBE;
- the IBE advantage is twice BB04's;
- the statements are asymptotic rather than concrete;
- the challenger answers forbidden queries with `⊥`;
- the encodings are injective on reachable objects (G40-01).

## Gate 40
- **Round 1** (Codex, at `110c2f9d`): **HOLD**, with 0 blockers, 2 majors and 4 minors. No mathematical defect was found, and T1–T4 were judged true and sufficient.
- The resolutions are in `briefs/pairings/gates/40-pairings-statements/resolutions-r1.md`. LE-gate40 fixes G40-01 to G40-05; G40-06 is this description and the README.
- **Round 2** (Codex) is staged at this head (`pack-r2.md`) and **pending**.

The evidence is in `briefs/pairings/gates/40-pairings-statements/` (`landing-r1/`, `integration-tip/`). Seyoon merges.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA

## ===== briefs/pairings/README.md (records, at b356e50b1b908b26c1379f2fa9e53d604dabfe41) =====

# Pairing campaign

Scope, sources, design decisions, statements, units, questions and the decision log are in
[PairingCryptographyPlan.md](../../PairingCryptographyPlan.md). Binding rules: `policy.md`,
`../pass-shelat-ch5-8/CLAUDE.md` and `../pass-shelat-ch5-8/MAINTAINER-HANDOFF.md` §2.

## Current checkpoint

Statement PR [#331](https://github.com/Shilun-Allan-Li/tcslib/pull/331) (draft), branch
`stmt/pairings`, audited by Gate 40 at head `110c2f9db810d243693b9a5e8976a5ad205f1bab` (merge base
`523d80d2d4dd8e4ed6799358831e5b3806c6187b`). Rulings Q1–Q13 and the location ruling are accepted.
Four sorried targets, T1–T4; `bb1_sidSecure` is proved from T2–T4.

Gate 40 round 1: **HOLD** (G40-01 encoding fidelity, G40-02 seal coverage, four minors). Ruling
G40-01: injectivity fields in `IBEScheme`, proved for BB1. The maintainer's landing edit LE-gate40
is in progress; Gate 40 round 2 follows.

**Seal coverage at `110c2f9d`.** The canonical Rule 10 suite ("12/12" in the PR description) is
12 probes over three modules only: `BonehBoyenMachine`, `BonehBoyenSecurity` and the
`IdentityBased` facade. `Group`, `Joux`, `Defs`, `BonehBoyen`, `Assumptions` and `Operations`
have round-1 hand-list probes only; LE-gate40 extends the canonical suite to them.

## Contents

* `statement-phase/EVIDENCE.md` — what was checked, and how, for the draft (historical).
* `statement-phase/evidence/` — build logs, axiom census, seal probes and controls, olean-tree
  snapshot and restore records, and the tools used.
* `statement-phase/evidence-r2/` — the round-2 statement evidence for `110c2f9d`.
* `gates/40-pairings-statements/` — the Gate 40 pack, dispatch prompt and findings.

The source PDFs ([Jou00], [BB04]) are not committed; their citations, versions and SHA-256 are
in the plan's § Sources.

## ===== briefs/pairings/gates/40-pairings-statements/integration-tip/PROVENANCE.txt (records, at b356e50b1b908b26c1379f2fa9e53d604dabfe41) =====

Verification build of the updated pairings PR #331 head merged onto the records tip (int-331-tip)
maintainer job, 2026-11-16 UTC
$SP = /tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad. Paths below are relative to this directory.
Rules: python3 -I throughout; Lean 4.25.0 cdd38ac5 (checks/lean-version.txt; PATH=$HOME/.elan/bin:$PATH). Every Lean run, including
  the Mathlib NthRootLemmas extra and the axioms probe, was a `bash scripts/lean_check_tree.sh <Module/Path>` call through
  tools-used/review/runner.py (G26-N1 count `^\S+\.lean:\d+:\d+: error[:(]`) with TCSLIB_OLEANS=$SP/dl-oleans. Only one of
  this job's Lean processes ran at a time. No lake command, no cache get. No commit, branch, checkout or push. Nothing was written
  under /home/user/tcslib; it was read only through `git rev-parse/diff/show/archive/hash-object/ls-tree`. dl-oleans-2 and
  wt-gate40 were not modified.
Head verified: 39d42e235a62b7085ffc19b01f371015c20d7795 (tree d77da415636c959e6626ac2287abdb7ebcaa6aff). Parents are #331's head
  70c1f44432a41bcdb6f6d8602d957d2fc68ce0da and the records tip 673a27158338437896c624df32bf5421c6ba45cf. It carries a gpgsig (SSH)
  header. That signature was not verified here because gpg.ssh.allowedSignersFile is not configured.
Source export: $SP/wt-i331tip = `git archive 39d42e23 -- TCSlib TCSlib.lean audits scripts lakefile.lean lake-manifest.json
  lean-toolchain`, plus .lake/packages -> /home/user/tcslib/.lake/packages. scripts/lean_check_tree.sh is byte-equal to
  /home/user/tcslib's copy. Removed at the end.
Method and tools: briefs/pass-shelat-ch5-8/maintainer/int-stmt-331-333-2026-11-16/int-stmt-331-333-evidence.zip (SHA-256
  9ffa41bbb1fb703bcd36ff15bc810a7ee09f3236445f81e1096eb63144617172). It was extracted to a fresh $SP/ev-i331tip and checked:
  1141/1141 OK against evidence-SHA256SUMS, path set exact, SHA256SUMS byte-equal. The extract was removed afterwards.
  tools-used/ holds unmodified copies of its tools-used/, plus one new tool, tools-used/fullorder.py (imports-first local closure
  of the roots). Probe source: axioms/AxiomsInt331Tip.lean.txt (`import TCSlib` + that job's `#admitted` DepTrace + 12 names).

git checks (checks/git-checks.txt):
  - `git diff 673a2715 39d42e23` touches exactly 13 files. They equal #331's own file set (merge-base 523d80d2 .. 70c1f444).
    The 11 non-facade files are blob-equal to 70c1f444.
  - The facade blobs equal resolved/: TCSlib.lean 124658fc8de755bcd1b4bc637d358cc984d3a789 and
    TCSlib/Cryptography/AdvancedEncryption.lean c1bc37f9a01e280205e9e850bd3955a1399ee309.
  - Code tree vs C4 cbfa9d85 (tree 26a68b89): audits/ e204e63c, TCSlib.lean, scripts/ and lake files are equal. TCSlib/ differs
    (66432452 vs 9fdaa525) in exactly 5 files, all M: AdvancedEncryption/IdentityBased/{Defs,BonehBoyen,BonehBoyenMachine}.lean
    and Pairing/{Group,Assumptions}.lean. In each of the 5, the C4 blob equals old #331 head 110c2f9d and the head blob equals new
    #331 head 70c1f444. These are exactly the code files changed between 110c2f9d and 70c1f444 (LE-gate40).

olean tree $SP/dl-oleans: pre tree/snapshot-pre.txt has 1230 files, 0 empty dirs, SHA-256
  457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f (the required value, byte-equal to int-stmt-331-333's pre). All
  1230 oleans match the base records (eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9, int-317).
order: order/order.txt is the closure of root TCSlib + audits/garg-ch1-3/Checks + audits/pass-shelat/Checks at the head. It has
  1299 modules and is identical as a set to downorder.py's order vs eff2dcd0 (order/down-vs-base/). 34 modules lie outside it
  (order/outside-closure.txt), and none of them has a snapshot olean.
plan (stateplan.py, state/state-init.json = snapshot keyed at eff2dcd0): build 661 (= downorder's down set exactly: 561 snapshot
  oleans to overwrite + 100 new), reuse 638. The 561 were copied to $SP/dl-i331tip-backup (tree/backed-up.txt, verified 561/561,
  all equal to snapshot-pre). Mathlib overlay: mloverlay.sh (3346 symlinks). NthRootLemmas (pinned mathlib 029db123, source
  b371bf48...) was copied byte-equal into the export and built through lean_check_tree.sh (build-mathlib-extra/): rc 0, olean
  c0a9cff04c67... = int-stmt-331-333's.

build (build/: results.jsonl, mods/*.log, per-module.tsv from permod.py, err_colon = `error:`, err_paren = `error(`), queue
  plan/queue.txt: 661/661 rc 0; error: 0; error( 0; substring "error" 0; 103 sorry warnings, 463 warnings; 08:58:39-10:38:55 UTC,
  6015 s, max RSS 4.51 GB. runner exit 0.
  #331 modules: Pairing/Assumptions 1 (T1 bdhAssumption_of_dbdhAssumption), BonehBoyenSecurity 2 (T2 bb1_sim_real, T3
  bb1_sim_random), BonehBoyenMachine 1 (T4 exists_bb1_distinguisher). The other 10, including Defs, BonehBoyen, Group, the facades
  and root TCSlib: 0 sorry, 0 warnings.
  First attempt (build-aborted-0858/): it was started as a tool-managed background task with a 2 h limit. I stopped it after 3
  modules (my own PIDs only) and relaunched it detached (run-build.sh, setsid nohup) with a fresh build/. The orphaned EXP check was
  killed before it wrote a record.
  state: `update` took 661 modules; `check` over the 1299-module order -> RESULT OK (state/statecheck.txt).

INCIDENT (disk full, about 08:59:50-09:00:25 UTC): during the lint step, a full `git archive` of tip and head (the briefs/ zips,
  about 2 GB) filled the volume. The export was deleted within seconds (2.3 GB free again). It broke the OTHER job's build on
  dl-oleans-2: its runner stopped at KarpLiptonSearchFamily with a 0-byte olean and an empty log. That was reported to the
  coordinator at once; I did not touch that job. Lint then used small `git archive -- TCSlib TCSlib.lean scripts` exports (66 MB).
  Own-build check:
  - checks/incident-window-check.txt: the 31 modules that started before 09:01:30 (08:58:39-09:01:16) all have rc 0 and non-empty
    oleans equal to their records.
  - They were rechecked after the build (build-recheck/, order checks/incident-recheck-order.txt): 31/31 rc 0, 0 errors in both
    forms. Every olean, log hash, sorry and warning count is identical to the first run (checks/incident-recheck-compare.txt,
    differing 0). Parity, which spanned the window, reproduced byte-for-byte.
  - Every state file and tree/*.txt was written before or after the window. snapshot-pre.txt still hashes to 457ba704.
  - The final whole-tree check verifies every olean against a successful (rc 0, same-source) record.

whole-tree check (tree-final/; treecheck_ml.py at 39d42e23 against order/order.txt and records/records-final.jsonl = base records
  (int-317) + build + build-recheck; run before the probe and the restore):
  - all 1299 modules rc 0 at the head source;
  - every olean equal to its record; none missing; no stray olean; no empty dir;
  - 4677 files = 1299 + 31 PFR + 3347 Mathlib overlay entries (3346 symlinks + NthRootLemmas);
  - RESULT OK.

admissions (admissions/census-{tip,head}.txt; tipcensus.py; record sets: base = int-317 base records, intall = int-all-open
  records-final, int331333 = int-stmt-331-333 records/records-final, this = build/results.jsonl; the first three come from the
  int-stmt-331-333 evidence zip; disagreeing 0):
  - tip 673a2715: 237 over 1288 modules.
  - head 39d42e23: 241 over 1299 modules, i.e. +4.
  - The census diff is only the 11 new #331 modules (Assumptions 1, BonehBoyenSecurity 2, BonehBoyenMachine 1, the other 8 at 0)
    plus record-set tags on the facades and root (0 at both). No other module changes its count.
  - The 34 modules outside root TCSlib's closure have no record at either rev, as before.

axioms (axioms/probe-run/: PlProbe/AxiomsInt331Tip via lean_check_tree.sh: rc 0, 0 errors, 0 warnings, 0 sorry. Its olean was
  written to PlProbe/ in the tree and deleted at restore, logged):
  - [propext, Classical.choice, Quot.sound], with no sorryAx user in the closure: bb1_correct (closure 8663), joux_correct (6837),
    jouxKeyIndist_of_dbdhAssumption (10289), bb1_encPP_inj (1530), bb1_encSK_inj (1526), bb1_encCT_inj (1531).
  - [propext, sorryAx, Classical.choice, Quot.sound], each its own closure's only direct sorryAx user:
    T1 Pairing.BilinearGen.bdhAssumption_of_dbdhAssumption (9582), T2 bb1_sim_real (10290), T3 bb1_sim_random (8324),
    T4 exists_bb1_distinguisher (8347).
  - bb1_sidSecure: [propext, sorryAx, Classical.choice, Quot.sound], inherited. The direct sorryAx users in its closure (14014)
    are exactly bb1_sim_random, bb1_sim_real and exists_bb1_distinguisher (T2-T4). T1 is not in it.
  - GSW.eval_encrypts: [propext, sorryAx, Classical.choice, Quot.sound]. It is its own closure's (5807) only direct sorryAx user,
    a pre-existing GSW statement-phase admission at the tip (#333, Eval.lean:184 `sorry`), unchanged by #331.

lint (lint/; `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography --check8b` run from TCSlib/TCSlib.lean/scripts exports
  of each rev, removed afterwards):
  - tip 673a2715: 92 FAIL / 101 WARN over 385 files.
  - head 39d42e23: 92 FAIL / 103 WARN over 396 files.
  - linediff-Cryptography-tip-vs-head.txt: only +2 lines, the known check-8 WARN false positives IdentityBased/Defs (SIDSecure)
    and Pairing/Assumptions (BDHAssumption, DBDHAssumption). No new FAIL.
  - The head's FAIL/WARN line set equals C4's (int-stmt-331-333 lint-Cryptography-b4).

restore (restore/; finish-restore.sh = tools-used/restore_derand.sh with a temporary `tools` symlink, removed, then restoreplan.py):
  - backup hash failures 0; 561 restored; 100 new oleans deleted; Mathlib overlay deleted (3346 symlinks + NthRootLemmas
    c0a9cff0, logged); probe olean PlProbe/AxiomsInt331Tip deleted (logged); 19 emptied dirs pruned.
  - tree/snapshot-post.txt: 1230 files, 0 empty dirs, SHA-256 457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f,
    byte-identical to snapshot-pre (SNAPSHOT EQUAL).
  - restoreplan (no --delete): extra 0, changed 0, missing 0.
  - A second independent snapshot (restore/snapshot-verify.txt/.out) also matches: 457ba704, equal.
  - The backup directory, the source export and the evidence extract were removed afterwards.
  (finish-restore.sh's console output was not saved because the tee target directory did not exist yet. Its results are in
  restore/restore-log.txt, tree/snapshot-post.txt, restore/restoreplan-check.out and restore/snapshot-verify.out.)
results.jsonl: every Lean run of this job in time order: build-mathlib-extra (1), build (661), build-recheck (31), probe (1),
  with done markers.
SHA256SUMS: every file here except itself (paths without "./"). ../int-331-tip-evidence.zip holds exactly these paths plus
  SHA256SUMS, under int-331-tip/.

## ===== blueprint/src/references/boneh-boyen-2004-selective-id-ibe.md (records, at b356e50b1b908b26c1379f2fa9e53d604dabfe41) =====

<!-- generated-by: maintainer transcription of the passages used (DW-7) -->
<!-- source-pdf-sha256: 63c1c7b0817f36d6e558107bf281e22d2c454f821fadd533ced653e81a6a35de -->
<!-- validation-status: scoped transcription for DW-7; awaiting Codex source review -->

# Efficient Selective-ID Secure Identity Based Encryption Without Random Oracles

Dan Boneh and Xavier Boyen. Cryptology ePrint Archive, Report 2004/172, full version dated
December 2004 (20 pages; tag `BB04`); extended abstract in *EUROCRYPT 2004*, LNCS 3027,
pp. 223–238. The ePrint numbering is used throughout.

**Scope.** Only the passages that the pairing campaign uses are transcribed (DW-7; pairing
ruling Q12): §2.1–§3.1 (IBE and HIBE, the selective-identity game, Definitions 2.1–2.2,
bilinear groups, BDH and Decision BDH, Definition 3.1), §4.1–§4.2 (the HIBE construction and
Theorem 4.1 with its proof) and §4.4 (arbitrary identities). The PDF is not committed. Physical
and printed pages coincide. The scoped raw extraction is
`boneh-boyen-2004-selective-id-ibe.raw.md`. Mathematics is set in LaTeX; the wording is the
paper's. Notes marked *Transcription note* are not part of the source.

<a id="pdf-63c1c7b0817f-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.95 -->

## 2 Preliminaries

**Section 2, opening (p. 2).** Before presenting our results we briefly review the definition
of security for an IBE system. We also review the definition of groups equipped with a
bilinear map.

<a id="pdf-63c1c7b0817f-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.95 -->

**Section 2.1, IBE and HIBE systems (pp. 2–3).** Recall that an Identity Based Encryption
system (IBE) consists of four algorithms [Sha84, BF01]: **Setup**, **KeyGen**, **Encrypt**,
**Decrypt**. The **Setup** algorithm generates system parameters, denoted by *params*, and a
master key *master-key*. The **KeyGen** algorithm uses the master key to generate the private
key corresponding to a given identity. The encryption algorithm encrypts messages for a given
identity (using the system parameters) and the decryption algorithm decrypts ciphertexts using
the private key. In a Hierarchical IBE [HL02, GS02] identities are vectors. A vector of
dimension $\ell$ represents an identity at depth $\ell$. Algorithm **KeyGen** takes as input
an identity $\mathrm{ID}=(I_1,\dots,I_\ell)$ at depth $\ell$ and the private key
$d_{\mathrm{ID}|_{\ell-1}}$ of the parent identity
$\mathrm{ID}|_{\ell-1}=(I_1,\dots,I_{\ell-1})$ at depth $\ell-1$. It outputs the private key
$d_{\mathrm{ID}}$ for identity $\mathrm{ID}$. We refer to the master-key as the private key at
depth $0$ and note that an IBE system is an HIBE where all identities are at depth $1$.

<a id="pdf-63c1c7b0817f-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.95 -->

**Section 2.1, the selective-identity game (p. 3).** Boneh and Franklin [BF01, BF03] define
chosen ciphertext security for IBE systems under a chosen identity attack. In their model the
adversary is allowed to adaptively chose the public key it wishes to attack (the public key on
which it will be challenged). Canetti, Halevi, and Katz [CHK03, CHK04] define a weaker notion of
security in which the adversary commits ahead of time to the public key it will attack. We
refer to this notion as *selective identity, chosen ciphertext secure IBE* (IND-sID-CCA). More
precisely, selective identity IBE and HIBE security is defined using the following game:

- **Init:** The adversary outputs an identity $\mathrm{ID}^*$ where it wishes to be
  challenged.
- **Setup:** The challenger runs the **Setup** algorithm. It gives the adversary the resulting
  system parameters *params*. It keeps the *master-key* to itself.
- **Phase 1:** The adversary issues queries $q_1,\dots,q_m$ where query $q_i$ is one of:
  - Private key query $\langle\mathrm{ID}_i\rangle$ where $\mathrm{ID}_i\neq\mathrm{ID}^*$ and
    $\mathrm{ID}_i$ is not a prefix of $\mathrm{ID}^*$. The challenger responds by running
    algorithm **KeyGen** to generate the private key $d_i$ corresponding to the public key
    $\langle\mathrm{ID}_i\rangle$. It sends $d_i$ to the adversary.
  - Decryption query $\langle C_i\rangle$ for identity $\mathrm{ID}^*$ or any prefix of
    $\mathrm{ID}^*$. The challenger responds by running algorithm **KeyGen** to generate the
    private key $d$ corresponding to $\mathrm{ID}^*$ (or the relevant prefix thereof as
    requested). It then runs algorithm **Decrypt** to decrypt the ciphertext $C_i$ using the
    private key $d$. It sends the resulting plaintext to the adversary.

  These queries may be asked adaptively, that is, each query $q_i$ may depend on the replies
  to $q_1,\dots,q_{i-1}$.
- **Challenge:** Once the adversary decides that Phase 1 is over it outputs two equal length
  plaintexts $M_0,M_1\in\mathcal M$ on which it wishes to be challenged. The challenger picks a
  random bit $b\in\{0,1\}$ and sets the challenge ciphertext to
  $C=\mathbf{Encrypt}(\textit{params},\mathrm{ID}^*,M_b)$. It sends $C$ as the challenge to
  the adversary.
- **Phase 2:** The adversary issues additional queries $q_{m+1},\dots,q_n$ where $q_i$ is one
  of:
  - Private key query $\langle\mathrm{ID}_i\rangle$ where $\mathrm{ID}_i\neq\mathrm{ID}^*$ and
    $\mathrm{ID}_i$ is not a prefix of $\mathrm{ID}^*$. The challenger responds as in Phase 1.
  - Decryption query $\langle C_i\rangle\neq\langle C\rangle$ for $\mathrm{ID}^*$ or any prefix
    of $\mathrm{ID}^*$. The challenger responds as in Phase 1.

  These queries may be asked adaptively as in Phase 1.
- **Guess:** Finally, the adversary outputs a guess $b'\in\{0,1\}$. The adversary wins if
  $b=b'$.

We refer to such an adversary $\mathcal A$ as an IND-sID-CCA adversary. We define the
advantage of the adversary $\mathcal A$ in attacking the scheme $\mathcal E$ as

$$
\mathrm{Adv}_{\mathcal E,\mathcal A}=\left|\Pr[b=b']-\frac12\right|
$$

The probability is over the random bits used by the challenger and the adversary.

*Transcription note.* The `-layout` extraction drops the vertical bars; the page image
(checked at 150 dpi) shows the absolute value $\left|\Pr[b=b']-\tfrac12\right|$.

<a id="pdf-63c1c7b0817f-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.95 -->

**Definition 2.1.** We say that an IBE or HIBE system $\mathcal E$ is
$(t,q_{ID},q_C,\epsilon)$-selective identity, adaptive chosen ciphertext secure if for any
$t$-time IND-sID-CCA adversary $\mathcal A$ that makes at most $q_{ID}$ chosen private key
queries and at most $q_C$ chosen decryption queries we have that
$\mathrm{Adv}_{\mathcal E,\mathcal A}<\epsilon$. As shorthand, we say that $\mathcal E$ is
$(t,q_{ID},q_C,\epsilon)$ IND-sID-CCA secure.

**Semantic Security.** As usual, we define selective identity, chosen plaintext security for
an IBE system as in the preceding game, except that the adversary is not allowed to issue any
decryption queries. The adversary may still issue adaptive private key queries.

<a id="pdf-63c1c7b0817f-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.95 -->

**Definition 2.2.** We say that an IBE or HIBE system $\mathcal E$ is
$(t,q_{ID},\epsilon)$-selective identity, chosen plaintext secure if $\mathcal E$ is
$(t,q_{ID},0,\epsilon)$-selective identity, chosen ciphertext secure. As shorthand, we say that
$\mathcal E$ is $(t,q_{ID},\epsilon)$ IND-sID-CPA secure.

<a id="pdf-63c1c7b0817f-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.95 -->

**Section 2.2, bilinear groups (p. 4).** We briefly review the necessary facts about bilinear
maps and bilinear map groups [Jou00, Mil04]. We use the following notation:

1. $\mathbb G$ and $\mathbb G_1$ are two (multiplicative) cyclic groups of prime order $p$;
2. $g$ is a generator of $\mathbb G$.
3. $e$ is a bilinear map $e:\mathbb G\times\mathbb G\to\mathbb G_1$.

Let $\mathbb G$ and $\mathbb G_1$ be two groups as above. A bilinear map is a map
$e:\mathbb G\times\mathbb G\to\mathbb G_1$ with the following properties:

1. Bilinearity: for all $u,v\in\mathbb G$ and $a,b\in\mathbb Z$, we have
   $e(u^a,v^b)=e(u,v)^{ab}$.
2. Non-degeneracy: $e(g,g)\neq 1$.

We say that $\mathbb G$ is a bilinear group if the group action in $\mathbb G$ can be computed
efficiently and there exists a group $\mathbb G_1$ and an efficiently computable bilinear map
$e:\mathbb G\times\mathbb G\to\mathbb G_1$ as above. Note that $e(\,,\,)$ is symmetric since
$e(g^a,g^b)=e(g,g)^{ab}=e(g^b,g^a)$.

Throughout the paper, for a prime order group $\mathbb G$ we use $\mathbb G^*$ to denote the set
$\mathbb G\setminus\{1_{\mathbb G}\}$ where $1_{\mathbb G}$ is the identity of $\mathbb G$.

<a id="pdf-63c1c7b0817f-p004-b004"></a>
<!-- pdf-source: page=4; block=4; confidence=0.95 -->

## 3 Complexity Assumptions

**Section 3 and Section 3.1, BDH and Decision BDH (pp. 4–5).** Let $\mathbb G$ be a bilinear
group of prime order $p$. We review the standard Bilinear Diffie-Hellman (BDH) assumption and
define the Bilinear Diffie-Hellman Inversion (BDHI) assumption.

The BDH problem [Jou00, SOK00, BF01] in $\mathbb G$ is as follows: given a tuple
$g,g^a,g^b,g^c\in\mathbb G$ as input, output $e(g,g)^{abc}\in\mathbb G_1$. An algorithm
$\mathcal A$ has advantage $\epsilon$ in solving BDH in $\mathbb G$ if

$$
\Pr\left[\mathcal A(g,g^a,g^b,g^c)=e(g,g)^{abc}\right]\ge\epsilon
$$

where the probability is over the random choice of generator $g$ in $\mathbb G^*$, the random
choice of $a,b,c$ in $\mathbb Z_p$, and the random bits used by $\mathcal A$. Similarly, we say
that an algorithm $\mathcal B$ that outputs $b\in\{0,1\}$ has advantage $\epsilon$ in solving
the *decision* BDH problem in $\mathbb G$ if

$$
\left|\Pr\left[\mathcal B(g,g^a,g^b,g^c,e(g,g)^{abc})=0\right]
-\Pr\left[\mathcal B(g,g^a,g^b,g^c,T)=0\right]\right|\ge\epsilon
$$

where the probability is over the random choice of generator $g$ in $\mathbb G^*$, the random
choice of $a,b,c$ in $\mathbb Z_p$, the random choice of $T\in\mathbb G_1$, and the random bits
consumed by $\mathcal B$. We refer to the distribution on the left as $\mathcal P_{\mathrm{BDH}}$
and the distribution on the right as $\mathcal R_{\mathrm{BDH}}$.

*Transcription note.* The `-layout` extraction drops the vertical bars, but the page image
(checked at 130 dpi) shows an absolute value around the difference, as transcribed. This
differs from `PairingCryptographyPlan.md` ("Where the papers' formulations differ", item 6),
which says the decision advantage of §3.1 is written without one; that record should be
corrected (the draft's choice is unaffected, since it takes the signed form as a deviation).

<a id="pdf-63c1c7b0817f-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.95 -->

**Definition 3.1.** We say that the (Decision) $(t,\epsilon)$-BDH assumption holds in
$\mathbb G$ if no $t$-time algorithm has advantage at least $\epsilon$ in solving the
(Decision) BDH problem in $\mathbb G$.

Occasionally we drop the $t$ and $\epsilon$ and refer to the BDH and Decision BDH assumptions in
$\mathbb G$.

<a id="pdf-63c1c7b0817f-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.95 -->

## 4 Efficient Selective Identity IBE and HIBE Based on BDH Without Random Oracles

**Section 4 and Section 4.1, opening (p. 5).** We construct an efficient HIBE system that is
selective identity secure without random oracles based on the Decision BDH assumption. In
particular, this implies an efficient selective identity, chosen ciphertext secure IBE based on
Decision BDH without random oracles.

Let $\mathbb G$ be a bilinear group of prime order $p$ (the security parameter determines the
size of $\mathbb G$). Let $e:\mathbb G\times\mathbb G\to\mathbb G_1$ be the bilinear map. For
now, we assume public keys (ID) of depth $\ell$ are vectors of elements in $\mathbb Z_p^{\ell}$.
We write $\mathrm{ID}=(I_1,\dots,I_\ell)\in\mathbb Z_p^{\ell}$. The $j$-th component
corresponds to the identity at level $j$. We later extend the construction to public keys over
$\{0,1\}^*$ by first hashing each component $I_j$ using a collision resistant hash
$H:\{0,1\}^*\to\mathbb Z_p$. We also assume messages to be encrypted are elements in
$\mathbb G_1$. The HIBE system works as follows:

<a id="pdf-63c1c7b0817f-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.95 -->

**Section 4.1, the HIBE construction (p. 6).**

**Setup**$(\ell)$: To generate system parameters for an HIBE of maximum depth $\ell$, select a
random generator $g$ in $\mathbb G^*$, a random $\alpha\in\mathbb Z_p$, and set
$g_1=g^{\alpha}$. Next, pick random elements $h_1,\dots,h_\ell\in\mathbb G$ and a random element
$g_2\in\mathbb G$. The public parameters *params* and the secret *master-key* are given by

$$
\textit{params}=(g,g_1,g_2,h_1,\dots,h_\ell),\qquad \textit{master-key}=g_2^{\alpha}
$$

For $j=1,\dots,\ell$, we define $F_j:\mathbb Z_p\to\mathbb G$ to be the function:
$F_j(x)=g_1^{x}h_j$.

**KeyGen**$(d_{\mathrm{ID}|_{j-1}},\mathrm{ID})$: To generate the private key
$d_{\mathrm{ID}}$ for an identity $\mathrm{ID}=(I_1,\dots,I_j)\in\mathbb Z_p^{j}$ of depth
$j\le\ell$, pick random $r_1,\dots,r_j\in\mathbb Z_p$ and output

$$
d_{\mathrm{ID}}=\left(g_2^{\alpha}\cdot\prod_{k=1}^{j}F_k(I_k)^{r_k},\ g^{r_1},\dots,g^{r_j}\right)
$$

Note that the private key for ID can be generated just given a private key for
$\mathrm{ID}|_{j-1}=(I_1,\dots,I_{j-1})\in\mathbb Z_p^{j-1}$, as required. Indeed, let
$d_{\mathrm{ID}|_{j-1}}=(d_0,\dots,d_{j-1})$ be the private key for $\mathrm{ID}|_{j-1}$. To
generate $d_{\mathrm{ID}}$ pick a random $r_j\in\mathbb Z_p$ and output
$d_{\mathrm{ID}}=(d_0\cdot F_j(I_j)^{r_j},d_1,\dots,d_{j-1},g^{r_j})$.

**Encrypt**$(\textit{params},\mathrm{ID},M)$: To encrypt a message $M\in\mathbb G_1$ under the
public key $\mathrm{ID}=(I_1,\dots,I_j)\in\mathbb Z_p^{j}$, pick a random $s\in\mathbb Z_p$ and
output

$$
C=\left(e(g_1,g_2)^{s}\cdot M,\ g^{s},\ F_1(I_1)^{s},\dots,F_j(I_j)^{s}\right)
$$

Note that $e(g_1,g_2)$ can be precomputed once and for all so that encryption does not require
any pairing computations. Alternatively, $e(g_1,g_2)$ can be included in the system
parameters, in which case $g_2$ can be dropped.

**Decrypt**$(d_{\mathrm{ID}},C)$: Consider an identity $\mathrm{ID}=(I_1,\dots,I_j)$. To decrypt
a given ciphertext $C=(A,B,C_1,\dots,C_j)$ using the private key
$d_{\mathrm{ID}}=(d_0,d_1,\dots,d_j)$, output

$$
A\cdot\frac{\prod_{k=1}^{j}e(C_k,d_k)}{e(B,d_0)}=M
$$

Indeed, for a valid ciphertext, we have

$$
\frac{\prod_{k=1}^{j}e(C_k,d_k)}{e(B,d_0)}
=\frac{\prod_{k=1}^{j}e(F_k(I_k),g)^{s r_k}}
{e(g,g_2)^{s\alpha}\prod_{k=1}^{j}e(g,F_k(I_k))^{s r_k}}
=\frac{1}{e(g_1,g_2)^{s}}
$$

<a id="pdf-63c1c7b0817f-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=0.95 -->

**Section 4.2, opening and Theorem 4.1 (p. 6).** The HIBE system above is reminiscent of the
Gentry-Silverberg HIBE which is only known to be secure in the random oracle model.
Surprisingly, our choice of functions $F_1,\dots,F_\ell$ enables us to prove security without
random oracles. We prove security of our HIBE system under the standard Decision BDH assumption
in $\mathbb G$.

**Theorem 4.1.** Suppose the $(t,\epsilon)$-Decision BDH assumption holds in $\mathbb G$. Then
the previously defined $\ell$-HIBE system is $(t',q_S,\epsilon)$-selective identity, chosen
plaintext (IND-sID-CPA) secure for arbitrary $\ell$ and $q_S$, and any
$t'<t-\Theta(\tau\,\ell\,q_S)$ where $\tau$ is the maximum time for an exponentiation in
$\mathbb G$.

<a id="pdf-63c1c7b0817f-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.95 -->

**Proof of Theorem 4.1, the simulator's setup (p. 7).** Suppose $\mathcal A$ has advantage
$\epsilon$ in attacking the HIBE system. We build an algorithm $\mathcal B$ that solves the
Decision BDH problem in $\mathbb G$. Algorithm $\mathcal B$ is given as input a random 5-tuple
$(g,g^a,g^b,g^c,T)$ that is either sampled from $\mathcal P_{\mathrm{BDH}}$ (where
$T=e(g,g)^{abc}$) or from $\mathcal R_{\mathrm{BDH}}$ (where $T$ is uniform and independent in
$\mathbb G_1$). Algorithm $\mathcal B$'s goal is to output $1$ if $T=e(g,g)^{abc}$ and $0$
otherwise. Set $g_1=g^a$, $g_2=g^b$, $g_3=g^c$. Algorithm $\mathcal B$ works by interacting
with $\mathcal A$ in a selective identity game as follows:

**Initialization.** The selective identity game begins with $\mathcal A$ first outputting an
identity $\mathrm{ID}^*=(I^*_1,\dots,I^*_k)\in\mathbb Z_p^{k}$ of depth $k\le\ell$ that it
intends to attack. If necessary, $\mathcal B$ appends random elements in $\mathbb Z_p$ to
$\mathrm{ID}^*$ so that $\mathrm{ID}^*$ is a vector of length $\ell$.

**Setup.** To generate the system parameters, algorithm $\mathcal B$ picks
$\alpha_1,\dots,\alpha_\ell\in\mathbb Z_p$ at random and defines
$h_j=g_1^{-I^*_j}g^{\alpha_j}\in\mathbb G$ for $j=1,\dots,\ell$. It gives $\mathcal A$ the
system parameters $\textit{params}=(g,g_1,g_2,h_1,\dots,h_\ell)$. Note that the corresponding
master key, which is unknown to $\mathcal B$, is $g_2^{a}=g^{ab}\in\mathbb G$. As before, for
$j=1,\dots,\ell$ we define $F_j:\mathbb Z_p\to\mathbb G$ to be the function

$$
F_j(x)=g_1^{x}h_j=g_1^{x-I^*_j}g^{\alpha_j}
$$

<a id="pdf-63c1c7b0817f-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.95 -->

**Proof of Theorem 4.1, Phase 1 (p. 7).** $\mathcal A$ issues up to $q_S$ private key queries.
Consider a query for the private key corresponding to
$\mathrm{ID}=(I_1,\dots,I_u)\in\mathbb Z_p^{u}$ where $u\le\ell$. The only restriction is that
ID is not a prefix of $\mathrm{ID}^*$. Let $j$ be the smallest index such that
$I_j\neq I^*_j$. Necessarily $1\le j\le u$. To respond to the query, algorithm $\mathcal B$
first derives a private key for the identity $(I_1,\dots,I_j)$ from which it then constructs a
private key for the requested identity $\mathrm{ID}=(I_1,\dots,I_j,\dots,I_u)$. Algorithm
$\mathcal B$ picks random elements $r_1,\dots,r_j\in\mathbb Z_p$ and sets

$$
d_0=g_2^{\frac{-\alpha_j}{I_j-I^*_j}}\prod_{v=1}^{j}F_v(I_v)^{r_v},\quad
d_1=g^{r_1},\quad\dots,\quad d_{j-1}=g^{r_{j-1}},\quad
d_j=g_2^{\frac{-1}{I_j-I^*_j}}g^{r_j}
$$

We claim that $(d_0,d_1,\dots,d_j)$ is a valid random private key for $(I_1,\dots,I_j)$. To
see this, let $\tilde r_j=r_j-b/(I_j-I^*_j)$. Then we have that

$$
g_2^{\frac{-\alpha_j}{I_j-I^*_j}}F_j(I_j)^{r_j}
=g_2^{\frac{-\alpha_j}{I_j-I^*_j}}\left(g_1^{I_j-I^*_j}g^{\alpha_j}\right)^{r_j}
=g_2^{a}\left(g_1^{I_j-I^*_j}g^{\alpha_j}\right)^{r_j-\frac{b}{I_j-I^*_j}}
=g_2^{a}F_j(I_j)^{\tilde r_j}
$$

It follows that the private key $(d_0,d_1,\dots,d_j)$ defined above satisfies

$$
d_0=g_2^{a}\cdot\Bigl(\prod_{v=1}^{j-1}F_v(I_v)^{r_v}\Bigr)\cdot F_j(I_j)^{\tilde r_j},\quad
d_1=g^{r_1},\ \dots,\ d_{j-1}=g^{r_{j-1}},\quad d_j=g^{\tilde r_j}
$$

where $r_1,\dots,r_{j-1},\tilde r_j$ are uniform in $\mathbb Z_p$. This matches the definition
for a private key for $(I_1,\dots,I_j)$. Hence, $(d_0,d_1,\dots,d_j)$ is a valid private key for
$(I_1,\dots,I_j)$. Algorithm $\mathcal B$ derives a private key for the requested ID from the
private key $(d_0,d_1,\dots,d_j)$ and gives $\mathcal A$ the result.

*Transcription note.* The exponents are stacked fractions in the PDF, flattened by the
extraction; they were read from the page image (150 dpi) as $-\alpha_j/(I_j-I^*_j)$ and
$-1/(I_j-I^*_j)$. The PDF sets identities in an upright font ($\mathrm I_j$); plain $I_j$ is
used here.

<a id="pdf-63c1c7b0817f-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.95 -->

**Proof of Theorem 4.1, Challenge (p. 7).** When $\mathcal A$ decides that Phase 1 is over, it
outputs two messages $M_0,M_1\in\mathbb G_1$ on which it wishes to be challenged. Algorithm
$\mathcal B$ picks a random bit $b\in\{0,1\}$ and responds with the ciphertext
$C=(M_b\cdot T,\ g_3,\ g_3^{\alpha_1},\dots,g_3^{\alpha_k})$. Since $F_i(I^*_i)=g^{\alpha_i}$ for
all $i$, we have that

$$
C=\left(M_b\cdot T,\ g^{c},\ F_1(I^*_1)^{c},\dots,F_k(I^*_k)^{c}\right)
$$

Hence, if $T=e(g,g)^{abc}=e(g_1,g_2)^{c}$ then $C$ is a valid encryption of $M_b$ under the
public key $\mathrm{ID}^*=(I^*_1,\dots,I^*_k)$. On the other hand, when $T$ is uniform and
independent in $\mathbb G_1$ (when the input 5-tuple is sampled from
$\mathcal R_{\mathrm{BDH}}$) then $C$ is independent of $b$ in the adversary's view.

<a id="pdf-63c1c7b0817f-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.95 -->

**Proof of Theorem 4.1, Phase 2, Guess and the advantage (p. 8).**

**Phase 2.** $\mathcal A$ continues to issue queries not issued in Phase 1. Algorithm
$\mathcal B$ responds as before.

**Guess.** Finally, $\mathcal A$ outputs a guess $b'\in\{0,1\}$. Algorithm $\mathcal B$
concludes its own game by outputting a guess as follows. If $b=b'$ then $\mathcal B$ outputs
$1$ meaning $T=e(g,g)^{abc}$. Otherwise, it outputs $0$ meaning $T\neq e(g,g)^{abc}$.

When the input 5-tuple is sampled from $\mathcal P_{\mathrm{BDH}}$ (where
$T=e(g,g)^{abc}$) then $\mathcal A$'s view is identical to its view in a real attack game and
therefore $\mathcal A$ must satisfy $\left|\Pr[b=b']-1/2\right|>\epsilon$. On the other hand,
when the input 5-tuple is sampled from $\mathcal R_{\mathrm{BDH}}$ (where $T$ is uniform in
$\mathbb G_1$) then $\Pr[b=b']=1/2$. Therefore, with $g$ uniform in $\mathbb G^*$, $a,b,c$
uniform in $\mathbb Z_p$, and $T$ uniform in $\mathbb G_1$ we have that

$$
\left|\Pr\left[\mathcal B(g,g^a,g^b,g^c,e(g,g)^{abc})=0\right]
-\Pr\left[\mathcal B(g,g^a,g^b,g^c,T)=0\right]\right|
\ge\left|\left(\frac12\pm\epsilon\right)-\frac12\right|=\epsilon
$$

as required. This completes the proof of Theorem 4.1.

*Transcription note.* The page image (150 dpi) shows absolute-value bars on both sides, as
transcribed.

<a id="pdf-63c1c7b0817f-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.95 -->

**Section 4.4, arbitrary identities (p. 8).** We can extend our HIBE above to handle identities
$\mathrm{ID}=(I_1,\dots,I_\ell)$ with $I_j\in\{0,1\}^*$ (as opposed to $I_j\in\mathbb Z_p$) by
first hashing each $I_j$ using a collision resistant hash function $H:\{0,1\}^*\to\mathbb Z_p$
prior to key generation and encryption. A standard argument shows that if the scheme above is
selective identity, chosen ciphertext secure then so is the scheme with the additional hash
function. We note that there is no need for a full domain hash into $\mathbb Z_p$; for example,
a collision resistant hash function $H:\{0,1\}^*\to\{1,\dots,2^b\}$ where $2^b<p$ is sufficient
for the security proof.

## ===== PairingCryptographyPlan.md (records, at b356e50b1b908b26c1379f2fa9e53d604dabfe41) =====

# Pairing-based cryptography

## Scope and ownership

Seyoon approved this campaign on 2026-11-16 (decision log, first row):

1. **Abstract bilinear groups.** A symmetric bilinear group generator in the existing asymptotic
   and NUPPT framework, with the BDH and Decision BDH (DBDH) assumptions. No concrete curves.
2. **Joux's one-round tripartite Diffie–Hellman** [Jou00]: the protocol, its correctness (the
   three parties derive the same key) and its key indistinguishability under DBDH.
3. **Boneh–Boyen selective-ID IBE (BB1)** [BB04], standard model: IND-sID-CPA security, the
   scheme, its correctness, and security from DBDH.

**Out of scope:** Boneh–Franklin IBE (it needs a random-oracle layer), asymmetric (Type-3)
pairings, concrete groups. BB04's BDHI-based system (BB2, §5), its HIBE at depth > 1, its CCA2
transforms (§4.3, §6) and its full-security transform (§7) are not targets.

**Location (Seyoon, 2026-11-16).** The bilinear-group substrate is `TCSlib/Cryptography/Pairing/`
and Joux is `TCSlib/Cryptography/KeyExchange/`. IBE (interface, IND-sID-CPA game, Boneh–Boyen)
is `TCSlib/Cryptography/AdvancedEncryption/IdentityBased/`, namespace
`TCSlib.Cryptography.AdvancedEncryption.IdentityBased`, behind the facades
`AdvancedEncryption.lean` and `AdvancedEncryption/IdentityBased.lean`. `AdvancedEncryption.lean`
is shared with GSW (`AdvancedEncryption/Homomorphic/`): the draft's facade imports only
`IdentityBased`, and **whichever statement PR lands second adds its child import** to it.

**Home and binding rules.** Records (this file, `briefs/pairings/`) live on the records branch
`cryptography/pass-shelat-ch2-4` and are pushed by the maintainer. Lean reaches that branch only
by PR, opened by the maintainer and merged by Seyoon. Binding: `policy.md` (modularity,
attribution, proof sketches, Rule 10, hosts first), `briefs/pass-shelat-ch5-8/CLAUDE.md` and
`MAINTAINER-HANDOFF.md` §2. Standing worker ruling (2026-11-11): Codex for audits and reviews,
Claude for fills and other external jobs.

| Item | Identity |
|---|---|
| Statement branch (local, not pushed) | `stmt/pairings` |
| Statement worktree | `$SP/wt-stmt-pairings` (sparse, `briefs/` excluded; `.lake/packages` symlinked) |
| Branch base (`origin/cryptography/pass-shelat-ch2-4` when cut) | `e7a9f70f5c1f11c2670f427ef813f2a6d8c53543` |
| Statement commit (modules) | `b02e6ce4a3dcc7c945825d1f1d3b636c5e377a01` |
| Statement head (root exports) | `ce9c3728ec582be45fc33ca68d64b5533701093d`, tree `327612ee0b6689bf371a40e28edaad984226d78e` |
| Records tip checked at commit time | `44e2dc2bd68b3a81eaeebe7acd61fca1fe857917` (records only since the base: no `TCSlib/`, root, lakefile or manifest change) |
| Lean / Mathlib | `leanprover/lean4:v4.25.0` / the pinned manifest |

`$SP` = `/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`.

## Sources

| Tag | Reference | Version used | SHA-256 | Committed? |
|---|---|---|---|---|
| Jou00 | A. Joux, *A One Round Protocol for Tripartite Diffie–Hellman*, ANTS-IV, W. Bosma (ed.), LNCS 1838, pp. 385–393, Springer, 2000 | Publisher copy, 9 pp. (Seyoon's upload) | `dd423b93a7e2dbeb87e6210b26f4c3ec022c3d0681a0ce72262b1d45c53f6df9` | No (publisher copy; PSV06/PSV07 precedent) |
| BB04 | D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without Random Oracles*, Cryptology ePrint Archive, Report 2004/172, full version dated December 2004; extended abstract in EUROCRYPT 2004, LNCS 3027, pp. 223–238 | ePrint full version, 20 pp.; **its numbering is used throughout** | `63c1c7b0817f36d6e558107bf281e22d2c454f821fadd533ced653e81a6a35de` | No (ePrint copy; same precedent) |
| PS10 | R. Pass, a. shelat, *A Course in Cryptography*, 3rd ed., 2010 | `Pass–Shelat.pdf` on this branch | `7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8` | Yes (existing) |

Both PDFs were read with `pdftotext -layout` (text treated as data). **PDF needed:** both are in
hand; nothing further is needed for the statement phase. **Policy §2 ingest** (reference pair
under `blueprint/src/references/`, `scripts/sources.py add`) is **open**: the PDFs themselves must
not be committed, so the ingest needs a ruling on what is committed instead (Q12).

Anchors used in the Lean (BB04 ePrint pages): §2.1 pp. 2–4 (IBE algorithms; the selective-identity
game; Definitions 2.1, 2.2), §2.2 p. 4 (bilinear groups), §3.1 pp. 4–5 (BDH, Decision BDH,
Definition 3.1), §4.1 pp. 5–6 (the HIBE construction; BB1 is depth 1), §4.2 pp. 6–8 (Theorem 4.1
and its proof), §4.4 p. 8 (arbitrary identities, "`2^b < p` is sufficient"). Jou00: §2 pp. 386–387
(pairings bilinear and non-degenerate), §3 pp. 387–388 (the protocol, `F_W`, `F_T`), §5 pp. 391–392
(security issues).

### Where the papers' formulations differ from the draft

1. **[Jou00] has no security theorem.** §5 says only that "some Diffie–Hellman like problem and
   Diffie–Hellman like decision problem should be hard in order to get security". The draft's
   `jouxKeyIndist_of_dbdhAssumption` is the maintainer's formal version, with Decision BDH taken
   from [BB04, §3.1] (which credits the BDH problem to [Jou00, SOK00, BF01]).
2. **[Jou00]'s protocol uses two points.** With the Weil pairing on one point `e_n(P, P) = 1`, so
   §3 moves to two independent points `P, Q` and the Tate pairing `F_T`. In a symmetric bilinear
   group as defined in [BB04, §2.2], non-degeneracy is `e(g, g) ≠ 1`, so the paper's first formula
   `F_W(x, P, Q) = e(P, Q)^x` works with one point. The draft formalizes that single-point form.
3. **[Jou00] fixes "some point `P`"**; the draft draws the public generator uniformly from `G^*`,
   the distribution under which [BB04, §3.1] states Decision BDH.
4. **[BB04, §4.1] is an HIBE**; BB1 is its depth-1 case ("an IBE system is an HIBE where all
   identities are at depth 1", §2.1). Identities are elements of `Z_p` there; arbitrary identities
   are hashed (§4.4). The draft uses `ℓ(κ)`-bit identities read as their binary value in `Z_p`,
   which is §4.4's sufficient condition (`H : {0,1}^* → {1, …, 2^b}`, `2^b < p`) with `H` the
   identity on `ℓ`-bit strings, under the hypothesis that `p ≥ 2^ℓ` except with negligible
   probability.
5. **[BB04] is concrete** (`(t, ε)` assumptions in a fixed group; Theorem 4.1's
   `t' < t − Θ(τ ℓ q_S)`). The draft is asymptotic, relative to a PPT generator, against
   non-uniform PPT machines.
6. **Advantage.** [BB04, §2.1] measures `|Pr[b = b'] − 1/2|`; the draft uses the two-experiment
   advantage, twice that, as `FixedLengthPKScheme.INDSecure` does. The decision advantage of
   [BB04, §3.1] is written without an absolute value; the draft takes it.
7. **Forbidden queries.** [BB04, §2.1] restricts the adversary (`ID_i ≠ ID*`, `M_0, M_1 ∈ M`);
   the draft's challenger answers such queries with `⊥`.
8. **The proof of Theorem 4.1** has `B` draw the challenge bit and output `[b = b']`; the draft
   fixes the bit and uses one distinguisher per bit, so the bound is a sum of two DBDH advantages.
9. **DBDH ⇒ BDH** is not stated in either source (folklore; Q10).

## Design decisions (and the precedent each mirrors)

### D1. Abstract bundle, generator as a PPT with a total group map

`Pairing.BilinearGroup wG wT` bundles finite commutative groups `G`, `GT` of the same prime order,
a generator `gen ≠ 1`, the pairing as `G →* G →* GT` (bimultiplicative; BB04's
`e(u^a, v^b) = e(u, v)^{ab}` is the proved `bilinear_pow`), non-degeneracy `e(gen, gen) ≠ 1`, and
injective fixed-width encodings `encG`, `encT`. `Pairing.BilinearGen` is a uniform `NUPPT`
`Gen(1^κ)` with exact description length `descLen(κ)`, element widths `wG`, `wT : PolyExpr`, and a
total map `group κ d` from descriptions to bundles.

*Precedent:* `Candidates.ExpGroupGen`/`SafePrimeGen` (an instance generator PPT; adversaries
receive the instance). *Difference:* no validity predicate or threshold `n₀`: every string
describes a group, so no fallback instance (`dlDefaultIndex`) is needed. The large-order condition
is `OrderAtLeastExcept N δ` (probability over the generator's coins), mirroring
`ExpGroupGen.FullLengthExcept` and its run-3 audit P8-2 lesson.

### D2. Experiments as games, sampled in sequence

All experiments are `Games.ProbComp Bool`: generator coins, then `g ∈ G^*`, exponents and `T`
from the group just drawn, then the adversary's coins; advantages are `Games.advantage`.
Exponents are ideal uniform in `Z_p`. *Precedent:* the run-3 audit P8-1 repair of the DDH
ensembles (a uniform seed over a dependent sum distorts the instance law); `dlProb`'s ideal
exponent; LWE's ideal experiments. Sequential sampling avoids P8-1 without coin blocks.

### D3. Adversary input format

A DBDH distinguisher gets `1^κ` and `⟨d, ⟨g, ⟨g^a, ⟨g^b, ⟨g^c, T⟩⟩⟩⟩⟩` (`tupleStr`); a BDH
solver gets the same without `T` (`bdhStr`) and wins iff its output is the encoding of
`e(g, g)^{abc}`. Joux's eavesdropper gets the transcript in the same format, so the Joux
experiments *are* DBDH experiments (`jouxGame_eq_dbdhGame`, proved). *Precedent:* `ddhTuple`'s
nested pairs; `distinguisherL`; `DLWEAssumption`'s "every `NUPPT` has negligible advantage".

### D4. Efficiency as a separate contract

"Efficiently computable" [BB04, §2.2] is `BilinearGen.Ops` (`Pairing/Operations.lean`):
polynomial-time string functions for the order, `G` multiplication and exponentiation by a
numeral, the pairing, `G_T` multiplication and `G_T` membership, specified on generated
descriptions, with numerals read by `NumberTheory.listToNat`. It is a hypothesis only of BB1's
security (whose reduction computes in the group), together with `Candidates.ArithmeticFP` (D11).
*Precedent:* `ArithmeticFP` as a hypothesis bundle; LWE's "`Family` asserts no efficient sampler".

### D5. IBE interface: typed probabilistic algorithms

`IdentityBased.IBEScheme` has, per `κ`, types `PP`, `MSK`, `SK`, `CT`; `setup`, `keyGen`, `enc`
as `ProbComp`s, `dec` deterministic with `⊥`; `idLen`- and `msgLen`-bit identities and messages;
a parameter-dependent message space `MsgSpace` (BB04's `M`); fixed-width encodings for the
adversary. Correctness is `AllOutputs` of an honest run. *Precedent:* the four-algorithm shape of
`PublicKeyScheme` and `GroupPKScheme` (key-dependent message space, El Gamal). *Difference:* the
algorithms are typed `ProbComp`s, not `NUPPT`s, and carry no efficiency field (Q5): with groups
drawn per description, an `NUPPT` interface would require proving BB1's machines PPT in a
definition (no `sorry` in definitions).

### D6. The IND-sID-CPA game: one machine, `Init` as an oracle

As in `FixedLengthPKScheme.indGame`: one `NUPPT` against bit-string oracles (`bitCodec`), budget
`q`, verdict bit. Oracles: `Init` (0; first query fixes `ID*`, answers `params`), `KeyGen` (1;
`⊥` before `Init` or for `ID*`, fresh coins per query), `Challenge` (2; `⊥` before `Init` or on
messages outside `M`; first valid query encrypts `M_b` for `ID*` and is recorded; later queries
repeat it). The machine starts with `1^κ` only, so it learns nothing about `params` before
committing; `Setup` is sampled before the run but revealed only at `Init`, which is [BB04, §2.1]'s
order in distribution. `SIDSecure` copies `INDSecure`'s quantifier shape. `oracleImpl` builds the
three oracles from typed handlers so that simulators in other files never read `inLens`/`outLens`
through their bodies (Rule 10).

### D7. BB1 over the generator

`bb1Scheme G ℓ` tags parameters, keys and ciphertexts with the description (`Σ d, …`); `dec` is
`⊥` on mismatched descriptions. Over one group, `BB1.setup/keyGen/encrypt/decrypt` follow
[BB04, §4.1] at depth 1, including the order of `Setup`'s samples (`g`, `α`, `h`, `g_2`) and a
random generator `g ∈ G^*`. Messages are `G_T` encodings (`decodeT` reads `1` off the message
space; never exercised, the game refuses).

### D8. The security proof as named steps

The paper's simulator `B` is defined beside the scheme as typed handlers (`bb1SimInit`,
`bb1SimKeyQ`, `bb1SimChal`, `bb1SimImpl`, `bb1SimGame`) with ideal exponents. The headline
`bb1_sidSecure` is **proved** by the triangle inequality from three sorried steps: perfect
simulation on `P_BDH` up to identity collisions (`bb1_sim_real`), bit-independence on `R_BDH`
(`bb1_sim_random`), and the machine step (`exists_bb1_distinguisher`). *Precedent:* Gate 12's
`exists_adaptive_cpa` proved from sorried statements.

## Module layout (statement draft)

| Module | Lines | Content |
|---|---|---|
| `Pairing/Group.lean` | 299 | `BilinearGroup`, `BilinearGen`, `desc`, `inst`, `OrderAtLeastExcept`; group facts |
| `Pairing/Assumptions.lean` | 221 | `tupleStr`, `bdhStr`, `dbdhGame`, `dbdhAdv`, `DBDHAssumption`, `bdhGame`, `BDHAssumption`; T1 |
| `Pairing/Operations.lean` | 117 | `BilinearGen.Ops` |
| `Pairing.lean` (facade) | 31 | |
| `KeyExchange/Joux.lean` | 193 | protocol, correctness, key indistinguishability (all proved) |
| `KeyExchange.lean` (facade) | 23 | |
| `AdvancedEncryption/IdentityBased/Defs.lean` | 408 | `IBEScheme`, `Correct`, IND-sID-CPA game, `oracleImpl` |
| `AdvancedEncryption/IdentityBased/BonehBoyen.lean` | 553 | BB1, `bb1Scheme`, correctness (proved), the simulator |
| `AdvancedEncryption/IdentityBased/BonehBoyenMachine.lean` | 78 | T4 (Q11: its own module) |
| `AdvancedEncryption/IdentityBased/BonehBoyenSecurity.lean` | 170 | T2, T3 and `bb1_sidSecure` |
| `AdvancedEncryption/IdentityBased.lean`, `AdvancedEncryption.lean` (facades) | 32, 25 | |
| `TCSlib.lean` | +3 imports | separate commit |

Every file is under 1000 lines and no line exceeds 100 characters. Layout deviation from the
initial proposal: `Operations.lean` (keeps `Group.lean` free of the arithmetic layer's imports)
and `BonehBoyenSecurity.lean` (definitions separate from the heavyweight theorem file, policy §1);
`BonehBoyenMachine.lean` (T4 alone, so that its fill unit owns its own file; ruling Q11).

## Statements

Proof sizes are estimates for the remaining targets.

| Statement | Source | Status | Est. size |
|---|---|---|---|
| `BilinearGroup.bilinear_pow`, `pair_pow_left`, `pair_pow_right` | BB04 §2.2 item 1 | proved | — |
| `BilinearGroup.pair_comm` | BB04 §2.2, remark after item 2 | proved | — |
| `BilinearGroup.exists_pow_eq`, `pow_order(_GT)`, `pow_val_mul(_GT)` | group facts | proved | — |
| `BilinearGroup.pair_ne_one` (`e(x, x) ≠ 1` on `G^*`) | BB04 §2.2 item 2 | proved | — |
| `BilinearGroup.pow_val_bijective` (`a ↦ e(x, x)^a` bijective) | BB04 §3.1 ("`T` uniform") | proved | — |
| **T1** `BilinearGen.bdhAssumption_of_dbdhAssumption` | folklore (Q10) | **sorry** | 150–300 |
| `jouxKey_eq`, `joux_correct` | Jou00 p. 388 | proved | — |
| `jouxGame_eq_dbdhGame`, `jouxKeyIndist_of_dbdhAssumption` | Jou00 §5 + BB04 §3.1 | proved | — |
| `IBEScheme.sidImpl_*` (9), `oracleImpl_*` (3), readers | BB04 §2.1 | proved | — |
| `BB1.decrypt_encrypt` | BB04 §4.1 ("for a valid ciphertext") | proved | — |
| `BB1.decodeT_encT` | — | proved | — |
| `bb1_correct` | BB04 §4.1 | proved | — |
| `bb1Sim*` case lemmas (9) | BB04 §4.2 proof | proved | — |
| **T2** `bb1_sim_real` | BB04 §4.2, proof of Thm 4.1 (P_BDH case) | **sorry** | 400–800 |
| **T3** `bb1_sim_random` | BB04 §4.2, proof of Thm 4.1 (R_BDH case) | **sorry** | 150–350 |
| **T4** `exists_bb1_distinguisher` | BB04 §4.2 (B is efficient) | **sorry** | 700–1400 |
| `bb1_sidSecure` | BB04 Theorem 4.1 at depth 1 | proved from T2–T4 | — |

Definitions (all complete, each with a reader): `BilinearGroup`, `BilinearGen`, `desc`, `inst`,
`OrderAtLeastExcept`, `tupleStr`, `bdhStr`, `dbdhGame`, `dbdhAdv`, `DBDHAssumption`, `bdhGame`,
`BDHAssumption`, `Ops`, `jouxMsg`, `jouxKey`, `jouxGame`, `jouxAdv`, `JouxKeyIndist`, `IBEScheme`,
`honestRun`, `Correct`, `inLens`, `outLens`, `sidSpec`, `SidState`, `sidImpl`, `oracleImpl`,
`sidCodec`, `sidGame`, `SIDSecure`, `BB1.{Params,Key,Ciphertext,F,setup,keyGen,encrypt,decrypt,
idToZ,decodeT}`, `bb1Scheme` (simps field equations, non-simp), `BB1SimState`, `bb1SimParams`,
`bb1SimKey`, `bb1SimInit`, `bb1SimKeyQ`, `bb1SimCt`, `bb1SimChal`, `bb1SimImpl`, `bb1SimGame`.
Instances: `BilinearGroup.factPrime`, `neZeroOrder`, `nonempty_ne_one` and the bundle's field
instances. No `@[simp]`. Abbrevs: `sidSpec`, `SidState`, `BB1SimState` (each with `_eq`).

Every target carries a `**Proof sketch.**` following the paper. The draft also *proves* the Joux
results and BB1 correctness; the statement gate audits those proofs too.

## Unit split for fills

Each unit owns its target's file; helper modules are allowed beside it.

| Unit | Targets | Files | Notes |
|---|---|---|---|
| `pair-bdh` | T1 | `Pairing/Assumptions.lean` | machine composition (`NUPPT` re-pairing and a string-equality test), a `1/p` bound and `OrderAtLeastExcept` |
| `bb1-sim` | T2, T3 | `IdentityBased/BonehBoyenSecurity.lean` | typed coupling of two `simulate` runs (state relation), re-randomization of `h` and `r`, lazy sampling of `T` (`Games.Hopping` eager/lazy lemmas) |
| `bb1-machine` | T4 | `IdentityBased/BonehBoyenMachine.lean` | handler theorem T1 (`Games.exists_handlerMachine`), `Ops`, `ArithmeticFP`, exponent sampling with `Candidates.sampleBelowL` and `statClose_sampleBelowL` |

T2/T3 and T4 are independent statements. T4 is in its own module (Q11, applied on
`stmt/pairings`), so `bb1-sim` and `bb1-machine` own disjoint files and can run in parallel;
`BonehBoyenSecurity` imports `BonehBoyenMachine` for `bb1_sidSecure` (proved-modulo rule).

## Modelling choices for the statement gate

1. The pairing is the field `pair : G →* G →* GT` of a bundle; bilinearity and non-degeneracy
   are fields (non-degeneracy at the bundle's `gen`; `pair_ne_one` extends it to `G^*`).
2. Groups are drawn by a uniform `NUPPT` generator; the group is a total function of the
   description; descriptions have exact polynomial length.
3. Elements are fixed-width injective encodings; decoding of adversary strings is
   `Function.partialInv` (`decodeT`), with membership as the message-space predicate.
4. The generator `g` is uniform in `G^*` in DBDH, BDH, Joux and BB1's `Setup`.
5. Exponents are `ZMod p` and act by `x ^ a.val`; `T` in `R_BDH` and Joux's random key are uniform
   in `G_T`.
6. Large order is `OrderAtLeastExcept N δ` with negligible `δ` (DBDH ⇒ BDH: `N = 2^κ`; BB1:
   `N = 2^ℓ`).
7. Efficiency of group operations is the separate contract `Ops`; honest IBE algorithms carry no
   efficiency requirement.
8. Identities are `ℓ(κ)`-bit strings, embedded in `Z_p` by binary value (BB04 §4.4).
9. Messages are `G_T` encodings; the message space is "is an encoding".
10. Selective-ID shape: one machine, `Init` oracle, `Setup` sampled first and revealed at `Init`,
    forbidden queries answered `⊥`, one polynomial budget for all queries.
11. Advantage: two experiments (twice BB04's guess advantage).
12. Parameters, keys and ciphertexts carry the description `d`; `dec` is `⊥` across descriptions.
13. Joux: single-point `F_W` form; security is the maintainer's formalization of Jou00 §5.

## Questions for Seyoon (recommended option first)

- **Q1. Group model.** (A) Abstract bundle drawn by a PPT generator with a total description map
  (current). (B) A fixed group per `κ` (no generator randomness; simpler types, the non-uniform
  reading of BB04's fixed `G`). (C) Abstract bundle with a validity predicate and threshold, as
  `ExpGroupGen`.
- **Q2. The generator `g`.** (A) Uniform in `G^*` everywhere (BB04 §3.1, §4.1; current). (B) The
  bundle's fixed `gen` everywhere (modern "generator outputs `g`" convention).
- **Q3. Joux's protocol.** (A) Single-point `F_W(x, P, Q) = e(P, Q)^x` over the symmetric bundle
  (current). (B) Joux's two-point form `(P_X, Q_X)` with an abstract pairing allowing
  `e(P, P) = 1`.
- **Q4. Joux's security.** (A) Key indistinguishability under DBDH only (current, proved). (B)
  Also the computational form: the key is hard to compute under BDH. (C) Correctness only.
- **Q5. Efficiency of honest algorithms.** (A) Typed algorithms without an efficiency field; the
  generator's `Ops` only where a reduction needs it; a BB1-is-PPT statement deferred (current).
  (B) Add a string-level `IBEScheme.Efficient` predicate now, with a BB1 efficiency target under
  `Ops` and `ArithmeticFP` (one more unit, machine-heavy). (C) An `NUPPT`-based IBE interface like
  `FixedLengthPKScheme`.
- **Q6. Identities.** (A) `ℓ(κ)`-bit strings by binary value with `p ≥ 2^ℓ` except negligibly
  (BB04 §4.4; current). (B) Identities as elements of `Z_p` in a BB1-specific game. (C) Arbitrary
  identities hashed by a CRH from `Hashing.CollisionResistant`.
- **Q7. Game shape.** (A) One machine with an `Init` oracle (current; mirrors the PK games). (B)
  A two-stage adversary `A₁(1^κ) → (ID*, st)`, `A₂(st, params)` with shared coins.
- **Q8. Messages outside `M`.** (A) The challenge is refused (`⊥`; BB04's "`M_0, M_1 ∈ M`";
  current). (B) Canonicalized to `1`, as El Gamal's `egCanon`.
- **Q9. Advantage.** (A) Two-experiment form, as `INDSecure` (current). (B) Guess-the-bit form
  (`Games.guessAdv`), BB04's literal `|Pr[b = b'] − 1/2|`.
- **Q10. DBDH ⇒ BDH.** (A) Keep T1 as a target, flagged "not in the sources" (current). (B) Drop
  it; BDH stays a definition with its reader.
- **Q11. Fill units.** (A) Three units `pair-bdh`, `bb1-sim`, `bb1-machine`, moving T4 to its own
  module (`IdentityBased/BonehBoyenReduction.lean`) at the statement PR so the two BB1 units run
  in parallel. (B) The same three units, with `bb1-machine` after `bb1-sim` on one file. (C) One
  BB1 unit for T2–T4.
- **Q12. Source ingest (policy §2).** (A) Keep the PDFs uncommitted; ingest later from Markdown
  transcriptions of the consumed passages only (BB04 §2.1–§4.4, Jou00 §3 and §5), as the LWE
  campaign's scoped review. (B) Commit full Markdown transcriptions now. (C) No ingest; the
  docstring tags suffice for this campaign.
- **Q13. Efficiency contract `Ops`.** (A) As drafted: order, `mulG`, `powG`, `pairStr`, `mulT`,
  `memT`, numerals by `listToNat`, specified at generated descriptions. (B) Only what BB1's
  reduction uses (drop `pairStr`). (C) Add `invG`, `powT`, `memG` for future consumers.

## Risks

- **T4 is the largest job**: a polynomial-time handler with group operations through `Ops`,
  modular arithmetic through `ArithmeticFP` (inverse of `ID − ID*`), exponent sampling from coin
  blocks with a statistical hybrid over `q + 1` samples, and T1's state and length bounds.
- **T2 needs a relational simulation argument** (two `simulate` runs with different states and
  re-randomized coins). If `Games.Hopping` lacks a state-relation coupling lemma, the fill should
  request it as a shared lemma rather than proving a private one (policy §1, duplication).
- **Dependent types.** Groups depend on the description; consumers outside `BonehBoyen.lean` must
  move between `(bb1Scheme G ℓ).sidSpec κ` and typed handlers through `oracleImpl_*` and cast
  readers; fills may need `_onSpec` reader variants (as in `OracleSecurity`).
- **Typed honest algorithms** (Q5) may draw an audit finding if the gate expects PPT schemes.
- **Order hypotheses** (`OrderAtLeastExcept`) are assumptions about the generator; whether a given
  generator satisfies them is not formalized (as for `FullLengthExcept`).
- **Root not elaborated.** The three facades and every new module are checked; the library root
  `TCSlib` is not (it needs the whole library on the tree).
- **Shared facade.** `AdvancedEncryption.lean` will conflict with the GSW statement PR on one
  import line; the second PR to land adds its child.

## Verification (statement draft)

Evidence: `briefs/pairings/statement-phase/evidence/` (summary in `EVIDENCE.md` there).

- **Tree.** `$SP/dl-oleans-2` only. Snapshot before: 1230 files, SHA-256
  `457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f` (the required value).
- **Base delta.** The tree holds the `eff2dcd0` sources. In the new modules' import closure (73
  modules at the base `e7a9f70f`), only `Foundations/BitLists` changed since (13 added lines). It
  and its 7 downstream closure modules (`Asymptotic/Adversary`, `Games/BitCodec`,
  `Encryption/PrivateKey/{Scheme,OracleSecurity}`, `Asymptotic/CollectionsHelpers`,
  `NumberTheory/Primality`, `Candidates/Arithmetic`) were backed up (hashes equal to the
  snapshot) and rebuilt at the base source: 8/8 rc 0.
- **Checks.** `scripts/lean_check_tree.sh`, one process at a time, final sweep of all 11 new
  modules in order: 11/11 rc 0, 0 errors, warnings only the 4 target `sorry`s (`Assumptions` 1,
  `BonehBoyenSecurity` 3).
- **Axioms** (`#eval` over every constant of the 11 modules, `Lean.collectAxioms`): 320
  declarations and 52 auxiliary constants; every one uses only `propext`, `Quot.sound`,
  `Classical.choice`, except the 4 targets and `bb1_sidSecure` (proved from 3 of them), which add
  `sorryAx`.
- **Rule 10.** Seven whole-file seal probes (`attribute [local irreducible]` on 2–51 foreign
  TCSlib definitions per module; names outside a module's closure are reported "unknown" and
  cannot be read; they are the only diagnostics in three probes): 7/7 with 0 other errors.
  Earlier runs found four reads (`intro` through `Correct` and through `SIDSecure`, and
  `DBDHAssumption` applied as a function in `Joux` and in `BonehBoyenSecurity`), now through
  `correct_iff`, `sidSecure_iff` and `dbdhAssumption_iff`. Controls: sealed `intro` through `Correct` fails;
  the same through `correct_iff` passes.
- **Style.** `scripts/style_lint.py`: 0 findings in 11 files. `campaign_style_lint.py --check8b`:
  0 FAIL, 2 WARN, both the check-8 acronym heuristic (`DBDHAssumption`, `BDHAssumption`,
  `SIDSecure` have readers `dbdhAssumption_iff`, `bdhAssumption_iff`, `sidSecure_iff`; the LWE
  precedent of `dlweAssumption_iff`).
- **Restore.** 8 backups copied back (0 hash failures), 15 new oleans deleted, 4 emptied
  directories pruned; snapshot after: 1230 files, `457ba704…a15f`, byte-identical (SNAPSHOT
  EQUAL).

- **Round 2 (Q11 split, 2026-11-16).** `stmt/pairings` rebased onto `523d80d2` (records only
  since `e7a9f70f`; range-diff identical, Lean sources unchanged) and T4 moved, byte-identical,
  to `BonehBoyenMachine.lean`. 12 modules: 12/12 rc 0, 0 errors, 4 target `sorry`s
  (`Assumptions` 1, `BonehBoyenMachine` 1, `BonehBoyenSecurity` 2). Axioms: 320 declarations and
  52 auxiliary constants, standard only except `sorryAx` in the 4 targets and `bb1_sidSecure`.
  Rule 10: the round-1 seal probes for the two changed modules pass (controls as before), and
  whole-file seals A/B, strict and coe, of `BonehBoyenMachine`, `BonehBoyenSecurity` and the
  `IdentityBased` facade pass 12/12 (`-DmaxErrors=0`). Lint unchanged (0 findings; 0 FAIL,
  2 WARN). Root `TCSlib` builds: 278 modules rebuilt from source on the tree (the closure's
  changed and missing modules and their downstream), 278/278 rc 0, root included. Evidence:
  `briefs/pairings/statement-phase/EVIDENCE.md`, round 2.

## Decision log

| Date | Decision / evidence | Status |
|---|---|---|
| 2026-11-16 | **Ruling (Seyoon): pairing campaign approved.** Abstract symmetric bilinear groups in the asymptotic/NUPPT framework with BDH and DBDH; Joux tripartite DH (protocol, correctness, key indistinguishability under DBDH); Boneh–Boyen BB1 selective-ID IBE in the standard model (IND-sID-CPA, scheme, correctness, security from DBDH). Out: Boneh–Franklin (no random-oracle layer), Type-3 pairings, concrete groups. Records on `cryptography/pass-shelat-ch2-4` in this file and `briefs/pairings/`; Lean by PR into that branch. | Approved scope |
| 2026-11-16 | **Sources received (Seyoon; not committed):** Jou00 publisher copy `dd423b93…f6df9`; BB04 ePrint 2004/172 full version `63c1c7b0…35de` (its numbering used). Both read; formulation differences recorded in § Sources. | Record |
| 2026-11-16 | **Ruling (Seyoon): IBE under `AdvancedEncryption/IdentityBased/`** (namespace `TCSlib.Cryptography.AdvancedEncryption.IdentityBased`); `Pairing/` and `KeyExchange/Joux` stay. `AdvancedEncryption.lean` is shared with GSW; the second statement PR adds its child import. Applied in the draft before commit. | Approved layout |
| 2026-11-16 | **Statement draft committed locally** on `stmt/pairings` (base `e7a9f70f5c1f11c2670f427ef813f2a6d8c53543`): modules `b02e6ce4a3dcc7c945825d1f1d3b636c5e377a01`, root exports `ce9c3728ec582be45fc33ca68d64b5533701093d` (both SSH-signed). 11 modules, 4 sorried targets; Joux and BB1 correctness proved; `bb1_sidSecure` proved from T2–T4. Checks, axioms, seals and style as in § Verification. Not pushed. | Ready for the statement PR (maintainer) and Codex statement gate |
| 2026-11-16 | **`dl-oleans-2` restored** to snapshot `457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f` (8 backups restored, 15 new oleans deleted; SNAPSHOT EQUAL). | Done |
| 2026-11-16 | Questions Q1–Q13 (§ Questions) await Seyoon's rulings. | Open |
| 2026-11-16 | **Rulings Q1–Q13 (Seyoon): all recommendations accepted.** Q1: abstract bilinear bundle from a uniform PPT generator with a total description map. Q2: `g` uniform in `G*`. Q3: Joux in the single-point `F_W` form. Q4: Joux key indistinguishability under DBDH only. Q5: typed IBE algorithms; a "BB1 is PPT" statement is deferred. Q6: `ℓ`-bit identities read in `Z_p`. Q7: one machine with an `Init` oracle. Q8: out-of-space challenge messages refused with `⊥`. Q9: the two-experiment advantage. Q10: keep T1 (DBDH ⇒ BDH). Q11: three fill units (`pair-bdh`, `bb1-sim`, `bb1-machine`), with T4 moved to its own module before the statement PR. Q12: PDFs uncommitted, with Markdown transcriptions of only the passages used, ingested later. Q13: `Ops` as drafted. Noted: Joux 2000 states no security theorem, so key indistinguishability under DBDH formalises its §5 remark. Draft branch `stmt/pairings` pushed at `ce9c3728`. | Approved |
| 2026-11-16 | **Q11 applied** on the local `stmt/pairings`: rebased onto `523d80d2d4dd8e4ed6799358831e5b3806c6187b` (records only since `e7a9f70f`; range-diff 2/2 identical: `8aa111658bd0509c0fd204d605538ff440f08d02`, `b7ca25477c1685795f2ea45cd895889f7ecaf1c8`) and T4 `exists_bb1_distinguisher` moved byte-identically to `AdvancedEncryption/IdentityBased/BonehBoyenMachine.lean`: head `110c2f9db810d243693b9a5e8976a5ad205f1bab` (SSH-signed). `bb1-sim` owns `BonehBoyenSecurity.lean` (T2, T3), `bb1-machine` owns `BonehBoyenMachine.lean` (T4). 12/12 modules rc 0 with the 4 target `sorry`s; axioms, seals and lint as in § Verification, round 2; root `TCSlib` builds. `dl-oleans-2` restored (SNAPSHOT EQUAL). Not pushed: `origin/stmt/pairings` is still `ce9c3728`. The records branch then advanced to `a32ad0df` (#318, #319, #323 merged); none of their Lean files is in the pairing closure and `stmt/pairings` merges into it cleanly (`git merge-tree`). | Ready for the statement PR (maintainer) |
| 2026-11-16 | **Gate 40 pack** (Codex statement gate, standing ruling): `briefs/pairings/gates/40-pairings-statements/` for draft [PR #331](https://github.com/Shilun-Allan-Li/tcslib/pull/331) at `110c2f9db810d243693b9a5e8976a5ad205f1bab` (base `523d80d2`; 3 commits, 13 files +2153/−0). Statement audit of the definitions under Q1–Q13 (bundle and generator, BDH/DBDH, IBE interface, selective-ID game, BB1, the simulator), truth and sufficiency of T1–T4 (`bb1_sidSecure` uses T2–T4 only), and the proved results audited as proofs (Joux, `jouxGame_eq_dbdhGame`, BB1 correctness, `bb1_sidSecure`); Rule 10 (canonical seals cover 3 of the 12 modules; the other 9 rest on the round-1 hand-list seals, put to Codex), docstrings and sketches, the Q11 unit split, duplication, policy. Source excerpts of only the passages used ([Jou00] §2, §3, §5; [BB04] §2.1–§3.1, §4.1–§4.2, §4.4), PDF hashes re-checked. Evidence `stmt-pairings-r2.zip` (`83b05fbe`) filed at `statement-phase/evidence-r2/` with its manifest (411/411) and PROVENANCE. Merge interaction (git objects): clean with the tip `0542dd92` (#326 merged), #324, #327, #332; add/add conflict with #333 in `AdvancedEncryption.lean` and `TCSlib.lean`, resolved by union (all open heads in two orders give one tree `1fc1b521`). Merge conditions: union by whichever of #331/#333 lands second; rebuild `Pairing/Operations` and its 6 downstream modules (closure meets #326's `DTIME.lean`) and the root on the merged tree. verification.zip `348ce61f` (99 entries), sources.zip 86 files, pack `278ce323`. | Ready to stage |
| 2026-11-16 | **Gate 40 staged** on the exchange (local commit, for the maintainer to verify and push): `outbox/gates/40-pairings-statements-gate/` at `870bed6ca6d79f43599ab2972f74834137672b2a` (on the exchange tip `da8f8f66`; bundle 18 sections, SHA-256 `34a4a1b7`; SHA256SUMS `eaf1dfab`, 13/13 from a fresh archive; `verification.zip` `348ce61f`, 98/98 inner; records pin `356321accdd29b9ec73391b1c7b211b7d4cabf0f`, signed; Lean head `110c2f9d` (#331)). Local branch `stage/gate40-exchange`. Dispatch prompt `briefs/pairings/gates/40-pairings-statements/dispatch.md`. | Ready to dispatch once pushed |
| 2026-11-16 | **Gate 40 findings** (Codex, round 1) filed at `briefs/pairings/gates/40-pairings-statements/findings/gate40-pairings-statements-findings.md`: **HOLD**, 0 blockers, 2 majors, 4 minors, on #331 head `110c2f9d`. G40-01 (major): the generic `IBEScheme` encodings carry no fidelity law, so a plaintext-revealing scheme with constant `encCT` is `Correct` and `SIDSecure` (countermodel; not a defect of BB1 or of T1–T4). G40-02 (major): canonical Rule 10 seals cover only `BonehBoyenMachine`, `BonehBoyenSecurity` and the facade; `Group`, `Joux`, `Defs`, `BonehBoyen`, `Assumptions`, `Operations` need term-collected seals, controls and the unfold scan. Minors: G40-03 explicit T4 sampler parameters (`n = κ + wG(κ) + 1`, `sampleBelowL p (Nat.size p) n n`); G40-04 T4 source tag, T1 attribution, `bilinear_pow` domain wording; G40-05 `**Proof sketch.**` markers on `decrypt_encrypt` and `bb1_correct`; G40-06 README checkpoint and PR-description coverage wording. T1–T4 judged true and T2–T4 sufficient for `bb1_sidSecure`; fill note for T2: `ProbComp.expect_simulate_congr` has one state type, so the fill needs a common augmented state or a shared relational lemma in `Games`. G40-01 formulation put to Seyoon. | Awaiting ruling (G40-01) |
| 2026-11-16 | **Ruling G40-01** (Seyoon): **injectivity fields.** `IBEScheme` gains three Prop fields: `encPP` injective on the parameters of setup outputs; `encSK` and `encCT` injective on the keys and ciphertexts reachable under one setup output. All three are proved for `bb1Scheme` in #331, with no new admissions; efficiency stays deferred (Q5). The maintainer writes LE-gate40 (fields, BB1 proofs, minors G40-03 to G40-06) and runs the G40-02 canonical seals on `Group`, `Joux`, `Defs`, `BonehBoyen`, `Assumptions` and `Operations`, then stages Gate 40 round 2. | In progress |
| 2026-11-16 | **G40-06 (records part)**: `briefs/pairings/README.md` current checkpoint refreshed to #331 at `110c2f9d` (base `523d80d2`), the Gate 40 hold, ruling G40-01 and LE-gate40; seal coverage stated explicitly (canonical 12 probes over 3 modules; 6 modules hand-list only until LE-gate40). Historical entries kept. The PR-description part follows with LE-gate40. LE-gate40 started (maintainer job; waits for a free olean tree). | In progress |
| 2026-11-16 | **Integration builds for #331, #332, #333: all PASS** (`dl-oleans-2`; evidence `briefs/pass-shelat-ch5-8/maintainer/int-stmt-331-333-2026-11-16/`, zip `9ffa41bbb1fb703bcd36ff15bc810a7ee09f3236445f81e1096eb63144617172`, 1141 files). Scratch merges on the tip `c58597e6` (unpushed, unsigned scratch): C1 tip+#332 `df4cfea4` (clean; #323's `isFaninTwo_iff` intact); C2 C1+#333 `18777085` (clean); C3 tip+#331 `c67f94a4` (clean); C4 C2+#331 `cbfa9d85` (tree `26a68b89`; add/add on `AdvancedEncryption.lean` and content conflict on `TCSlib.lean`, resolved by union; resolved files in `resolved/`, to be applied by the maintainer when #331 is updated for merge). Builds, every module rc 0 with 0 `error:`/`error(`: 3 tip+#331 652/652; 2 tip+#332+#333 292 rebuilt; 1 tip+#332 3 rebuilt; 4 combined 4 rebuilt; reuse keyed on source and import closure, state check OK after each; whole-tree check at C4 (1299 modules) OK. Admissions: tip 202, C1 202, C2 237 (+35 GSW targets), C3 206 (+4 T1–T4), C4 241; no other change. Axioms: #332 readers standard; Joux and `bb1_correct` sorry-free; T1–T4 and the 10 GSW headlines each reach `sorryAx` only through themselves; `bb1_sidSecure` inherits exactly T2–T4. Lint Cryptography 92/101 at tip, C1, C2; 92/103 with #331 (two new check-8 WARNs: `SIDSecure`; `BDHAssumption`/`DBDHAssumption`; passed to LE-gate40). `dl-oleans-2` restored to `457ba704` (SNAPSHOT EQUAL). Stray `/lint-a` at the filesystem root (a mistyped redirect, tip lint lines) left for Seyoon; its deletion was refused to the job. #332 and #333 marked ready. | #332, #333 clear to merge |
| 2026-11-16 | **#332 and #333 merged** (Seyoon): the records tip now holds the DAGCircuit readers and the GSW statements. GSW fills `gsw-core`/`gsw-security` were issued on `486f44f8`, now an ancestor of the tip. Cross-build tip × #327 × #324 running on `dl-oleans-2` (#327 and #324 touch `SequentialZK`, `ComposeSecurity` and `ZeroKnowledge/Defs`, downstream of `DAGCircuit`); #327 (Gate 39 CLOSED) marked ready. #331 must take the resolved facade union (`maintainer/int-stmt-331-333-2026-11-16/resolved/`) when it is updated after LE-gate40. | #327, #324 after cross-build |
| 2026-11-16 | **LE-gate40 pushed** on #331: `stmt/pairings` fast-forwarded `110c2f9d` → `70c1f44432a41bcdb6f6d8602d957d2fc68ce0da` (signed: `3f9c49e5` landing edit, `70c1f444` a two-line proof fix; 5 files +189/−28). **G40-01:** `IBEScheme` gains `encPP_inj`, `encSK_inj`, `encCT_inj` (injectivity on setup outputs and on keys/ciphertexts reachable under one setup output; Deviation note: injectivity on reachable objects, not efficient decoding nor global injectivity; Q5 kept); proved for `bb1Scheme` via `bb1_encPP_inj`, `bb1_encSK_inj`, `bb1_encCT_inj` (public lemmas only; no generic helper, no private copies). **G40-03/04/05** doc-only (sampler parameters `n = κ + wG(κ) + 1`; T4 tag [BB04, §4.2]; T1 as folklore; natural vs signed exponent law; two `**Proof sketch.**` markers); strip-verified. Build of the 20-module pairing closure on the base: 20/20 rc 0, 0 `error:`/`error(`; sorry only T1–T4. Axioms: 384 constants, `sorryAx` only in T1–T4 and `bb1_sidSecure`; new lemmas and fields standard. **G40-02:** canonical seals on 10 owners (Group, Assumptions, Operations, Joux, Defs, BonehBoyen, Machine, Security, two facades): strict A/B and coe A/B 10/10 each, 0 errors; controls strict and coe ALL_OK True (43 sealed negatives each, each failing once); unfold scan 0 foreign. Lint: the two check-8 WARNs (`SIDSecure`, `BDH`/`DBDHAssumption`) are heuristic false positives (readers `sidSecure_iff`, `bdhAssumption_iff`, `dbdhAssumption_iff` exist). `dl-oleans` restored (SNAPSHOT EQUAL). Evidence `gates/40-pairings-statements/landing-r1/gate40-le-evidence.zip` (`5be013be`). Next: merge the tip (with #332, #333) into #331 with the resolved facade union, rebuild, then stage Gate 40 round 2. | Update and r2 next |
| 2026-11-16 | **#331 updated onto the tip** (local, unpushed until verified): signed merge `39d42e235a62b7085ffc19b01f371015c20d7795` of the records tip `673a2715` (with #332, #333) into `70c1f444`; the two facade conflicts resolved by the filed union (`maintainer/int-stmt-331-333-2026-11-16/resolved/`, byte-identical; the union keeps both sides' imports, contents entries and references). Diff against the tip: #331's 13 files only (+2293). Full-closure build on `dl-oleans` running; push, then Gate 40 round 2 staging, follow. | Build running |
| 2026-11-16 | **DW-7 ingests** (records `6078f369`): Jou00 (`joux-2000-tripartite-dh`) and BB04 (`boneh-boyen-2004-selective-id-ibe`) scoped passages ingested. **Correction:** the page images show BB04 writing absolute values in §2.1, in the §3.1 Decision BDH advantage and in the proof of Theorem 4.1, so this plan's item 6 ("written without an absolute value") is wrong; the Lean's absolute decision advantage therefore follows BB04, and any docstring calling it a deviation should be corrected in a later doc edit (to be checked against #331's docstrings). | Correction noted |
| 2026-11-16 | **#331 updated and pushed**: `stmt/pairings` fast-forwarded `70c1f444` → `9e7a96481785d6cac4dea3b2e990c49ac278b060` = the signed merge `39d42e23` (tip `673a2715` with #332, #333 into `70c1f444`; facades by the filed union) plus LE-doc-abs `9e7a9648` (docstring only, strip-equal: [BB04, §3.1] writes the absolute difference, per the DW-7 transcription). Build of `39d42e23` on `dl-oleans` (evidence `gates/40-pairings-statements/integration-tip/int-331-tip-evidence.zip`, `3227f70b`): diff vs tip = #331's 13 files; facades equal the resolved files; code tree = C4 except the 5 LE-gate40 files; closure 1299 modules, 661 rebuilt, 661/661 rc 0, 0 `error:`/`error(`; sorry totals tip 237 → head 241 (T1–T4 only); whole-tree check OK; axioms: `bb1_correct`, Joux results and the three `bb1_enc*_inj` standard; T1–T4 each the only sorry in its closure; `bb1_sidSecure` inherits exactly T2–T4; lint only the two known check-8 false positives. `dl-oleans` restored (SNAPSHOT EQUAL). A 09:00 UTC disk-full incident (this job's full `git archive` for lint) stopped the other build; this build's 31 modules from that window re-verified identical. Next: Gate 40 round 2 pack. | Gate 40 r2 to stage |

## ===== briefs/pairings/gates/40-pairings-statements/pack.md (records, at b356e50b1b908b26c1379f2fa9e53d604dabfe41) =====

# Gate 40 · Pairing campaign statements: bilinear groups, Joux, Boneh–Boyen BB1 (statement)

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews). The pairing
campaign keeps its own gate folder (`briefs/pairings/gates/`); the gate number continues the global sequence.

- **PR:** draft [PR #331](https://github.com/Shilun-Allan-Li/tcslib/pull/331) at
  `110c2f9db810d243693b9a5e8976a5ad205f1bab` (branch `stmt/pairings`, tree
  `e0fcac097c5e6e66ff78496c575a417f50e8e9f7`).
- **Target and base:** `cryptography/pass-shelat-ch2-4`, merge base `523d80d2d4dd8e4ed6799358831e5b3806c6187b`. The
  diff `origin/cryptography/pass-shelat-ch2-4...110c2f9d` equals `523d80d2..110c2f9d` byte for byte (`pr.diff.txt`,
  119,848 bytes, SHA-256 `9deba4da…`; `pack-checks/series.txt`). Since the base the records branch has gained #318,
  #319, #323 and (during this staging) #326; their interaction is under **Merge interaction**.
- **Commits:** 3, all by the maintainer (author and committer Claude, `gpgsig` header present on each):
  `8aa11165` modules, `b7ca2547` root exports, `110c2f9d` "move T4 to BonehBoyenMachine (ruling Q11)". Rebased from
  the round-1 head `ce9c3728` with range-diff 2/2 `=` (evidence `git/rebase-range-diff.txt`).
- **Scope:** a **statement audit** before any fill, plus an audit **as proofs** of the results the PR already proves.
  The campaign plan is `PairingCryptographyPlan.md` (scope ruling, location ruling, rulings Q1–Q13 of 2026-11-16, all
  recommendations accepted, Q11 applied).
- **Sources** (PDFs not committed; text excerpts of only the passages used are in `source-excerpts/` and in the
  bundle, ruling Q12): [Jou00] A. Joux, ANTS-IV 2000, LNCS 1838, pp. 385–393 (SHA-256 `dd423b93…f6df9`); [BB04]
  D. Boneh, X. Boyen, ePrint 2004/172, full version December 2004, **its numbering** (SHA-256 `63c1c7b0…35de`). Both
  hashes were re-checked when the excerpts were written.

## What changed

13 files, 2153 insertions, 0 deletions (`pack-checks/files.txt`). Paths under `TCSlib/Cryptography/`. Every line is at
most 100 characters; every file is under 1000 lines.

| File | Lines | Public decls | `sorry` | Content |
|---|---:|---:|---:|---|
| `Pairing/Group.lean` | 299 | 24 | 0 | `BilinearGroup`, `BilinearGen`, `desc`, `inst`, `OrderAtLeastExcept`; group facts (all proved) |
| `Pairing/Assumptions.lean` | 221 | 15 | 1 | `tupleStr`, `bdhStr`, `dbdhGame`, `dbdhAdv`, `DBDHAssumption`, `bdhGame`, `BDHAssumption`; **T1** |
| `Pairing/Operations.lean` | 117 | 1 | 0 | `BilinearGen.Ops` (efficiency contract, Q13) |
| `KeyExchange/Joux.lean` | 193 | 15 | 0 | protocol, correctness, `jouxGame_eq_dbdhGame`, key indistinguishability (all proved) |
| `AdvancedEncryption/IdentityBased/Defs.lean` | 408 | 37 | 0 | `IBEScheme`, `Correct`, `sidImpl` and its 9 case lemmas, `oracleImpl`, `sidGame`, `SIDSecure` |
| `AdvancedEncryption/IdentityBased/BonehBoyen.lean` | 553 | 45 | 0 | BB1, `bb1Scheme`, `bb1_correct` (proved), the simulator `bb1Sim*` |
| `AdvancedEncryption/IdentityBased/BonehBoyenMachine.lean` | 78 | 1 | 1 | **T4** `exists_bb1_distinguisher` (Q11) |
| `AdvancedEncryption/IdentityBased/BonehBoyenSecurity.lean` | 170 | 3 | 2 | **T2**, **T3**, `bb1_sidSecure` (proved from T2–T4) |
| facades `Pairing`, `KeyExchange`, `AdvancedEncryption/IdentityBased`, `AdvancedEncryption` | 31, 23, 32, 25 | — | 0 | each imports and lists every child (`pack-checks/facades.txt`) |
| `TCSlib.lean` (root) | 86 → 89 | — | — | three imports, insertion only |

`pack-checks/decls.txt` lists every declaration (kind, body `rfl` / `Iff.rfl` / proof / `sorry`, docstring, source tag,
sketch); `pack-checks/readers.txt` the reader of every public definition (all present; structures are read through
their fields); `pack-checks/names.txt` finds **no** full-name clash with the 22,173 public names at the tip.

### The four targets

```lean
-- T1  Pairing/Assumptions.lean
theorem BilinearGen.bdhAssumption_of_dbdhAssumption
    (hN : ∃ δ : ℕ → ℝ, Negligible δ ∧ G.OrderAtLeastExcept (fun κ => 2 ^ κ) δ)
    (h : G.DBDHAssumption) : G.BDHAssumption
-- T2  BonehBoyenSecurity.lean
theorem bb1_sim_real (A : NUPPT) (q : ℕ) (b : Bool) (κ : ℕ) :
    advantage ((bb1Scheme G ℓ).sidGame A q b κ) (bb1SimGame G ℓ A q b true κ) ≤
      uprob (fun r : G.gen.Coins κ => (G.inst κ r).order < 2 ^ ℓ.eval κ)
-- T3  BonehBoyenSecurity.lean
theorem bb1_sim_random (A : NUPPT) (q : ℕ) (κ : ℕ) :
    advantage (bb1SimGame G ℓ A q false false κ) (bb1SimGame G ℓ A q true false κ) = 0
-- T4  BonehBoyenMachine.lean
theorem exists_bb1_distinguisher (H : Candidates.ArithmeticFP) (O : G.Ops) (A : NUPPT) (q : PolyExpr) :
    ∃ D : Bool → NUPPT, ∃ σ : ℕ → ℝ, Negligible σ ∧ ∀ (b real : Bool) (κ : ℕ),
      advantage (bb1SimGame G ℓ A (q.eval κ) b real κ) (G.dbdhGame (D b) real κ) ≤ σ κ
```

and the proved headline

```lean
theorem bb1_sidSecure (H : Candidates.ArithmeticFP) (O : G.Ops)
    (hN : ∃ δ : ℕ → ℝ, Negligible δ ∧ G.OrderAtLeastExcept (fun κ => 2 ^ ℓ.eval κ) δ)
    (h : G.DBDHAssumption) : (bb1Scheme G ℓ).SIDSecure
```

`bb1_sidSecure` uses **T2, T3 and T4 only**; T1 (DBDH ⇒ BDH) is a separate result that nothing in the PR uses. Its
proof chains nine games, `sidGame b=0 → sim(0,P) → dbdh(D₀,P) → dbdh(D₀,R) → sim(0,R) → sim(1,R) → dbdh(D₁,R) →
dbdh(D₁,P) → sim(1,P) → sidGame b=1`, giving `2δ + 4σ + dbdhAdv D₀ + dbdhAdv D₁` (`linarith` over
`advantage_triangle` and `advantage_comm`).

## Rulings and records in force

- **Scope (Seyoon, 2026-11-16):** abstract symmetric bilinear groups in the asymptotic/NUPPT framework with BDH and
  DBDH; Joux (protocol, correctness, key indistinguishability under DBDH); BB1 in the standard model (IND-sID-CPA,
  scheme, correctness, security from DBDH). Out: Boneh–Franklin, Type-3 pairings, concrete groups, BB2, HIBE depth > 1,
  BB04 §4.3/§6/§7.
- **Location (Seyoon, 2026-11-16):** `Pairing/`, `KeyExchange/`, and IBE under `AdvancedEncryption/IdentityBased/`
  (namespace `TCSlib.Cryptography.AdvancedEncryption.IdentityBased`). `AdvancedEncryption.lean` is **shared with GSW**;
  the draft facade imports only `IdentityBased`, and whichever statement PR lands second adds its child.
- **Q1–Q13 (Seyoon, 2026-11-16), all (A):** Q1 abstract bundle from a uniform PPT generator with a total description
  map; Q2 `g` uniform in `G^*`; Q3 Joux single-point `F_W`; Q4 Joux key indistinguishability under DBDH only; Q5 typed
  IBE algorithms, "BB1 is PPT" deferred; Q6 `ℓ`-bit identities read in `Z_p`; Q7 one machine with an `Init` oracle;
  Q8 out-of-space challenges refused with `⊥`; Q9 the two-experiment advantage; Q10 keep T1; Q11 three fill units,
  T4 in its own module; Q12 PDFs uncommitted, Markdown transcriptions of only the passages used, ingested later; Q13
  `Ops` as drafted.
- **Plan § Sources, "Where the papers' formulations differ from the draft"** (nine disclosed deviations) and
  **§ Modelling choices for the statement gate** (thirteen items) are the deviation list this gate checks against.
- **Standing rules:** Rule 10 (no proof reads another file's definition except through published readers); policy
  §§1–3 (modularity, attribution with `[Tag, location]`, `**Proof sketch.**` for nontrivial proofs and sorry-stubs);
  the #305 facade rule; lines of at most 100 characters.

## Questions for the audit

1. **Fidelity of the definitions under the rulings.** Compare with `source-excerpts/BB04-excerpts.md` (§2.1, §2.2,
   §3.1, §4.1, §4.2, §4.4) and `Jou00-excerpts.md` (§2, §3, §5).
   - *Bundle and generator* (`BilinearGroup`, `BilinearGen`): bimultiplicative `pair : G →* G →* GT` for
     [BB04, §2.2] item 1 (`bilinear_pow` derives `e(u^a, v^b) = e(u, v)^{ab}` for natural exponents; the paper says
     `a, b ∈ Z`); non-degeneracy at the bundle's `gen` (`pair_ne_one` extends it to `G^*`); equal prime orders; a total
     description map, exact description length, no validity predicate (Q1); large order only through
     `OrderAtLeastExcept N δ`.
   - *BDH and DBDH* (`dbdhGame`, `bdhGame`): `g` uniform in `G^*`, `a, b, c` uniform in `Z_p`, `T` uniform in `G_T`,
     the adversary's coins last; inputs `⟨d, ⟨g, g^a, g^b, g^c, T⟩⟩` with the description in front (D3); the advantage
     `|·|` of [BB04, §3.1]'s signed difference (deviation 6); BDH wins iff the output **is the encoding** of
     `e(g, g)^{abc}`.
   - *IBE interface and selective-ID game* (`IBEScheme`, `sidImpl`, `sidGame`, `SIDSecure`): one `NUPPT` with
     oracles `Init` (0), `KeyGen` (1), `Challenge` (2) (Q7); `Setup` sampled before the run and revealed only at
     `Init` (is this [BB04, §2.1]'s order *in distribution* for every adversary, including one that queries
     `KeyGen`/`Challenge` before `Init` or calls `Init` twice?); `⊥` (`zeroBits`) for `KeyGen(ID*)`, before `Init`,
     and for challenges outside `M` (deviation 7, Q8), with a validity bit on `KeyGen` answers but none on
     `Challenge` answers; fresh `KeyGen` coins per query; the first valid challenge recorded and repeated; one
     polynomial budget for all queries; `ℓ(κ)`-bit identities (Q6); messages as `wT(κ)`-bit strings with
     `MsgSpace` = "is an encoding" (Q9 of the modelling list); two-experiment advantage (Q9), quantifier shape of
     `FixedLengthPKScheme.INDSecure`.
   - *BB1* (`BB1.setup/keyGen/encrypt/decrypt`, `bb1Scheme`): depth-1 [BB04, §4.1] with `Setup`'s sample order
     `g ∈ G^*, α, h, g₂` (`h, g₂` uniform in `G`, as the paper: "random elements `h_1 … ∈ G` and a random element
     `g_2 ∈ G`"); `F(x) = g₁^x h`; `idToZ` = binary value mod `p` (§4.4 with `H` the identity on `ℓ`-bit strings,
     `2^ℓ ≤ p`); description tags and `⊥` across descriptions (modelling choice 12); `decodeT` reading `1` off the
     message space.
   - *The simulator* (`bb1SimParams`, `bb1SimKey`, `bb1SimInit`, `bb1SimKeyQ`, `bb1SimCt`, `bb1SimChal`,
     `bb1SimGame`): against the proof of [BB04, Theorem 4.1] at depth 1 (`g₁ = X`, `g₂ = Y`,
     `h = X^{−ID*} g^{α₁}` with `α₁` drawn at the first `Init`, keys `(Y^{−α₁/(ID−ID*)} F(ID)^r, Y^{−1/(ID−ID*)} g^r)`,
     challenge `(M_b·T, Z, Z^{α₁})`). Note that `ZMod` division by zero is `0`: on colliding residues
     (`ID ≠ ID*` as strings, `idToZ ID = idToZ ID*`, possible only when `p < 2^ℓ`) the simulated key is a defined but
     wrong value; T2 excludes those coins and T4 must reproduce the same value.
2. **Is every target true and sufficient, with no hidden hypothesis?**
   - **T1:** the sketch's distinguisher re-pairs the first five components and compares `A`'s answer with `T`'s
     encoding; on `R_BDH` it accepts with probability `≤ 1/p`, so `Pr[A wins] ≤ dbdhAdv + 2^{−κ} + δ(κ)`. Is
     `OrderAtLeastExcept (2^κ)` the right (and only) extra hypothesis? Is "re-pair" polynomial-time for the
     `pairEncode` layout of `tupleStr`/`bdhStr`?
   - **T2:** is the bound `Pr_r[p < 2^ℓ]` correct for **every** adversary, budget `q` and bit, with the simulator's
     `α₁` drawn at `Init` rather than at `Setup`, the real `h` uniform in `G`, and `MsgSpace` depending only on the
     description? Is the coupling of the two `simulate` runs (different state types: `Option id × Option ct` versus
     `Option (id × Z_p) × Option ct`) expressible with the existing `Games` lemmas, or must the fill request a shared
     state-relation lemma (plan § Risks)?
   - **T3:** exact equality `= 0`: `T` is used only in the challenge's first component; is `T ↦ M_b·T` reindexing
     valid when the challenge is chosen adaptively after `T` is sampled?
   - **T4:** for **all** `b`, `real`, `κ` (including generator coins with `p < 2^ℓ` and colliding residues) is there a
     uniform PPT `D_b` whose DBDH experiment is within negligible `σ` of `bb1SimGame`? It needs `O` (order, `mulG`,
     `powG`, `mulT`, `memT`) and `H` (`ArithmeticFP`: negation, difference, inverse, with `0⁻¹ = 0` to match `ZMod`),
     exponents by `Candidates.sampleBelowL` with `wG(κ)`-bit trials (`p ≤ 2^{wG}` from injectivity of `encG`), and
     the handler theorem `Games.exists_handlerMachine`. Is anything missing from `Ops` (Q13 kept `pairStr`, which the
     reduction does not need)?
   - **Sufficiency:** do T2–T4 imply `bb1_sidSecure` with exactly the hypotheses stated (`H`, `O`, `hN` at `2^ℓ`,
     `h`)? Are `H` and `O` acceptable as hypotheses of a security theorem whose paper version has none (D4)?
3. **Audit the proved results as proofs** (`Pairing/Group.lean`, `KeyExchange/Joux.lean`, `BonehBoyen.lean`,
   `BonehBoyenSecurity.lean`):
   - Joux correctness `jouxKey_eq`, `joux_correct` ([Jou00, p. 388]) and the helper `pow_val_mul_mul`;
   - `jouxGame_eq_dbdhGame` (`rw [jouxGame_eq, dbdhGame_eq]; simp only [jouxKey_eq]; rfl`: the final `rfl` unfolds
     only `jouxMsg`, defined in the same file) and `jouxKeyIndist_of_dbdhAssumption` (through `dbdhAssumption_iff`);
   - `BB1.decrypt_encrypt` (the paper's computation, `pair_comm`, `bilinear_pow`) and `bb1_correct` (through
     `correct_iff`, `honestRun_eq`, the `bb1Scheme` `simps` equations, `allOutputs_true`, `decodeT_encT`);
   - `bb1_sidSecure` from T2–T4 (the nine-game chain above; check the four `σ` and two `δ` terms);
   - the group facts `pair_ne_one`, `pow_val_bijective`, `pair_comm`, `exists_pow_eq`, `pow_val_mul(_GT)`;
   - the case lemmas `sidImpl_*` (9), `oracleImpl_*` (3), `bb1SimInit/KeyQ/Chal_*` (9).
   All compile with standard axioms only (evidence `axioms.txt`: 320 declarations + 52 auxiliary constants;
   `sorryAx` only in T1–T4 and `bb1_sidSecure`).
4. **Rule 10, readers and seals.** Every public definition has a reader (`pack-checks/readers.txt`); none is
   `@[simp]`; `bb1Scheme` has non-simp `simps` equations. Seal coverage (please rate):
   - the canonical whole-file seals (archived Gate 06/10 instrumenter; strict A, `PolyExpr.eval`-sealed B, and the
     coe variants) were run in round 2 on **three** modules: `BonehBoyenMachine`, `BonehBoyenSecurity` and the
     `IdentityBased` facade, 12/12 probes (`rule10/seal-seals-*.tsv`). The PR description's "whole-file seals pass
     12/12" counts these probes, not modules;
   - the other nine new modules (including every module with a proof: `Group`, `Joux`, `Defs`, `BonehBoyen`) rely on
     the **round-1 hand-list seals** (`round1/tools/seal.py`: 2–51 named foreign definitions per module;
     `round1/seal/summary.txt`, whose `rc=1` lines are "unknown constant" for names outside a module's closure), with
     the controls `Control_neg` (sealed read of `Correct` fails) and `Control_pos`. Is that sufficient evidence that
     `bb1_correct`, `jouxGame_eq_dbdhGame`, `jouxKeyIndist_of_dbdhAssumption` and the `simp [sidImpl]` /
     `simp [bb1SimKeyQ]` case lemmas read foreign definitions only through readers, or is a canonical seal of those
     modules a necessary condition (a **major** if necessary evidence is missing)?
5. **Docstrings, tags and sketches** against the papers' numbering (BB04 ePrint numbering throughout): every public
   declaration has a docstring; T1–T4 and `bb1_sidSecure` carry `**Proof sketch.**`. Please rate:
   - `BB1.decrypt_encrypt`, `bb1_correct` and `jouxKeyIndist_of_dbdhAssumption` explain their proofs in prose without
     a `**Proof sketch.**` heading; `jouxGame_eq_dbdhGame` has none (a four-line proof). Policy §3 asks for a sketch
     for proofs over about 20 lines or of difficulty ≥ 3.
   - T1's docstring says DBDH ⇒ BDH is "not stated in [BB04] or [Jou00]" (folklore, Q10); BB04 §3.1 does not call
     the decision form "stronger" either. Is the source line adequate under policy §2?
   - The nine disclosed deviations (plan § Sources) and their docstring counterparts: single-point Joux (D-2), `g`
     uniform (D-3), HIBE depth 1 and `ℓ`-bit identities (D-4), asymptotic (D-5), two-experiment advantage (D-6),
     `⊥` (D-7), one distinguisher per bit (D-8), T1 not in the sources (D-9), and Joux's §5 remark formalized as key
     indistinguishability (D-1, Q4). Is any deviation undisclosed?
6. **The fill-unit split.** `pair-bdh` owns `Pairing/Assumptions.lean` (T1); `bb1-sim` owns `BonehBoyenSecurity.lean`
   (T2, T3); `bb1-machine` owns `BonehBoyenMachine.lean` (T4). The split moved the 21-line T4 block byte-identically
   (evidence `statements/T4-identity.txt`, `T4-block.txt`, `BonehBoyenSecurity-at-ce9c3728.lean`).
   `BonehBoyenSecurity` imports `BonehBoyenMachine` for the proved-modulo headline. Are the files disjoint, and can
   each unit be proved without editing another unit's file (helpers beside the owned file)?
7. **Duplication** against the existing DDH (`Candidates/DDH.lean`, `DiscreteLog.lean`), El Gamal
   (`Encryption/PublicKey/ElGamal.lean`, `GroupPKScheme`) and `Games` layers (`Games/Advantage.lean`,
   `PublicKey/OracleSecurity.lean`): all five are in `verification.zip` `context/` at the tip; `pack-checks/
   dupscan.txt` has the keyword scan (no BDH, IBE or pairing-group notion exists; `bilinear` hits are unrelated
   areas). Is `BilinearGen` a justified sibling of `ExpGroupGen`/`SafePrimeGen` (D1), `dbdhGame` of the DDH
   ensembles (D2 avoids the P8-1 seed distortion), `sidImpl`/`sidGame` of `FixedLengthPKScheme.indGame` (D6), and
   `oracleImpl` a new generic helper that belongs in `Games` instead?
8. **Policy: modularity, sizes, facades.** Layout `Pairing/`, `KeyExchange/`, `AdvancedEncryption/IdentityBased/`
   per the location ruling; the largest file is 553 lines; facades import and list every child; the root gains three
   imports. Are the imports precise (no bare `import Mathlib`)? Is `Operations.lean`'s import of
   `Candidates.Arithmetic` the right layering?

## Known dispositions (not findings)

- **The shared facade.** `AdvancedEncryption.lean` is added by both this PR and #333 (GSW), and both add an import to
  `TCSlib.lean`: an expected add/add conflict, resolved by union by whichever lands second (location ruling). It is a
  merge condition (below), not a finding.
- **The proofs of T1–T4 are out of scope;** the gate asks whether the statements are true, provable on the sketched
  routes and sufficient.
- **Typed honest algorithms** without an efficiency field (Q5) and the efficiency hypotheses `H`, `O` of the security
  theorem (D4) are ruled.
- **The evidence archive** `stmt-pairings-r2.zip` was not in the records when the PR was opened; this gate files it
  (`briefs/pairings/statement-phase/evidence-r2/`, with its manifest and PROVENANCE).
- **Source ingest (policy §2) is deferred** by Q12; the excerpts here are the gate's fidelity material, not the
  ingest.

### Slips noted by the staging (please rate)

- PR description: "the whole-file seals pass 12/12" (three modules × four variants; see Q4).
- `briefs/pairings/README.md` "Current checkpoint" still names the round-1 head `ce9c3728` and "not pushed"; the plan's
  identity table also names `ce9c3728`/`b02e6ce4` and base `e7a9f70f`. The decision log and the Q11 row carry the
  current head.
- The plan's decision-log row for Q11 says "Not pushed: `origin/stmt/pairings` is still `ce9c3728`"; the branch was
  pushed afterwards at `110c2f9d` (PassShelatChapter5-8Plan.md row of 2026-11-16).

## Merge interaction (maintainer merge conditions, not audit items)

From git objects only (`pack-checks/mergetrees.txt`, `pack-checks/mergeall.txt`); the records tip during staging was
`0542dd9210ccdb844ad125cd95f8488c9f553153` (it now contains #326, merged as `7e85f4c0`).

| Merge of #331 with | Result | Modules whose closure meets both sides' Lean changes |
|---|---|---|
| tip (`#318`, `#319`, `#323`, `#326` merged) | clean | 7: `Pairing/Operations` (its closure reaches `ClassP/DTIME.lean`, changed by #326's E1–E3), `Pairing`, `BonehBoyenMachine`, `BonehBoyenSecurity`, `IdentityBased`, `AdvancedEncryption`, `TCSlib` |
| #324 sc-compose `4bd2d80b` | clean | `TCSlib` only |
| #327 seq-zk `bd19c433` | clean | `TCSlib` only |
| #332 DAGCircuit readers `94eae71b` | clean | `TCSlib` only |
| #333 GSW `48d796a8` | **conflict** in `TCSlib.lean` and `AdvancedEncryption.lean` (add/add) | `AdvancedEncryption`, `TCSlib` |

All open heads merged onto the tip in two orders (#324, #326, #327, #331, #332, #333 and the reverse grouping) give the
**same tree** `1fc1b521602bd7ac2f4199accdb7f7245f428198` once the one conflict is resolved by union (`mergeall.txt`
prints the resolved facade: both children imported and listed, both references; `TCSlib.lean` gains `Pairing`,
`KeyExchange`, `AdvancedEncryption` after `Implications`, once each).

**Merge conditions.** (1) Whichever of #331 and #333 merges second resolves the facade and root by that union and
re-checks `AdvancedEncryption` and `TCSlib`. (2) The statement evidence was built at base `523d80d2`; before merging,
rebuild the seven modules above on the merged tree (the #326 change to `DTIME.lean` is in `Operations`' closure), with
the root last. No Lean file changed by #331 is changed by any other open or merged PR.

## Evidence

`verification.zip` (99 entries, SHA-256 `348ce61f7c8f1eb07faa8c1b4cf402fbc4f241d7909c9cd456129c75e0628f70`; its
`SHA256SUMS` lists every other entry; `PROVENANCE.txt` maps each to its source; built at records `0542dd92`):
- `evidence/`: `stmt-pairings-r2.zip` (SHA-256 `83b05fbe…d573d`, 411 files, its inner manifest verified) with its
  manifest `SHA256SUMS` and `PROVENANCE.txt`, byte-identical to the files this gate files in the records;
- `evidence-extracts/`: byte copies of the entries cited here: the build (`build/closure/summary.txt`: 20/20 rc 0, 4
  target `sorry`s; `build/root/summary.txt`: 278/278 rc 0), `axioms.txt`, the seals (`rule10/seal-seals-*.tsv`,
  `rule10/modules.txt`, `seal/summary.txt`), lint (0 findings; 2 check-8 acronym WARNs), the T4 split
  (`statements/`), the series (`git/`), the olean-tree snapshots (`457ba704…` before and after) and the axiom probe;
- `round1/`: the round-1 evidence already in the records (`briefs/pairings/statement-phase/evidence/`), including the
  hand-list seal tool and logs;
- `records/`: the plan, the pairings README, the statement-phase `EVIDENCE.md` (pre-pin versions) and `policy.md`;
- `source-excerpts/`: the two excerpt files;
- `context/`: `Candidates/DDH.lean`, `Candidates/DiscreteLog.lean`, `Encryption/PublicKey/ElGamal.lean`,
  `Games/Advantage.lean`, `Encryption/PublicKey/OracleSecurity.lean` at the tip (question 7);
- `pack-checks/`: `series`, `files`, `decls`, `sorries`, `readers`, `facades`, `names`, `dupscan`, `mergetrees`,
  `mergeall`, with the scripts that produced them (git objects and `python3 -I` only; nothing was built).

Also: `pr.diff.txt`, `pr-description.md` (fetched 2026-11-16), `source-head.json` (hashes, line counts, over-width
counts of the 13 files; SHA-256 `5a52bffe…`) and `sources.zip` (the import closure at the head of every changed module,
86 files, SHA-256 `a08ebc08…`).

## Findings delivery

Return `gate40-pairings-statements-findings.md` as a Markdown file in this chat. If you have several evidence files,
return a ZIP.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

**Severities**
- **blocker:** a false or unusable statement, a proved result whose proof is unsound, or a scope violation.
- **major:** a missing or wrong hypothesis, a statement too weak or too strong for its consumers (`bb1_sidSecure`, the
  fill routes), an undisclosed deviation from the sources or the rulings, a forbidden read in a proved declaration, a
  duplicate public result, or necessary evidence that cannot be verified.
- **minor:** documentation or API defects, including an inaccurate formula docstring or proof sketch.
- **note:** anything else.

Report the audited head and the counts by severity. The gate closes at zero blockers and zero majors.

## ===== TCSlib/Cryptography/Pairing/Group.lean (Lean, at 9e7a96481785d6cac4dea3b2e990c49ac278b060) =====

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.PPT
import TCSlib.Cryptography.Foundations.Probability
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SpecificGroups.Cyclic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Symmetric bilinear groups and their generators

A *bilinear group* [BB04, §2.2] is a pair of cyclic groups `G`, `G_1` of prime order `p` with a
map `e : G × G → G_1` that is bilinear (`e(u^a, v^b) = e(u, v)^{ab}`) and non-degenerate
(`e(g, g) ≠ 1` for a generator `g`). The pairing is symmetric: `e(u, v) = e(v, u)`. Here the
groups stay abstract. No elliptic curve or concrete pairing (Weil, Tate) is formalized.

**Representation.** A bilinear group is a bundle `BilinearGroup wG wT`: two finite commutative
groups `G` and `GT` (the paper's `G_1`) of the same prime order, a distinguished generator `gen`,
the pairing as a bimultiplicative map `G →* G →* GT`, and injective fixed-width encodings of the
elements of both groups as `wG`- and `wT`-bit strings. A bimultiplicative map is the
multiplicative form of [BB04, §2.2, item 1]: `bilinear_pow` reads `e(u^a, v^b) = e(u, v)^{ab}`
for natural exponents; for integer exponents the law follows from the homomorphism fields.

**The generator.** The asymptotic layer quantifies over non-uniform PPT adversaries
(`Complexity.NUPPT`) and draws the group from a *bilinear group generator*, as the
discrete-logarithm and DDH layers draw theirs from an instance generator
(`Candidates.ExpGroupGen`, `Candidates.SafePrimeGen`). A `BilinearGen` is a PPT `Gen(1^κ)`
whose output string, the *description* `d`, has a fixed polynomial length. The group it describes
is `group κ d`, a total function of the description. So every string describes some bilinear
group, and no validity predicate is needed. Adversaries receive the description.

**Deviation:** [BB04] is concrete (a fixed group `G`, `(t, ε)` bounds); here the group is drawn
by a PPT generator at each security parameter, and security is asymptotic. The efficiency of the
group operations and of the pairing ("efficiently computable", [BB04, §2.2]) is not a field of
the bundle. It is the separate contract `BilinearGen.Ops` (`Pairing/Operations.lean`), assumed
only by the results whose reductions compute in the group.

## Main definitions

* `TCSlib.Cryptography.Pairing.BilinearGroup` — a symmetric bilinear group of prime order with
  fixed-width encodings [BB04, §2.2].
* `TCSlib.Cryptography.Pairing.BilinearGen` — a bilinear group generator; `BilinearGen.desc`,
  `BilinearGen.inst` — the description and the group at the generator's coins;
  `BilinearGen.OrderAtLeastExcept` — the order is large except on a set of coins of small
  probability.

## Main results

* `BilinearGroup.bilinear_pow`, `pair_pow_left`, `pair_pow_right` — bilinearity
  [BB04, §2.2, item 1].
* `BilinearGroup.pair_comm` — the pairing is symmetric [BB04, §2.2, the remark after item 2].
* `BilinearGroup.pow_order`, `BilinearGroup.pow_val_mul` — exponents act through `Z_p`.
* `BilinearGroup.exists_pow_eq` — every element of `G^*` generates `G`.
* `BilinearGroup.pair_ne_one` — every element of `G^*` pairs non-trivially with itself.
* `BilinearGroup.pow_val_bijective` — `a ↦ e(g, g)^a` is a bijection `Z_p → G_1` for `g ∈ G^*`.

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §2.2 (bilinear groups).
* [Jou00] A. Joux, *A One Round Protocol for Tripartite Diffie–Hellman*, ANTS-IV, LNCS 1838,
  pp. 385–393, Springer, 2000. §2 (the Weil and Tate pairings are bilinear and non-degenerate).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Definition 26.8, non-uniform PPT; the instance-generator convention of §2.8 and §3.11.)
-/

namespace TCSlib.Cryptography.Pairing

open Complexity

/-- A **symmetric bilinear group of prime order** with fixed-width encodings [BB04, §2.2]: finite
commutative groups `G` and `G_T` (the paper's `G_1`) of the same prime order `p`, a generator `g`
of `G` (`g ≠ 1`; `G` has prime order), a pairing `e : G × G → G_T` that is multiplicative in each
argument, and non-degenerate, `e(g, g) ≠ 1` [BB04, §2.2, items 1–2]. Elements are written as
`wG`-bit (resp. `wT`-bit) strings by injective encodings, the representation handed to machines.

**Deviation:** bilinearity is stated as a bimultiplicative map `G →* G →* G_T`. The paper's
`e(u^a, v^b) = e(u, v)^{ab}` for `a, b ∈ ℤ` follows from these homomorphism fields (`map_zpow` in
each argument); the published reader `bilinear_pow` states it for natural exponents `a, b ∈ ℕ`,
the form the schemes use (exponents `x.val` for `x ∈ Z_p`). The fixed generator `gen`
witnesses that `G^* = G ∖ {1}` is not empty; the schemes and assumptions sample their generator
uniformly from `G^*`, as [BB04, §3.1 and §4.1] do. -/
structure BilinearGroup (wG wT : ℕ) where
  /-- The source group `G`. -/
  G : Type
  /-- The target group `G_T` (the paper's `G_1`). -/
  GT : Type
  /-- `G` is a commutative group. -/
  [commGroupG : CommGroup G]
  /-- `G_T` is a commutative group. -/
  [commGroupGT : CommGroup GT]
  /-- `G` is finite. -/
  [fintypeG : Fintype G]
  /-- `G_T` is finite. -/
  [fintypeGT : Fintype GT]
  /-- Equality in `G` is decidable. -/
  [decEqG : DecidableEq G]
  /-- Equality in `G_T` is decidable. -/
  [decEqGT : DecidableEq GT]
  /-- The common prime order `p`. -/
  order : ℕ
  /-- `p` is prime. -/
  order_prime : order.Prime
  /-- `|G| = p`. -/
  card_G : Fintype.card G = order
  /-- `|G_T| = p`. -/
  card_GT : Fintype.card GT = order
  /-- A generator `g` of `G`. -/
  gen : G
  /-- `g ≠ 1`, so `g` generates the group `G` of prime order. -/
  gen_ne_one : gen ≠ 1
  /-- The pairing `e`, multiplicative in each argument. -/
  pair : G →* G →* GT
  /-- Non-degeneracy: `e(g, g) ≠ 1` [BB04, §2.2, item 2]. -/
  pair_gen_ne_one : pair gen gen ≠ 1
  /-- The encoding of `G` as `wG`-bit strings. -/
  encG : G → Fin wG → Bool
  /-- Distinct elements of `G` have distinct encodings. -/
  encG_injective : Function.Injective encG
  /-- The encoding of `G_T` as `wT`-bit strings. -/
  encT : GT → Fin wT → Bool
  /-- Distinct elements of `G_T` have distinct encodings. -/
  encT_injective : Function.Injective encT

attribute [instance] BilinearGroup.commGroupG BilinearGroup.commGroupGT BilinearGroup.fintypeG
  BilinearGroup.fintypeGT BilinearGroup.decEqG BilinearGroup.decEqGT

namespace BilinearGroup

variable {wG wT : ℕ} (B : BilinearGroup wG wT)

/-- The order of a bilinear group is prime, as a `Fact` (so `ZMod B.order` is a field). -/
instance factPrime : Fact B.order.Prime := ⟨B.order_prime⟩

/-- The order of a bilinear group is nonzero (so `ZMod B.order` is finite). -/
instance neZeroOrder : NeZero B.order := ⟨B.order_prime.ne_zero⟩

/-- `G^* = G ∖ {1}` is not empty: it contains the generator `gen`. -/
instance nonempty_ne_one : Nonempty {x : B.G // x ≠ 1} := ⟨⟨B.gen, B.gen_ne_one⟩⟩

/-- **Bilinearity** [BB04, §2.2, item 1]: `e(u^a, v^b) = e(u, v)^{ab}` for natural exponents
`a, b ∈ ℕ`. The paper states the law for `a, b ∈ ℤ`; that signed-exponent form follows from the
homomorphism fields of `pair` (`map_zpow`), and this reader is the natural-exponent case. -/
theorem bilinear_pow (u v : B.G) (a b : ℕ) : B.pair (u ^ a) (v ^ b) = B.pair u v ^ (a * b) := by
  rw [map_pow (B.pair (u ^ a)) v b, map_pow B.pair u a, MonoidHom.pow_apply, ← pow_mul,
    mul_comm]

/-- Bilinearity in the first argument: `e(u^a, v) = e(u, v)^a`. -/
theorem pair_pow_left (u v : B.G) (a : ℕ) : B.pair (u ^ a) v = B.pair u v ^ a := by
  rw [map_pow, MonoidHom.pow_apply]

/-- Bilinearity in the second argument: `e(u, v^b) = e(u, v)^b`. -/
theorem pair_pow_right (u v : B.G) (b : ℕ) : B.pair u (v ^ b) = B.pair u v ^ b :=
  map_pow (B.pair u) v b

/-- `|G| = p` as a `Nat.card`: `Nat.card B.G = B.order`. -/
theorem natCard_G : Nat.card B.G = B.order := by
  rw [Nat.card_eq_fintype_card, B.card_G]

/-- **Every element of `G^*` generates `G`**: for `g ≠ 1` and any `x`, `x = g^n` for some `n`
(`G` has prime order). -/
theorem exists_pow_eq {g : B.G} (hg : g ≠ 1) (x : B.G) : ∃ n : ℕ, g ^ n = x :=
  (Submonoid.mem_powers_iff _ _).1 (mem_powers_of_prime_card B.natCard_G hg)

/-- **The pairing is symmetric** [BB04, §2.2, the remark after item 2]: `e(u, v) = e(v, u)`,
since `e(g^a, g^b) = e(g, g)^{ab} = e(g^b, g^a)`. -/
theorem pair_comm (u v : B.G) : B.pair u v = B.pair v u := by
  obtain ⟨a, rfl⟩ := B.exists_pow_eq B.gen_ne_one u
  obtain ⟨b, rfl⟩ := B.exists_pow_eq B.gen_ne_one v
  rw [B.bilinear_pow, B.bilinear_pow, mul_comm]

/-- `x^p = 1` in `G`: Lagrange's theorem with `|G| = p`. -/
theorem pow_order (x : B.G) : x ^ B.order = 1 := by
  rw [← B.card_G]
  exact pow_card_eq_one

/-- `y^p = 1` in `G_T`: Lagrange's theorem with `|G_T| = p`. -/
theorem pow_order_GT (y : B.GT) : y ^ B.order = 1 := by
  rw [← B.card_GT]
  exact pow_card_eq_one

/-- Exponents of `G` act through `Z_p`: `x^{(ab mod p)} = (x^a)^b` read in `Z_p`, i.e.
`x ^ (a * b).val = x ^ (a.val * b.val)` for `a, b ∈ Z_p`. -/
theorem pow_val_mul (x : B.G) (a b : ZMod B.order) : x ^ (a * b).val = x ^ (a.val * b.val) := by
  rw [ZMod.val_mul, ← Nat.mod_add_div (a.val * b.val) B.order, pow_add, pow_mul, B.pow_order,
    one_pow, mul_one, Nat.mod_add_div]

/-- Exponents of `G_T` act through `Z_p`: `y ^ (a * b).val = y ^ (a.val * b.val)`. -/
theorem pow_val_mul_GT (y : B.GT) (a b : ZMod B.order) :
    y ^ (a * b).val = y ^ (a.val * b.val) := by
  rw [ZMod.val_mul, ← Nat.mod_add_div (a.val * b.val) B.order, pow_add, pow_mul, B.pow_order_GT,
    one_pow, mul_one, Nat.mod_add_div]

/-- **Non-degeneracy at every generator**: `e(x, x) ≠ 1` for every `x ∈ G^*` (from
`e(g, g) ≠ 1` [BB04, §2.2, item 2], since every `x ∈ G^*` generates `G`).

**Proof sketch.** Write `x = g^k` with `k ≢ 0 (mod p)` (`x ≠ 1`). Then
`e(x, x) = e(g, g)^{k²}` by bilinearity. The element `e(g, g) ≠ 1` of the group `G_T` of prime
order `p` has order `p`, and `p ∤ k²` because `p` is prime and `p ∤ k`. -/
theorem pair_ne_one {x : B.G} (hx : x ≠ 1) : B.pair x x ≠ 1 := by
  obtain ⟨k, rfl⟩ := B.exists_pow_eq B.gen_ne_one x
  rw [B.bilinear_pow]
  intro h
  have ho : orderOf (B.pair B.gen B.gen) = B.order :=
    orderOf_eq_prime (B.pow_order_GT _) B.pair_gen_ne_one
  have hd : B.order ∣ k * k := ho ▸ orderOf_dvd_of_pow_eq_one h
  obtain ⟨j, rfl⟩ : B.order ∣ k := ((Nat.Prime.dvd_mul B.order_prime).1 hd).elim id id
  exact hx (by rw [pow_mul, B.pow_order, one_pow])

/-- **`a ↦ e(x, x)^a` is a bijection `Z_p → G_T`** for every `x ∈ G^*`: the law of `e(x, x)^z`
for uniform `z ∈ Z_p` is uniform on `G_T` (the identification of [BB04, §3.1]'s "`T` uniform in
`G_1`" with `e(g, g)^z`, `z` uniform, used by the proofs).

**Proof sketch.** `e(x, x) ≠ 1` (`pair_ne_one`) has prime order `p` in `G_T`, so
`a ↦ e(x, x)^{a.val}` is injective on `Z_p`; both sides have `p` elements (`card_GT`). -/
theorem pow_val_bijective {x : B.G} (hx : x ≠ 1) :
    Function.Bijective fun a : ZMod B.order => B.pair x x ^ a.val := by
  have ho : orderOf (B.pair x x) = B.order :=
    orderOf_eq_prime (B.pow_order_GT _) (B.pair_ne_one hx)
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun a b hab => ZMod.val_injective _ ?_, by rw [ZMod.card, B.card_GT]⟩
  have h := pow_eq_pow_iff_modEq.1 hab
  rw [ho] at h
  exact Nat.ModEq.eq_of_lt_of_lt h (ZMod.val_lt a) (ZMod.val_lt b)

end BilinearGroup

/-- A **bilinear group generator**: a PPT `Gen(1^κ)` whose output, the *description* `d` of the
group, has `descLen(κ)` bits, and the bilinear group `group κ d` that `d` describes, with element
widths `wG(κ)` and `wT(κ)`. The form of [BB04, §2.2] ("`G` is a bilinear group") and of
[BB04, §4.1] ("the security parameter determines the size of `G`") in the asymptotic layer.

**Deviation:** the group is a total function of the description (every string describes some
bilinear group), so no validity predicate or threshold appears, unlike `Candidates.ExpGroupGen`;
descriptions have an exact polynomial length (a PPT generator can always pad its output to its
time bound). The order of the group is unconstrained here: results that need a large order
assume `OrderAtLeastExcept`. Efficient group operations are the separate contract
`BilinearGen.Ops`. -/
structure BilinearGen where
  /-- The generator `Gen(1^κ)`, run on the empty argument. -/
  gen : NUPPT
  /-- `Gen` is a PPT. -/
  gen_uniform : gen.Uniform
  /-- The length of a description. -/
  descLen : PolyExpr
  /-- Every description at parameter `κ` has `descLen(κ)` bits. -/
  desc_length : ∀ κ (r : gen.Coins κ), (gen.runAt κ [] r).length = descLen.eval κ
  /-- The width of the encoding of `G`. -/
  wG : PolyExpr
  /-- The width of the encoding of `G_T`. -/
  wT : PolyExpr
  /-- The bilinear group described by a string at parameter `κ`. -/
  group : (κ : ℕ) → List Bool → BilinearGroup (wG.eval κ) (wT.eval κ)

namespace BilinearGen

variable (G : BilinearGen)

/-- The description `d = Gen(1^κ; r)` output by the generator on the coins `r`. -/
def desc (κ : ℕ) (r : G.gen.Coins κ) : List Bool := G.gen.runAt κ [] r

/-- `G.desc κ r = G.gen.runAt κ [] r`. -/
theorem desc_eq (κ : ℕ) (r : G.gen.Coins κ) : G.desc κ r = G.gen.runAt κ [] r := rfl

/-- A description has `descLen(κ)` bits: `(G.desc κ r).length = G.descLen.eval κ`. -/
theorem length_desc (κ : ℕ) (r : G.gen.Coins κ) : (G.desc κ r).length = G.descLen.eval κ :=
  G.desc_length κ r

/-- The bilinear group generated on the coins `r`: `G.inst κ r = G.group κ (G.desc κ r)`. -/
def inst (κ : ℕ) (r : G.gen.Coins κ) : BilinearGroup (G.wG.eval κ) (G.wT.eval κ) :=
  G.group κ (G.desc κ r)

/-- `G.inst κ r = G.group κ (G.desc κ r)`. -/
theorem inst_eq (κ : ℕ) (r : G.gen.Coins κ) : G.inst κ r = G.group κ (G.desc κ r) := rfl

/-- **The order is at least `N(κ)` except with probability `δ(κ)`**: for every `κ`,
`Pr_r[|G| < N(κ)] ≤ δ(κ)` over the generator's coins `r`. With `N(κ) = 2^κ` and a negligible
`δ` this is "the security parameter determines the size of `G`" [BB04, §4.1]; with
`N(κ) = 2^{ℓ(κ)}` it makes `ℓ(κ)`-bit identities distinct in `Z_p` [BB04, §4.4, "`2^b < p`"].

**Deviation:** a strict PPT generator may fail with small probability, so a bound on every coin
string is not demanded (the lesson of `Candidates.ExpGroupGen.FullLengthExcept`, run-3 audit
P8-2). -/
def OrderAtLeastExcept (N : ℕ → ℕ) (δ : ℕ → ℝ) : Prop :=
  ∀ κ, uprob (fun r : G.gen.Coins κ => (G.inst κ r).order < N κ) ≤ δ κ

/-- `G.OrderAtLeastExcept N δ` iff for every `κ` the probability over the generator's coins that
the order is below `N κ` is at most `δ κ`. -/
theorem orderAtLeastExcept_iff (N : ℕ → ℕ) (δ : ℕ → ℝ) :
    G.OrderAtLeastExcept N δ ↔
      ∀ κ, uprob (fun r : G.gen.Coins κ => (G.inst κ r).order < N κ) ≤ δ κ :=
  Iff.rfl

end BilinearGen

end TCSlib.Cryptography.Pairing
```

## ===== TCSlib/Cryptography/Pairing/Assumptions.lean (Lean, at 9e7a96481785d6cac4dea3b2e990c49ac278b060) =====

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Pairing.Group
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Games.Advantage
import TCSlib.Cryptography.Foundations.Negligible

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The bilinear Diffie–Hellman assumptions

The *bilinear Diffie–Hellman* (BDH) problem [BB04, §3.1]: given `g, g^a, g^b, g^c ∈ G`, output
`e(g, g)^{abc} ∈ G_1`; and its decisional form (Decision BDH, DBDH): distinguish
`(g, g^a, g^b, g^c, e(g, g)^{abc})` (the distribution `P_BDH`) from `(g, g^a, g^b, g^c, T)` with
`T` uniform in `G_1` (the distribution `R_BDH`). In both, the generator `g` is uniform in
`G^* = G ∖ {1}`, the exponents `a, b, c` are uniform in `Z_p`, and the probability is also over
the adversary's coins. [BB04, §3.1] credits the BDH problem to [Jou00, SOK00, BF01].

**The experiments.** The bilinear group is drawn by the generator (`Pairing.BilinearGen`), and
the adversary is a non-uniform PPT machine (`Complexity.NUPPT`) that receives `1^κ` and the
string `⟨d, ⟨g, ⟨g^a, ⟨g^b, ⟨g^c, T⟩⟩⟩⟩⟩` of the description `d` and the encoded elements
(`tupleStr`; without `T` for BDH, `bdhStr`). The experiments are games of the `Games` framework
(`Games.ProbComp`): the generator's coins are drawn first, then `g`, the exponents and `T` from
the group they describe, then the adversary's coins. Sampling in sequence keeps the law of the
group the generator's law (a uniform seed over a dependent sum would not; run-3 audit P8-1 of
the DDH layer).

**Deviation:** [BB04, Definition 3.1] is concrete ("no `t`-time algorithm has advantage at least
`ε` in `G`"). Here the assumptions are asymptotic: every non-uniform PPT has negligible advantage
(BDH: success probability), relative to the generator. The decision advantage is the absolute
difference of acceptance probabilities; the paper writes the absolute difference of the
probabilities of output `0` [BB04, §3.1], which is the same number, since outputs `0` and `1` are
complementary. The adversary receives the group's description `d` and `1^κ`.

## Main definitions

* `TCSlib.Cryptography.Pairing.tupleStr`, `bdhStr` — the strings handed to the adversary.
* `BilinearGen.dbdhGame`, `BilinearGen.dbdhAdv`, `BilinearGen.DBDHAssumption` — the Decision BDH
  experiment, its advantage and the assumption [BB04, §3.1 and Definition 3.1].
* `BilinearGen.bdhGame`, `BilinearGen.BDHAssumption` — the BDH experiment and the assumption
  [BB04, §3.1 and Definition 3.1].

## Main results

* `BilinearGen.bdhAssumption_of_dbdhAssumption` — Decision BDH implies BDH when the order is
  at least `2^κ` except with negligible probability.

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §3.1 (pp. 4–5): the BDH and
  Decision BDH problems, Definition 3.1.
* [Jou00] A. Joux, *A One Round Protocol for Tripartite Diffie–Hellman*, ANTS-IV, LNCS 1838,
  pp. 385–393, Springer, 2000. §5 (p. 392): "some Diffie–Hellman like problem and
  Diffie–Hellman like decision problem should be hard in order to get security".
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Definition 26.8, non-uniform PPT; Definition 69.4's convention that `A` receives `1^n`.)
-/

namespace TCSlib.Cryptography.Pairing

open Complexity Turing TCSlib.Cryptography.Games

/-- The **Decision BDH string** `⟨d, ⟨g, ⟨X, ⟨Y, ⟨Z, T⟩⟩⟩⟩⟩` of a description `d`, four elements
`g, X, Y, Z` of `G` and an element `T` of `G_T`, each written by its encoding. It is the input
`(g, g^a, g^b, g^c, T)` of a Decision BDH algorithm [BB04, §3.1], with the group's description
in front. -/
def tupleStr {wG wT : ℕ} (B : BilinearGroup wG wT) (d : List Bool) (g x y z : B.G) (t : B.GT) :
    List Bool :=
  pairEncode d (pairEncode (List.ofFn (B.encG g)) (pairEncode (List.ofFn (B.encG x))
    (pairEncode (List.ofFn (B.encG y)) (pairEncode (List.ofFn (B.encG z))
      (List.ofFn (B.encT t))))))

/-- `tupleStr B d g x y z t = ⟨d, ⟨g, ⟨x, ⟨y, ⟨z, t⟩⟩⟩⟩⟩` with the elements encoded. -/
theorem tupleStr_eq {wG wT : ℕ} (B : BilinearGroup wG wT) (d : List Bool) (g x y z : B.G)
    (t : B.GT) :
    tupleStr B d g x y z t =
      pairEncode d (pairEncode (List.ofFn (B.encG g)) (pairEncode (List.ofFn (B.encG x))
        (pairEncode (List.ofFn (B.encG y)) (pairEncode (List.ofFn (B.encG z))
          (List.ofFn (B.encT t)))))) := rfl

/-- The **BDH string** `⟨d, ⟨g, ⟨X, ⟨Y, Z⟩⟩⟩⟩`: the input `(g, g^a, g^b, g^c)` of a BDH algorithm
[BB04, §3.1], with the group's description in front. -/
def bdhStr {wG wT : ℕ} (B : BilinearGroup wG wT) (d : List Bool) (g x y z : B.G) : List Bool :=
  pairEncode d (pairEncode (List.ofFn (B.encG g)) (pairEncode (List.ofFn (B.encG x))
    (pairEncode (List.ofFn (B.encG y)) (List.ofFn (B.encG z)))))

/-- `bdhStr B d g x y z = ⟨d, ⟨g, ⟨x, ⟨y, z⟩⟩⟩⟩` with the elements encoded. -/
theorem bdhStr_eq {wG wT : ℕ} (B : BilinearGroup wG wT) (d : List Bool) (g x y z : B.G) :
    bdhStr B d g x y z =
      pairEncode d (pairEncode (List.ofFn (B.encG g)) (pairEncode (List.ofFn (B.encG x))
        (pairEncode (List.ofFn (B.encG y)) (List.ofFn (B.encG z))))) := rfl

namespace BilinearGen

variable (G : BilinearGen)

/-- **The Decision BDH experiment** [BB04, §3.1] for the distinguisher `D` at parameter `κ`:
draw the generator's coins `r` (group `B = G.inst κ r`, description `d`), a generator
`g ∈ G^*`, exponents `a, b, c ∈ Z_p`, an element `T ∈ G_T` and `D`'s coins `ρ`, all uniform, and
return `D(1^κ, ⟨d, ⟨g, g^a, g^b, g^c, T'⟩⟩; ρ)`, where `T' = e(g, g)^{abc}` when `real` (the
distribution `P_BDH`) and `T' = T` otherwise (`R_BDH`). -/
noncomputable def dbdhGame (D : NUPPT) (real : Bool) (κ : ℕ) : ProbComp Bool :=
  (ProbComp.sample (G.gen.Coins κ)).bind fun r =>
  (ProbComp.sample {x : (G.inst κ r).G // x ≠ 1}).bind fun g =>
  (ProbComp.sample (ZMod (G.inst κ r).order × ZMod (G.inst κ r).order ×
    ZMod (G.inst κ r).order)).bind fun abc =>
  (ProbComp.sample (G.inst κ r).GT).bind fun t =>
  (ProbComp.sample (D.Coins κ)).bind fun ρ =>
    .pure (D.distinguisherL κ (tupleStr (G.inst κ r) (G.desc κ r) g.1 (g.1 ^ abc.1.val)
      (g.1 ^ abc.2.1.val) (g.1 ^ abc.2.2.val)
      (if real then (G.inst κ r).pair g.1 g.1 ^ (abc.1 * abc.2.1 * abc.2.2).val else t)) ρ)

/-- The Decision BDH experiment draws the generator's coins, `g ∈ G^*`, `(a, b, c) ∈ Z_p³`,
`T ∈ G_T` and the distinguisher's coins, and runs the distinguisher on
`tupleStr B d g g^a g^b g^c T'` with `T' = e(g, g)^{abc}` if `real` and `T' = T` otherwise. -/
theorem dbdhGame_eq (D : NUPPT) (real : Bool) (κ : ℕ) :
    G.dbdhGame D real κ =
      (ProbComp.sample (G.gen.Coins κ)).bind fun r =>
      (ProbComp.sample {x : (G.inst κ r).G // x ≠ 1}).bind fun g =>
      (ProbComp.sample (ZMod (G.inst κ r).order × ZMod (G.inst κ r).order ×
        ZMod (G.inst κ r).order)).bind fun abc =>
      (ProbComp.sample (G.inst κ r).GT).bind fun t =>
      (ProbComp.sample (D.Coins κ)).bind fun ρ =>
        .pure (D.distinguisherL κ (tupleStr (G.inst κ r) (G.desc κ r) g.1 (g.1 ^ abc.1.val)
          (g.1 ^ abc.2.1.val) (g.1 ^ abc.2.2.val)
          (if real then (G.inst κ r).pair g.1 g.1 ^ (abc.1 * abc.2.1 * abc.2.2).val else t)) ρ) :=
  rfl

/-- **The Decision BDH advantage** of `D` at `κ`:
`|Pr[D(P_BDH) = 1] − Pr[D(R_BDH) = 1]|` [BB04, §3.1]. -/
noncomputable def dbdhAdv (D : NUPPT) (κ : ℕ) : ℝ :=
  advantage (G.dbdhGame D false κ) (G.dbdhGame D true κ)

/-- `G.dbdhAdv D κ = advantage (G.dbdhGame D false κ) (G.dbdhGame D true κ)`. -/
theorem dbdhAdv_eq (D : NUPPT) (κ : ℕ) :
    G.dbdhAdv D κ = advantage (G.dbdhGame D false κ) (G.dbdhGame D true κ) := rfl

/-- **The Decision BDH assumption** relative to the generator `G` [BB04, §3.1 and
Definition 3.1]: every non-uniform PPT distinguisher has negligible Decision BDH advantage.

**Deviation:** asymptotic, relative to a generator, against non-uniform PPT machines that
receive `1^κ` and the description (module docstring). -/
def DBDHAssumption : Prop := ∀ D : NUPPT, Negligible fun κ => G.dbdhAdv D κ

/-- `G.DBDHAssumption` iff `κ ↦ G.dbdhAdv D κ` is negligible for every non-uniform PPT `D`. -/
theorem dbdhAssumption_iff : G.DBDHAssumption ↔ ∀ D : NUPPT, Negligible fun κ => G.dbdhAdv D κ :=
  Iff.rfl

/-- **The BDH experiment** [BB04, §3.1] for the machine `A` at parameter `κ`: draw the
generator's coins `r`, a generator `g ∈ G^*`, exponents `a, b, c ∈ Z_p` and `A`'s coins `ρ`, all
uniform, and accept iff `A(1^κ, ⟨d, ⟨g, g^a, g^b, g^c⟩⟩; ρ)` is the encoding of `e(g, g)^{abc}`. -/
noncomputable def bdhGame (A : NUPPT) (κ : ℕ) : ProbComp Bool :=
  (ProbComp.sample (G.gen.Coins κ)).bind fun r =>
  (ProbComp.sample {x : (G.inst κ r).G // x ≠ 1}).bind fun g =>
  (ProbComp.sample (ZMod (G.inst κ r).order × ZMod (G.inst κ r).order ×
    ZMod (G.inst κ r).order)).bind fun abc =>
  (ProbComp.sample (A.Coins κ)).bind fun ρ =>
    .pure (decide (A.runAt κ (bdhStr (G.inst κ r) (G.desc κ r) g.1 (g.1 ^ abc.1.val)
      (g.1 ^ abc.2.1.val) (g.1 ^ abc.2.2.val)) ρ =
        List.ofFn ((G.inst κ r).encT
          ((G.inst κ r).pair g.1 g.1 ^ (abc.1 * abc.2.1 * abc.2.2).val))))

/-- The BDH experiment draws the generator's coins, `g ∈ G^*`, `(a, b, c) ∈ Z_p³` and the
machine's coins, and accepts iff the machine's output on `bdhStr B d g g^a g^b g^c` is the
encoding of `e(g, g)^{abc}`. -/
theorem bdhGame_eq (A : NUPPT) (κ : ℕ) :
    G.bdhGame A κ =
      (ProbComp.sample (G.gen.Coins κ)).bind fun r =>
      (ProbComp.sample {x : (G.inst κ r).G // x ≠ 1}).bind fun g =>
      (ProbComp.sample (ZMod (G.inst κ r).order × ZMod (G.inst κ r).order ×
        ZMod (G.inst κ r).order)).bind fun abc =>
      (ProbComp.sample (A.Coins κ)).bind fun ρ =>
        .pure (decide (A.runAt κ (bdhStr (G.inst κ r) (G.desc κ r) g.1 (g.1 ^ abc.1.val)
          (g.1 ^ abc.2.1.val) (g.1 ^ abc.2.2.val)) ρ =
            List.ofFn ((G.inst κ r).encT
              ((G.inst κ r).pair g.1 g.1 ^ (abc.1 * abc.2.1 * abc.2.2).val)))) :=
  rfl

/-- **The BDH assumption** relative to the generator `G` [BB04, §3.1 and Definition 3.1]: every
non-uniform PPT machine solves the BDH problem with negligible probability.

**Deviation:** asymptotic, relative to a generator, against non-uniform PPT machines that
receive `1^κ` and the description; the answer must be the encoding of `e(g, g)^{abc}` exactly. -/
def BDHAssumption : Prop := ∀ A : NUPPT, Negligible fun κ => accept (G.bdhGame A κ)

/-- `G.BDHAssumption` iff `κ ↦ Pr[G.bdhGame A κ = 1]` is negligible for every non-uniform
PPT `A`. -/
theorem bdhAssumption_iff :
    G.BDHAssumption ↔ ∀ A : NUPPT, Negligible fun κ => accept (G.bdhGame A κ) := Iff.rfl

/-- **Decision BDH implies BDH** when the group order is at least `2^κ` except with negligible
probability: a BDH solver `A` gives the Decision BDH distinguisher "run `A` on `(g, g^a, g^b, g^c)`
and accept iff its answer is `T`".

**Source:** not stated in [BB04] or [Jou00], which define the two problems ([BB04, §3.1]). The
implication is independently derived here: the folklore fact that deciding is no harder than
computing.

**Proof sketch.** Given `A`, let `D(1^κ, ⟨s, T⟩)` run `A(1^κ, s)` with its own coins and accept
iff the answer equals the encoding of `T`, where `s` is re-paired from the first five components
(a polynomial-time string map, so `D` is a non-uniform PPT). On `P_BDH`, `D` accepts exactly when
`A` succeeds, so `Pr[D(P_BDH) = 1] = Pr[A wins]`. On `R_BDH`, `T` is uniform in `G_T` and
independent of `A`'s view, so `Pr[D(R_BDH) = 1] ≤ 1/p` by injectivity of the encoding. Hence
`Pr[A wins] ≤ dbdhAdv D κ + E_r[1/p] ≤ dbdhAdv D κ + 2^{-κ} + δ(κ)` (the coins where `p < 2^κ`
cost at most `δ(κ)`), a sum of negligible functions. -/
theorem bdhAssumption_of_dbdhAssumption
    (hN : ∃ δ : ℕ → ℝ, Negligible δ ∧ G.OrderAtLeastExcept (fun κ => 2 ^ κ) δ)
    (h : G.DBDHAssumption) : G.BDHAssumption := by
  sorry

end BilinearGen

end TCSlib.Cryptography.Pairing
```

## ===== TCSlib/Cryptography/Pairing/Operations.lean (Lean, at 9e7a96481785d6cac4dea3b2e990c49ac278b060) =====

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Pairing.Group
import TCSlib.Cryptography.Candidates.Arithmetic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Efficient group operations of a bilinear group generator

[BB04, §2.2]: "`G` is a bilinear group if the group action in `G` can be computed efficiently and
there exists a group `G_1` and an efficiently computable bilinear map `e`". A `BilinearGen` keeps
its groups abstract (`Pairing/Group.lean`); this file states the efficiency half of the
definition as a separate contract, `BilinearGen.Ops`: polynomial-time string functions that, on
every generated description `d`, compute on the encodings of the elements of the group `d`
describes.

The contract is a hypothesis only of the results whose reductions compute in the group (the
security of BB1, `AdvancedEncryption.IdentityBased.bb1_sidSecure`). It reads exponents and the
order as binary numerals with `NumberTheory.listToNat`, the convention of the arithmetic bundle
`Candidates.ArithmeticFP` (D11), so that a reduction can do its exponent arithmetic modulo `p`
with that bundle.

## Main definitions

* `TCSlib.Cryptography.Pairing.BilinearGen.Ops` — the order, multiplication and exponentiation in
  `G`, the pairing, multiplication in `G_T` and the membership test of `G_T`, as polynomial-time
  string functions with their specifications at generated descriptions.

## Main results

None: the contract is a hypothesis, read through its fields.

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §2.2 (p. 4).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Definition 23.5, polynomial-time computation.)
-/

namespace TCSlib.Cryptography.Pairing

open Complexity Turing TCSlib.Cryptography.NumberTheory

namespace BilinearGen

/-- **Efficient operations of a bilinear group generator** [BB04, §2.2, "the group action in `G`
can be computed efficiently … an efficiently computable bilinear map `e`"]: polynomial-time
string functions that, on every generated description `d = G.desc κ r` and the encodings of
elements `x, y ∈ G`, `u, v ∈ G_T`, compute
* the order `p`, as a binary numeral (`orderStr d`);
* `x · y` from `⟨d, ⟨x, y⟩⟩` (`mulG`) and `x^n` from `⟨d, ⟨x, n⟩⟩` for any numeral `n` (`powG`);
* `e(x, y)` from `⟨d, ⟨x, y⟩⟩` (`pairStr`);
* `u · v` from `⟨d, ⟨u, v⟩⟩` (`mulT`);
* whether a `wT(κ)`-bit string `w` encodes an element of `G_T`, from `⟨d, w⟩` (`memT`).

**Deviation:** the paper asks for efficient group operations and pairing; the order, the
membership test of `G_T` and numeral exponents are the minimal extras a machine needs to sample
exponents in `Z_p` and to read messages of `G_T` sent by an adversary. Inputs that are not of
these forms are unconstrained. Inversion is `x^{p−1}`. -/
structure Ops (G : BilinearGen) where
  /-- The order `p` of the described group, as a binary numeral. -/
  orderStr : List Bool → List Bool
  /-- Multiplication in `G` on `⟨d, ⟨x, y⟩⟩`. -/
  mulG : List Bool → List Bool
  /-- Exponentiation in `G` on `⟨d, ⟨x, n⟩⟩`, `n` a binary numeral. -/
  powG : List Bool → List Bool
  /-- The pairing on `⟨d, ⟨x, y⟩⟩`. -/
  pairStr : List Bool → List Bool
  /-- Multiplication in `G_T` on `⟨d, ⟨u, v⟩⟩`. -/
  mulT : List Bool → List Bool
  /-- The membership test of `G_T` on `⟨d, w⟩`. -/
  memT : List Bool → List Bool
  /-- `orderStr` is polynomial-time. -/
  orderStr_poly : PolyTimeComputable orderStr
  /-- `mulG` is polynomial-time. -/
  mulG_poly : PolyTimeComputable mulG
  /-- `powG` is polynomial-time. -/
  powG_poly : PolyTimeComputable powG
  /-- `pairStr` is polynomial-time. -/
  pairStr_poly : PolyTimeComputable pairStr
  /-- `mulT` is polynomial-time. -/
  mulT_poly : PolyTimeComputable mulT
  /-- `memT` is polynomial-time. -/
  memT_poly : PolyTimeComputable memT
  /-- `orderStr d` reads as the order of the described group. -/
  orderStr_spec : ∀ κ (r : G.gen.Coins κ), listToNat (orderStr (G.desc κ r)) = (G.inst κ r).order
  /-- `mulG ⟨d, ⟨x, y⟩⟩` is the encoding of `x · y`. -/
  mulG_spec : ∀ κ (r : G.gen.Coins κ) (x y : (G.inst κ r).G),
    mulG (pairEncode (G.desc κ r) (pairEncode (List.ofFn ((G.inst κ r).encG x))
      (List.ofFn ((G.inst κ r).encG y)))) = List.ofFn ((G.inst κ r).encG (x * y))
  /-- `powG ⟨d, ⟨x, n⟩⟩` is the encoding of `x^n`, `n` read as a binary numeral. -/
  powG_spec : ∀ κ (r : G.gen.Coins κ) (x : (G.inst κ r).G) (n : List Bool),
    powG (pairEncode (G.desc κ r) (pairEncode (List.ofFn ((G.inst κ r).encG x)) n)) =
      List.ofFn ((G.inst κ r).encG (x ^ listToNat n))
  /-- `pairStr ⟨d, ⟨x, y⟩⟩` is the encoding of `e(x, y)`. -/
  pairStr_spec : ∀ κ (r : G.gen.Coins κ) (x y : (G.inst κ r).G),
    pairStr (pairEncode (G.desc κ r) (pairEncode (List.ofFn ((G.inst κ r).encG x))
      (List.ofFn ((G.inst κ r).encG y)))) = List.ofFn ((G.inst κ r).encT ((G.inst κ r).pair x y))
  /-- `mulT ⟨d, ⟨u, v⟩⟩` is the encoding of `u · v`. -/
  mulT_spec : ∀ κ (r : G.gen.Coins κ) (u v : (G.inst κ r).GT),
    mulT (pairEncode (G.desc κ r) (pairEncode (List.ofFn ((G.inst κ r).encT u))
      (List.ofFn ((G.inst κ r).encT v)))) = List.ofFn ((G.inst κ r).encT (u * v))
  /-- `memT ⟨d, w⟩` is `[true]` iff `w` encodes an element of `G_T`, and `[false]` otherwise. -/
  memT_spec : ∀ κ (r : G.gen.Coins κ) (w : Fin (G.wT.eval κ) → Bool),
    memT (pairEncode (G.desc κ r) (List.ofFn w)) = [decide (∃ u, (G.inst κ r).encT u = w)]

end BilinearGen

end TCSlib.Cryptography.Pairing
```

## ===== TCSlib/Cryptography/KeyExchange/Joux.lean (Lean, at 9e7a96481785d6cac4dea3b2e990c49ac278b060) =====

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Pairing.Assumptions

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Joux's one-round tripartite Diffie–Hellman

[Jou00, §3]: three participants `A`, `B`, `C` share a group with a pairing and a public point.
Each picks a random exponent (`a`, `b`, `c`), broadcasts the multiple of the point once (one round,
`P_A = aP`, `P_B = bP`, `P_C = cP`), and computes the common key with
`F(x, P, Q) = e(P, Q)^x`: `K = F(a, P_B, P_C) = F(b, P_A, P_C) = F(c, P_A, P_B) = F(1, P, P)^{abc}`
[Jou00, p. 388]. In multiplicative notation, with the generator `g`: the messages are `g^a`,
`g^b`, `g^c`, and each key is `e(g^b, g^c)^a = e(g^a, g^c)^b = e(g^a, g^b)^c = e(g, g)^{abc}`.

**The single-point form.** [Jou00, §3] notes that with the Weil pairing on one point
`e_n(P, P) = 1`, so the key would be constant, and therefore uses two independent points `P`, `Q`
and the Tate pairing. In a symmetric bilinear group as defined in [BB04, §2.2], non-degeneracy is
`e(g, g) ≠ 1`, so the paper's first formula `F_W(x, P, Q) = e(P, Q)^x` already gives a
non-constant key, and one point suffices. This file formalizes that single-point form over the
abstract groups of `Pairing.BilinearGroup`.

**Security.** [Jou00, §5] gives no theorem; it says that "some Diffie–Hellman like problem and
Diffie–Hellman like decision problem should be hard in order to get security". The key
indistinguishability theorem here takes that decision problem to be Decision BDH [BB04, §3.1]:
an eavesdropper who sees the public point and the three broadcasts cannot tell the common key
from a uniform element of `G_T`.

**Deviation:** abstract symmetric bilinear groups (no curve, no Weil or Tate pairing); one public
point instead of two; multiplicative notation; the public point `g` is uniform in `G^*` (the
paper fixes "some point `P`"), the distribution under which [BB04, §3.1] states Decision BDH;
exponents in `Z_p`; security is the maintainer's formalization of [Jou00, §5]'s remark.

## Main definitions

* `TCSlib.Cryptography.KeyExchange.jouxMsg` — a participant's broadcast `g^x`.
* `TCSlib.Cryptography.KeyExchange.jouxKey` — the key `F(x, X, Y) = e(X, Y)^x`.
* `jouxGame`, `jouxAdv`, `JouxKeyIndist` — key indistinguishability for an eavesdropper.

## Main results

* `TCSlib.Cryptography.KeyExchange.jouxKey_eq` — every participant's key is `e(g, g)^{abc}`.
* `TCSlib.Cryptography.KeyExchange.joux_correct` — the three participants agree.
* `TCSlib.Cryptography.KeyExchange.jouxGame_eq_dbdhGame` — the eavesdropper's experiments are
  Decision BDH experiments.
* `TCSlib.Cryptography.KeyExchange.jouxKeyIndist_of_dbdhAssumption` — key indistinguishability
  under Decision BDH.

## References

* [Jou00] A. Joux, *A One Round Protocol for Tripartite Diffie–Hellman*, ANTS-IV, LNCS 1838,
  pp. 385–393, Springer, 2000. §3 (pp. 387–388): the protocol and `F_W`; §5 (pp. 391–392):
  security issues.
* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §2.2 (bilinear groups), §3.1
  (Decision BDH).
-/

namespace TCSlib.Cryptography.KeyExchange

open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing

variable {wG wT : ℕ} (B : BilinearGroup wG wT)

/-- **A participant's broadcast** [Jou00, §3, `P_A = aP`]: the power `g^x` of the public
generator `g` by the participant's secret exponent `x ∈ Z_p`. -/
def jouxMsg (g : B.G) (x : ZMod B.order) : B.G := g ^ x.val

/-- `jouxMsg B g x = g ^ x.val`. -/
theorem jouxMsg_eq (g : B.G) (x : ZMod B.order) : jouxMsg B g x = g ^ x.val := rfl

/-- **A participant's key** [Jou00, §3, `F_W(x, P, Q) = e_n(P, Q)^x`]: from its secret exponent
`x` and the two other broadcasts `X`, `Y`, the key `e(X, Y)^x`. Participant `A` computes
`jouxKey B a P_B P_C`, `B` computes `jouxKey B b P_A P_C`, `C` computes `jouxKey B c P_A P_B`. -/
def jouxKey (x : ZMod B.order) (X Y : B.G) : B.GT := B.pair X Y ^ x.val

/-- `jouxKey B x X Y = e(X, Y) ^ x.val`. -/
theorem jouxKey_eq_pow (x : ZMod B.order) (X Y : B.G) : jouxKey B x X Y = B.pair X Y ^ x.val :=
  rfl

/-- Exponents of `G_T` multiply through `Z_p`: `u^{(abc mod p)} = u^{a b c}` with the
representatives `a.val, b.val, c.val`. -/
theorem pow_val_mul_mul (u : B.GT) (a b c : ZMod B.order) :
    u ^ (a * b * c).val = u ^ (a.val * b.val * c.val) := by
  rw [B.pow_val_mul_GT, pow_mul, B.pow_val_mul_GT, ← pow_mul]

/-- **The common key** [Jou00, p. 388, `F_W(a, P_B, P_C) = F_W(1, P, P)^{abc}`]: participant `A`'s
key `e(g^b, g^c)^a` is `e(g, g)^{abc}`. -/
theorem jouxKey_eq (g : B.G) (a b c : ZMod B.order) :
    jouxKey B a (jouxMsg B g b) (jouxMsg B g c) = B.pair g g ^ (a * b * c).val := by
  rw [jouxKey_eq_pow, jouxMsg_eq, jouxMsg_eq, B.bilinear_pow, pow_val_mul_mul, ← pow_mul]
  congr 1
  ring

/-- **Correctness: the three participants agree** [Jou00, p. 388,
`F_W(a, P_B, P_C) = F_W(b, P_A, P_C) = F_W(c, P_A, P_B)`]: `e(g^b, g^c)^a = e(g^a, g^c)^b` and
`e(g^a, g^c)^b = e(g^a, g^b)^c`. -/
theorem joux_correct (g : B.G) (a b c : ZMod B.order) :
    jouxKey B a (jouxMsg B g b) (jouxMsg B g c) = jouxKey B b (jouxMsg B g a) (jouxMsg B g c) ∧
      jouxKey B b (jouxMsg B g a) (jouxMsg B g c) =
        jouxKey B c (jouxMsg B g a) (jouxMsg B g b) := by
  refine ⟨?_, ?_⟩ <;> rw [jouxKey_eq, jouxKey_eq] <;> congr 2 <;> ring

/-- **The key-indistinguishability experiment** for the eavesdropper `A` at parameter `κ`: draw
the generator's coins `r` (group `B`, description `d`), the public generator `g ∈ G^*`, the
secret exponents `a, b, c ∈ Z_p`, a uniform `K ∈ G_T` and `A`'s coins `ρ`; give `A` the
description, the public generator, the three broadcasts and either the common key
`e(g^b, g^c)^a` (`real`) or `K`, in the string format of Decision BDH (`tupleStr`). -/
noncomputable def jouxGame (G : BilinearGen) (A : NUPPT) (real : Bool) (κ : ℕ) : ProbComp Bool :=
  (ProbComp.sample (G.gen.Coins κ)).bind fun r =>
  (ProbComp.sample {x : (G.inst κ r).G // x ≠ 1}).bind fun g =>
  (ProbComp.sample (ZMod (G.inst κ r).order × ZMod (G.inst κ r).order ×
    ZMod (G.inst κ r).order)).bind fun abc =>
  (ProbComp.sample (G.inst κ r).GT).bind fun K =>
  (ProbComp.sample (A.Coins κ)).bind fun ρ =>
    .pure (A.distinguisherL κ (tupleStr (G.inst κ r) (G.desc κ r) g.1
      (jouxMsg (G.inst κ r) g.1 abc.1) (jouxMsg (G.inst κ r) g.1 abc.2.1)
      (jouxMsg (G.inst κ r) g.1 abc.2.2)
      (if real then jouxKey (G.inst κ r) abc.1 (jouxMsg (G.inst κ r) g.1 abc.2.1)
        (jouxMsg (G.inst κ r) g.1 abc.2.2) else K)) ρ)

/-- The key-indistinguishability experiment draws the generator's coins, `g ∈ G^*`,
`(a, b, c) ∈ Z_p³`, `K ∈ G_T` and the eavesdropper's coins, and runs the eavesdropper on the
transcript `g, g^a, g^b, g^c` with `A`'s key if `real` and `K` otherwise. -/
theorem jouxGame_eq (G : BilinearGen) (A : NUPPT) (real : Bool) (κ : ℕ) :
    jouxGame G A real κ =
      (ProbComp.sample (G.gen.Coins κ)).bind fun r =>
      (ProbComp.sample {x : (G.inst κ r).G // x ≠ 1}).bind fun g =>
      (ProbComp.sample (ZMod (G.inst κ r).order × ZMod (G.inst κ r).order ×
        ZMod (G.inst κ r).order)).bind fun abc =>
      (ProbComp.sample (G.inst κ r).GT).bind fun K =>
      (ProbComp.sample (A.Coins κ)).bind fun ρ =>
        .pure (A.distinguisherL κ (tupleStr (G.inst κ r) (G.desc κ r) g.1
          (jouxMsg (G.inst κ r) g.1 abc.1) (jouxMsg (G.inst κ r) g.1 abc.2.1)
          (jouxMsg (G.inst κ r) g.1 abc.2.2)
          (if real then jouxKey (G.inst κ r) abc.1 (jouxMsg (G.inst κ r) g.1 abc.2.1)
            (jouxMsg (G.inst κ r) g.1 abc.2.2) else K)) ρ) :=
  rfl

/-- **Each key-indistinguishability experiment is a Decision BDH experiment**: with the key
`e(g^b, g^c)^a = e(g, g)^{abc}` (`jouxKey_eq`) the transcript and key are drawn from `P_BDH`, and
with a uniform `K` from `R_BDH`, in the same string format, so
`jouxGame G A real κ = G.dbdhGame A real κ`. -/
theorem jouxGame_eq_dbdhGame (G : BilinearGen) (A : NUPPT) (real : Bool) (κ : ℕ) :
    jouxGame G A real κ = G.dbdhGame A real κ := by
  rw [jouxGame_eq, BilinearGen.dbdhGame_eq]
  simp only [jouxKey_eq]
  rfl

/-- **The eavesdropper's advantage** at `κ`: `|Pr[A(transcript, K) = 1] − Pr[A(transcript,
key) = 1]|`. -/
noncomputable def jouxAdv (G : BilinearGen) (A : NUPPT) (κ : ℕ) : ℝ :=
  advantage (jouxGame G A false κ) (jouxGame G A true κ)

/-- `jouxAdv G A κ = advantage (jouxGame G A false κ) (jouxGame G A true κ)`. -/
theorem jouxAdv_eq (G : BilinearGen) (A : NUPPT) (κ : ℕ) :
    jouxAdv G A κ = advantage (jouxGame G A false κ) (jouxGame G A true κ) := rfl

/-- **Key indistinguishability of Joux's protocol** relative to the generator `G`: every
non-uniform PPT eavesdropper has negligible advantage in telling the common key from a uniform
element of `G_T`, given the public generator and the three broadcasts. The security goal of
[Jou00, §3] ("this common value `K_{A,B,C}` will be hard to compute given `P_A`, `P_B` and `P_C`"),
in its decisional form [Jou00, §5]. -/
def JouxKeyIndist (G : BilinearGen) : Prop := ∀ A : NUPPT, Negligible fun κ => jouxAdv G A κ

/-- `JouxKeyIndist G` iff `κ ↦ jouxAdv G A κ` is negligible for every non-uniform PPT `A`. -/
theorem jouxKeyIndist_iff (G : BilinearGen) :
    JouxKeyIndist G ↔ ∀ A : NUPPT, Negligible fun κ => jouxAdv G A κ := Iff.rfl

/-- **Joux's protocol has indistinguishable keys under Decision BDH** ([Jou00, §5] with the
decision problem of [BB04, §3.1]).

**Source:** [Jou00] states no theorem; this is the formal version of its §5 requirement
(module docstring).

The eavesdropper is itself the Decision BDH distinguisher: `jouxAdv G A κ = G.dbdhAdv A κ`
(`jouxGame_eq_dbdhGame`). -/
theorem jouxKeyIndist_of_dbdhAssumption (G : BilinearGen) (h : G.DBDHAssumption) :
    JouxKeyIndist G := by
  intro A
  have hfun : (fun κ => jouxAdv G A κ) = fun κ => G.dbdhAdv A κ := funext fun κ => by
    rw [jouxAdv_eq, BilinearGen.dbdhAdv_eq, jouxGame_eq_dbdhGame, jouxGame_eq_dbdhGame]
  rw [hfun]
  exact G.dbdhAssumption_iff.1 h A

end TCSlib.Cryptography.KeyExchange
```

## ===== TCSlib/Cryptography/AdvancedEncryption/IdentityBased/Defs.lean (Lean, at 9e7a96481785d6cac4dea3b2e990c49ac278b060) =====

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Encryption.PrivateKey.OracleSecurity
import TCSlib.Cryptography.Games.Machines

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Identity-based encryption and selective-identity security

An *identity-based encryption* (IBE) system [BB04, §2.1] consists of four algorithms: `Setup`
generates the system parameters `params` and a master key; `KeyGen` uses the master key to
generate the private key `d_ID` of an identity `ID`; `Encrypt` encrypts a message for an identity
using the parameters; `Decrypt` decrypts with a private key.

*Selective-identity chosen-plaintext security* (IND-sID-CPA, [BB04, §2.1, the game and
Definition 2.2]): the adversary first commits to the identity `ID*` it will attack (**Init**);
the challenger runs `Setup` and gives it `params` (**Setup**); the adversary adaptively asks for
the private keys of identities `ID ≠ ID*` (**Phase 1**); it outputs two messages `M₀, M₁` of the
message space and receives `Encrypt(params, ID*, M_b)` (**Challenge**); it asks more private-key
queries (**Phase 2**) and outputs a guess `b'` (**Guess**). There are no decryption queries.

**The scheme interface.** The algorithms are probabilistic computations of the `Games` framework
over typed parameters, keys and ciphertexts (`IBEScheme`). Identities are `idLen(κ)`-bit strings
and messages arrive as `msgLen(κ)`-bit strings; a scheme declares which strings are messages for
given parameters (`MsgSpace`, the paper's message space `M`). For the adversary, parameters,
private keys and ciphertexts are written as fixed-width strings (`encPP`, `encSK`, `encCT`),
injective on the objects the algorithms can output (`encPP_inj`, `encSK_inj`, `encCT_inj`).

**The game's encoding.** As in the public-key games (`Encryption.PublicKey.OracleSecurity`), one
non-uniform PPT machine plays every phase against bit-string oracles (`Games.bitCodec`):
* `Init` (oracle 0) takes `ID*` and answers `params`. The first query fixes `ID*`; later queries
  repeat `params` and leave `ID*` unchanged.
* `KeyGen` (oracle 1) takes `ID` and answers `⟨1, d_ID⟩` with fresh `KeyGen` coins when `ID*` is
  fixed and `ID ≠ ID*`, and `⊥` (all `false`) otherwise.
* `Challenge` (oracle 2) takes `⟨M₀, M₁⟩` and answers `Encrypt(params, ID*, M_b)` the first time
  it is asked with `ID*` fixed and `M₀, M₁ ∈ M`, recording it; later it repeats the recorded
  challenge; it answers `⊥` before `Init` and on messages outside `M`.
The machine starts with input `1^κ` only, so the only information it has before committing is
its coins. `Setup` is run before the machine starts; since nothing about `params` reaches the
machine before its `Init` query, this is the order of [BB04, §2.1] in distribution.

**Deviation:** [BB04, Definition 2.2] is concrete (`(t, q_ID, ε)`) and measures
`|Pr[b = b'] − 1/2|`; here security is asymptotic, for every non-uniform PPT and every polynomial
query budget, and the advantage is `|Pr[b' = 1 | b = 0] − Pr[b' = 1 | b = 1]|`, twice the
paper's (`Games.guessAdv_eq_half_advantage`). Queries to `KeyGen` for `ID*` and challenges outside
`M` are answered `⊥` instead of being forbidden. The algorithms are typed probabilistic
computations; their efficiency is not part of the interface (per-scheme contracts).

## Main definitions

* `TCSlib.Cryptography.AdvancedEncryption.IdentityBased.IBEScheme` — an IBE system [BB04, §2.1].
* `IBEScheme.Correct` — perfect correctness on the message space.
* `IBEScheme.sidSpec`, `IBEScheme.sidImpl`, `IBEScheme.sidGame`, `IBEScheme.SIDSecure` — the
  IND-sID-CPA game and security [BB04, §2.1 and Definition 2.2].
* `IBEScheme.oracleImpl` — the three oracles from typed handlers (for simulators).

## Main results

* `IBEScheme.sidImpl_init_none`, `sidImpl_init_some`, `sidImpl_keyGen_none`,
  `sidImpl_keyGen_target`, `sidImpl_keyGen_ne`, `sidImpl_challenge_none`,
  `sidImpl_challenge_repeat`, `sidImpl_challenge_fresh`, `sidImpl_challenge_invalid` — the
  oracles case by case; `oracleImpl_zero`, `oracleImpl_one`, `oracleImpl_two`.
* `IBEScheme.honestRun_eq`, `correct_iff`, `sidGame_eq`, `sidSecure_iff` — the experiments and
  predicates through their published equations.

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §2.1 (pp. 2–4): IBE systems, the
  selective identity game, Definitions 2.1 and 2.2.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Definition 26.8, non-uniform PPT; the one-machine encoding of the games of §7.1.4.)
-/

namespace TCSlib.Cryptography.AdvancedEncryption.IdentityBased

open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Composability

/-- An **identity-based encryption system** [BB04, §2.1]: at each security parameter `κ`, types of
system parameters `PP κ`, master keys `MSK κ`, private keys `SK κ` and ciphertexts `CT κ`, and
* `setup κ`, a probabilistic computation of `(params, master-key)`;
* `keyGen κ msk ID`, a probabilistic computation of the private key `d_ID` of the `idLen(κ)`-bit
  identity `ID`;
* `enc κ params ID M`, a probabilistic computation of a ciphertext of the `msgLen(κ)`-bit message
  `M` for `ID`;
* `dec κ d_ID C`, the deterministic decryption, `none` for `⊥`;
* the message space `MsgSpace κ params` (the paper's `M`), and fixed-width encodings of
  parameters, private keys and ciphertexts for the adversary, which lose no information on the
  objects the algorithms can output (`encPP_inj`, `encSK_inj`, `encCT_inj`).

**Deviation:** messages are strings with a parameter-dependent message space (as for El Gamal,
`Candidates.GroupPKScheme`); the algorithms are typed probabilistic computations, without an
efficiency requirement in the interface. The adversary sees parameters, private keys and
ciphertexts only through their encodings; their fidelity is injectivity on reachable objects
(possible outputs of `setup`, and keys and ciphertexts under one possible output of `setup`), not
efficient decoding, and not injectivity on all of `PP κ`, `SK κ`, `CT κ` (an encoding may omit
data that the parameters fix). The efficiency of the encodings is deferred with that of the
algorithms (ruling Q5 of `PairingCryptographyPlan.md`). -/
structure IBEScheme where
  /-- The identity length. -/
  idLen : PolyExpr
  /-- The message length. -/
  msgLen : PolyExpr
  /-- The width of encoded parameters. -/
  ppLen : PolyExpr
  /-- The width of encoded private keys. -/
  skLen : PolyExpr
  /-- The width of encoded ciphertexts. -/
  ctLen : PolyExpr
  /-- System parameters. -/
  PP : ℕ → Type
  /-- Master keys. -/
  MSK : ℕ → Type
  /-- Private keys. -/
  SK : ℕ → Type
  /-- Ciphertexts. -/
  CT : ℕ → Type
  /-- `Setup`: system parameters and a master key. -/
  setup : (κ : ℕ) → ProbComp (PP κ × MSK κ)
  /-- `KeyGen`: the private key of an identity. -/
  keyGen : (κ : ℕ) → MSK κ → (Fin (idLen.eval κ) → Bool) → ProbComp (SK κ)
  /-- `Encrypt`: a ciphertext of a message for an identity. -/
  enc : (κ : ℕ) → PP κ → (Fin (idLen.eval κ) → Bool) → (Fin (msgLen.eval κ) → Bool) →
    ProbComp (CT κ)
  /-- `Decrypt`: the message of a ciphertext under a private key, or `⊥`. -/
  dec : (κ : ℕ) → SK κ → CT κ → Option (Fin (msgLen.eval κ) → Bool)
  /-- The message space for given parameters. -/
  MsgSpace : (κ : ℕ) → PP κ → (Fin (msgLen.eval κ) → Bool) → Prop
  /-- The encoding of parameters. -/
  encPP : (κ : ℕ) → PP κ → Fin (ppLen.eval κ) → Bool
  /-- The encoding of private keys. -/
  encSK : (κ : ℕ) → SK κ → Fin (skLen.eval κ) → Bool
  /-- The encoding of ciphertexts. -/
  encCT : (κ : ℕ) → CT κ → Fin (ctLen.eval κ) → Bool
  /-- **The parameter encoding is injective on reachable parameters**: two parameters output by
  `setup κ` with equal encodings are equal. With `encSK_inj` and `encCT_inj`, the adversary's
  wire view loses no information about the objects it is given [BB04, §2.1: the adversary
  receives `params`, the private keys `d_i` and the challenge ciphertext `C`]. -/
  encPP_inj : ∀ κ, (setup κ).AllOutputs fun k => (setup κ).AllOutputs fun k' =>
    encPP κ k.1 = encPP κ k'.1 → k.1 = k'.1
  /-- **The private-key encoding is injective on reachable keys**: for every possible output
  `(params, master-key)` of `setup κ`, two private keys output by `keyGen` with that master key,
  for any identities, with equal encodings are equal [BB04, §2.1, the adversary's view]. -/
  encSK_inj : ∀ κ, (setup κ).AllOutputs fun k => ∀ id id',
    (keyGen κ k.2 id).AllOutputs fun d => (keyGen κ k.2 id').AllOutputs fun d' =>
      encSK κ d = encSK κ d' → d = d'
  /-- **The ciphertext encoding is injective on reachable ciphertexts**: for every possible output
  of `setup κ`, two ciphertexts output by `enc` with its parameters, for any identities and
  messages, with equal encodings are equal [BB04, §2.1, the adversary's view]. -/
  encCT_inj : ∀ κ, (setup κ).AllOutputs fun k => ∀ id id' m m',
    (enc κ k.1 id m).AllOutputs fun c => (enc κ k.1 id' m').AllOutputs fun c' =>
      encCT κ c = encCT κ c' → c = c'

namespace IBEScheme

variable (S : IBEScheme)

/-- One honest run for the identity `ID` and the message `M`: `Setup`, then `KeyGen` for `ID`
and `Encrypt(params, ID, M)`, returning the parameters, the private key and the ciphertext. -/
noncomputable def honestRun (κ : ℕ) (id : Fin (S.idLen.eval κ) → Bool)
    (m : Fin (S.msgLen.eval κ) → Bool) : ProbComp (S.PP κ × S.SK κ × S.CT κ) :=
  (S.setup κ).bind fun k =>
  (S.keyGen κ k.2 id).bind fun sk =>
  (S.enc κ k.1 id m).bind fun c => .pure (k.1, sk, c)

/-- `S.honestRun κ id m` runs `Setup`, `KeyGen` for `id` and `Encrypt` of `m` for `id`, and
returns `(params, d_id, C)`. -/
theorem honestRun_eq (κ : ℕ) (id : Fin (S.idLen.eval κ) → Bool)
    (m : Fin (S.msgLen.eval κ) → Bool) :
    S.honestRun κ id m =
      (S.setup κ).bind fun k =>
      (S.keyGen κ k.2 id).bind fun sk =>
      (S.enc κ k.1 id m).bind fun c => .pure (k.1, sk, c) := rfl

/-- **Perfect correctness** [BB04, §2.1, "the decryption algorithm decrypts ciphertexts using the
private key"; §4.1's verification for BB1]: for every identity `ID` and every message `M`, every
possible outcome `(params, d_ID, C)` of an honest run with `M` in the message space of `params`
has `Decrypt(d_ID, C) = M`. -/
def Correct : Prop :=
  ∀ κ (id : Fin (S.idLen.eval κ) → Bool) (m : Fin (S.msgLen.eval κ) → Bool),
    (S.honestRun κ id m).AllOutputs fun x => S.MsgSpace κ x.1 m → S.dec κ x.2.1 x.2.2 = some m

/-- `S.Correct` iff every possible outcome of every honest run with a message of the message
space decrypts to that message. -/
theorem correct_iff :
    S.Correct ↔ ∀ κ (id : Fin (S.idLen.eval κ) → Bool) (m : Fin (S.msgLen.eval κ) → Bool),
      (S.honestRun κ id m).AllOutputs fun x =>
        S.MsgSpace κ x.1 m → S.dec κ x.2.1 x.2.2 = some m := Iff.rfl

/-! ### The selective-identity game -/

/-- The query lengths of the three oracles: `Init` and `KeyGen` take an identity, `Challenge`
takes two messages. -/
def inLens (κ : ℕ) : Fin 3 → ℕ
  | 0 => S.idLen.eval κ
  | 1 => S.idLen.eval κ
  | 2 => S.msgLen.eval κ + S.msgLen.eval κ

/-- `Init` queries are identities: `S.inLens κ 0 = S.idLen.eval κ`. -/
theorem inLens_zero (κ : ℕ) : S.inLens κ 0 = S.idLen.eval κ := rfl

/-- `KeyGen` queries are identities: `S.inLens κ 1 = S.idLen.eval κ`. -/
theorem inLens_one (κ : ℕ) : S.inLens κ 1 = S.idLen.eval κ := rfl

/-- `Challenge` queries are two messages: `S.inLens κ 2 = S.msgLen.eval κ + S.msgLen.eval κ`. -/
theorem inLens_two (κ : ℕ) : S.inLens κ 2 = S.msgLen.eval κ + S.msgLen.eval κ := rfl

/-- The answer lengths of the three oracles: `Init` answers the parameters, `KeyGen` a validity
bit and a private key, `Challenge` a ciphertext. -/
def outLens (κ : ℕ) : Fin 3 → ℕ
  | 0 => S.ppLen.eval κ
  | 1 => S.skLen.eval κ + 1
  | 2 => S.ctLen.eval κ

/-- `Init` answers parameters: `S.outLens κ 0 = S.ppLen.eval κ`. -/
theorem outLens_zero (κ : ℕ) : S.outLens κ 0 = S.ppLen.eval κ := rfl

/-- `KeyGen` answers a validity bit and a key: `S.outLens κ 1 = S.skLen.eval κ + 1`. -/
theorem outLens_one (κ : ℕ) : S.outLens κ 1 = S.skLen.eval κ + 1 := rfl

/-- `Challenge` answers a ciphertext: `S.outLens κ 2 = S.ctLen.eval κ`. -/
theorem outLens_two (κ : ℕ) : S.outLens κ 2 = S.ctLen.eval κ := rfl

/-- The three oracles of the IND-sID-CPA game at parameter `κ`. -/
abbrev sidSpec (κ : ℕ) : OracleSpec (Fin 3) := bitSpec (S.inLens κ) (S.outLens κ)

/-- The IND-sID-CPA oracle specification is the bit specification at the scheme's query and
answer lengths: `S.sidSpec κ = bitSpec (S.inLens κ) (S.outLens κ)`. -/
theorem sidSpec_eq (κ : ℕ) : S.sidSpec κ = bitSpec (S.inLens κ) (S.outLens κ) := rfl

/-- The state of the IND-sID-CPA game: the committed identity `ID*` (once `Init` is asked) and
the challenge ciphertext (once issued). -/
abbrev SidState (κ : ℕ) : Type :=
  Option (Fin (S.idLen.eval κ) → Bool) × Option (Fin (S.ctLen.eval κ) → Bool)

/-- The game state is the optional committed identity and the optional encoded challenge:
`S.SidState κ = Option (Fin (S.idLen.eval κ) → Bool) × Option (Fin (S.ctLen.eval κ) → Bool)`. -/
theorem sidState_eq (κ : ℕ) :
    S.SidState κ =
      (Option (Fin (S.idLen.eval κ) → Bool) × Option (Fin (S.ctLen.eval κ) → Bool)) := rfl

open Classical in
/-- **The oracles of the IND-sID-CPA game** [BB04, §2.1] with hidden bit `b`, at parameter `κ`,
for the parameters `pp` and the master key `msk`:
- `Init` on `ID`: answers `params`; records `ID*` = `ID` if none is recorded yet.
- `KeyGen` on `ID`: when `ID*` is recorded and `ID ≠ ID*`, answers `⟨1, d_ID⟩` with
  `d_ID ← KeyGen(msk, ID)`; otherwise `⊥`.
- `Challenge` on `⟨M₀, M₁⟩`: with `ID*` recorded and no challenge yet, if `M₀, M₁ ∈ M`, answers
  and records `C ← Encrypt(params, ID*, M_b)`, and otherwise `⊥`; once a challenge is recorded,
  repeats it; before `Init`, `⊥`. -/
noncomputable def sidImpl (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ) :
    QueryImpl (S.sidSpec κ) (S.SidState κ) unifSpec
  | 0, id, s =>
    match s.1 with
    | none => .pure (S.encPP κ pp, (some id, s.2))
    | some _ => .pure (S.encPP κ pp, s)
  | 1, id, s =>
    match s.1 with
    | some t =>
      if id = t then .pure (zeroBits _, s)
      else (S.keyGen κ msk id).bind fun sk =>
        .pure (FixedLengthScheme.decAnswer (some (S.encSK κ sk)), s)
    | none => .pure (zeroBits _, s)
  | 2, mm, s =>
    match s.1, s.2 with
    | some _, some c => .pure (c, s)
    | some t, none =>
      if S.MsgSpace κ pp (FixedLengthScheme.splitHalf mm).1 ∧
          S.MsgSpace κ pp (FixedLengthScheme.splitHalf mm).2 then
        (S.enc κ pp t (if b then (FixedLengthScheme.splitHalf mm).2
          else (FixedLengthScheme.splitHalf mm).1)).bind fun c =>
          .pure (S.encCT κ c, (some t, some (S.encCT κ c)))
      else .pure (zeroBits _, s)
    | none, _ => .pure (zeroBits _, s)

/-- `Init` before any commitment answers the parameters and records the identity. -/
theorem sidImpl_init_none (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (id : Fin (S.idLen.eval κ) → Bool) (c : Option (Fin (S.ctLen.eval κ) → Bool)) :
    S.sidImpl b κ pp msk 0 id (none, c) = .pure (S.encPP κ pp, (some id, c)) := rfl

/-- `Init` after a commitment answers the parameters and keeps the state. -/
theorem sidImpl_init_some (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (id t : Fin (S.idLen.eval κ) → Bool) (c : Option (Fin (S.ctLen.eval κ) → Bool)) :
    S.sidImpl b κ pp msk 0 id (some t, c) = .pure (S.encPP κ pp, (some t, c)) := rfl

/-- `KeyGen` before `Init` answers `⊥`. -/
theorem sidImpl_keyGen_none (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (id : Fin (S.idLen.eval κ) → Bool) (c : Option (Fin (S.ctLen.eval κ) → Bool)) :
    S.sidImpl b κ pp msk 1 id (none, c) = .pure (zeroBits _, (none, c)) := rfl

/-- `KeyGen` for the committed identity answers `⊥`. -/
theorem sidImpl_keyGen_target (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (t : Fin (S.idLen.eval κ) → Bool) (c : Option (Fin (S.ctLen.eval κ) → Bool)) :
    S.sidImpl b κ pp msk 1 t (some t, c) = .pure (zeroBits _, (some t, c)) := by
  simp [sidImpl]

/-- `KeyGen` for an identity other than the committed one answers `⟨1, d_ID⟩` with
`d_ID ← KeyGen(msk, ID)` and keeps the state. -/
theorem sidImpl_keyGen_ne (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (id t : Fin (S.idLen.eval κ) → Bool) (c : Option (Fin (S.ctLen.eval κ) → Bool))
    (h : id ≠ t) :
    S.sidImpl b κ pp msk 1 id (some t, c) =
      (S.keyGen κ msk id).bind fun sk =>
        .pure (FixedLengthScheme.decAnswer (some (S.encSK κ sk)), (some t, c)) := by
  simp [sidImpl, h]

/-- `Challenge` before `Init` answers `⊥`. -/
theorem sidImpl_challenge_none (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (mm : Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool)
    (c : Option (Fin (S.ctLen.eval κ) → Bool)) :
    S.sidImpl b κ pp msk 2 mm (none, c) = .pure (zeroBits _, (none, c)) := rfl

/-- `Challenge` after a recorded challenge repeats it. -/
theorem sidImpl_challenge_repeat (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (mm : Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) (t : Fin (S.idLen.eval κ) → Bool)
    (c : Fin (S.ctLen.eval κ) → Bool) :
    S.sidImpl b κ pp msk 2 mm (some t, some c) = .pure (c, (some t, some c)) := rfl

/-- The first `Challenge` with both messages in the message space answers and records
`C ← Encrypt(params, ID*, M_b)`. -/
theorem sidImpl_challenge_fresh (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (mm : Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) (t : Fin (S.idLen.eval κ) → Bool)
    (h : S.MsgSpace κ pp (FixedLengthScheme.splitHalf mm).1 ∧
      S.MsgSpace κ pp (FixedLengthScheme.splitHalf mm).2) :
    S.sidImpl b κ pp msk 2 mm (some t, none) =
      (S.enc κ pp t (if b then (FixedLengthScheme.splitHalf mm).2
        else (FixedLengthScheme.splitHalf mm).1)).bind fun c =>
        .pure (S.encCT κ c, (some t, some (S.encCT κ c))) := by
  simp only [sidImpl]
  rw [if_pos h]

/-- The first `Challenge` with a message outside the message space answers `⊥`. -/
theorem sidImpl_challenge_invalid (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (mm : Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) (t : Fin (S.idLen.eval κ) → Bool)
    (h : ¬ (S.MsgSpace κ pp (FixedLengthScheme.splitHalf mm).1 ∧
      S.MsgSpace κ pp (FixedLengthScheme.splitHalf mm).2)) :
    S.sidImpl b κ pp msk 2 mm (some t, none) = .pure (zeroBits _, (some t, none)) := by
  simp only [sidImpl]
  rw [if_neg h]

/-- **The three oracles from typed handlers**: an implementation of `S.sidSpec κ` whose `Init`,
`KeyGen` and `Challenge` oracles are the handlers `init`, `key` and `chal`, which take and return
strings of the scheme's lengths. Simulators and reductions describe their oracles this way, so
that they never read the oracle lengths `inLens`, `outLens` through their bodies. -/
def oracleImpl {σ : Type} (κ : ℕ)
    (init : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.ppLen.eval κ) → Bool) × σ))
    (key : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.skLen.eval κ + 1) → Bool) × σ))
    (chal : (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) → σ →
      ProbComp ((Fin (S.ctLen.eval κ) → Bool) × σ)) :
    QueryImpl (S.sidSpec κ) σ unifSpec
  | 0, x, s => init x s
  | 1, x, s => key x s
  | 2, x, s => chal x s

/-- Oracle `0` of `S.oracleImpl κ init key chal` is the handler `init`. -/
theorem oracleImpl_zero {σ : Type} (κ : ℕ)
    (init : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.ppLen.eval κ) → Bool) × σ))
    (key : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.skLen.eval κ + 1) → Bool) × σ))
    (chal : (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) → σ →
      ProbComp ((Fin (S.ctLen.eval κ) → Bool) × σ))
    (x : Fin (S.idLen.eval κ) → Bool) (s : σ) :
    S.oracleImpl κ init key chal 0 x s = init x s := rfl

/-- Oracle `1` of `S.oracleImpl κ init key chal` is the handler `key`. -/
theorem oracleImpl_one {σ : Type} (κ : ℕ)
    (init : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.ppLen.eval κ) → Bool) × σ))
    (key : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.skLen.eval κ + 1) → Bool) × σ))
    (chal : (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) → σ →
      ProbComp ((Fin (S.ctLen.eval κ) → Bool) × σ))
    (x : Fin (S.idLen.eval κ) → Bool) (s : σ) :
    S.oracleImpl κ init key chal 1 x s = key x s := rfl

/-- Oracle `2` of `S.oracleImpl κ init key chal` is the handler `chal`. -/
theorem oracleImpl_two {σ : Type} (κ : ℕ)
    (init : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.ppLen.eval κ) → Bool) × σ))
    (key : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.skLen.eval κ + 1) → Bool) × σ))
    (chal : (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) → σ →
      ProbComp ((Fin (S.ctLen.eval κ) → Bool) × σ))
    (x : Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) (s : σ) :
    S.oracleImpl κ init key chal 2 x s = chal x s := rfl

/-- The codec of the adversary: the three oracles and a one-bit guess. -/
def sidCodec (κ : ℕ) : MachineCodec (S.sidSpec κ) (Fin 1 → Bool) :=
  bitCodec (S.inLens κ) (S.outLens κ) 1

/-- The adversary codec is a bit codec: `S.sidCodec κ = bitCodec (S.inLens κ) (S.outLens κ) 1`. -/
theorem sidCodec_eq (κ : ℕ) : S.sidCodec κ = bitCodec (S.inLens κ) (S.outLens κ) 1 := rfl

/-- **The experiment `IND-sID-CPA_b(A, κ)`** [BB04, §2.1] with query budget `q`: run `Setup`,
draw `A`'s coins, run `A(1^κ)` against the three oracles from the empty state (no identity
committed, no challenge), and return its one-bit guess. -/
noncomputable def sidGame (A : NUPPT) (q : ℕ) (b : Bool) (κ : ℕ) : ProbComp Bool :=
  (S.setup κ).bind fun k =>
  (ProbComp.sample (A.Coins κ)).bind fun r =>
  (simulate (S.sidImpl b κ k.1 k.2) (A.toComp (S.sidCodec κ) κ q r) (none, none)).bind
    fun res => .pure (res.1 0)

/-- The IND-sID-CPA experiment runs `Setup`, samples the adversary's coins, simulates the
oracles from the empty state, and returns the guess bit. -/
theorem sidGame_eq (A : NUPPT) (q : ℕ) (b : Bool) (κ : ℕ) :
    S.sidGame A q b κ =
      (S.setup κ).bind fun k =>
      (ProbComp.sample (A.Coins κ)).bind fun r =>
      (simulate (S.sidImpl b κ k.1 k.2) (A.toComp (S.sidCodec κ) κ q r) (none, none)).bind
        fun res => .pure (res.1 0) := rfl

/-- **IND-sID-CPA security** [BB04, §2.1 and Definition 2.2]: for every non-uniform PPT `A` and
every polynomial query budget `q`, `A`'s advantage between the experiments with `b = 0` and
`b = 1` is negligible.

**Deviation:** asymptotic, with a polynomial budget `q(κ)` on all queries (the paper's `q_ID`
bounds private-key queries); the advantage is twice the paper's (module docstring). -/
def SIDSecure : Prop :=
  ∀ (A : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ κ, advantage (S.sidGame A (q.eval κ) false κ) (S.sidGame A (q.eval κ) true κ) ≤ ε κ

/-- IND-sID-CPA security is negligible advantage, uniformly in `κ`, for every non-uniform PPT
adversary and polynomial query budget. -/
theorem sidSecure_iff :
    S.SIDSecure ↔ ∀ (A : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ κ, advantage (S.sidGame A (q.eval κ) false κ) (S.sidGame A (q.eval κ) true κ) ≤ ε κ :=
  Iff.rfl

end IBEScheme

end TCSlib.Cryptography.AdvancedEncryption.IdentityBased
```

## ===== TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyen.lean (Lean, at 9e7a96481785d6cac4dea3b2e990c49ac278b060) =====

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.Defs
import TCSlib.Cryptography.Pairing.Group
import TCSlib.Cryptography.Asymptotic.Sampling
import Mathlib.Algebra.Field.ZMod

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The Boneh–Boyen selective-identity IBE (BB1)

[BB04, §4.1] with depth `ℓ = 1` (an IBE system is an HIBE whose identities have depth 1,
[BB04, §2.1]). In a bilinear group `G` of prime order `p` with pairing `e`:
* **Setup**: a random generator `g ∈ G^*`, `α ∈ Z_p`, `g_1 = g^α`, random `h, g_2 ∈ G`;
  `params = (g, g_1, g_2, h)`, `master-key = g_2^α`; `F(x) = g_1^x h`.
* **KeyGen**(`ID ∈ Z_p`): a random `r ∈ Z_p`, `d_ID = (g_2^α · F(ID)^r, g^r)`.
* **Encrypt**(`params`, `ID`, `M ∈ G_1`): a random `s ∈ Z_p`,
  `C = (e(g_1, g_2)^s · M, g^s, F(ID)^s)`.
* **Decrypt**(`d_ID = (d_0, d_1)`, `C = (A, B, C_1)`): `A · e(C_1, d_1) / e(B, d_0)`.

It is IND-sID-CPA secure under Decision BDH [BB04, Theorem 4.1], without random oracles; the
security statement and its simulation are in `AdvancedEncryption.IdentityBased.BonehBoyenSecurity`.

**Identities and messages.** The generic interface (`IBEScheme`) has `ℓ(κ)`-bit identities.
BB1 reads an identity as the residue of its binary value in `Z_p` (`idToZ`), the injective
"hash" `{0,1}^ℓ → {0, …, 2^ℓ − 1}` of [BB04, §4.4] ("a collision resistant hash function
`H : {0,1}^* → {1, …, 2^b}` where `2^b < p` is sufficient"); distinct identities stay distinct in
`Z_p` when `2^ℓ ≤ p`, which the security theorem assumes except with negligible probability.
Messages are elements of `G_T` (the paper's `G_1`), sent as their `wT(κ)`-bit encodings; the
message space is the set of encodings, and `Encrypt` reads a string through `decodeT` (strings
outside the message space read as `1`, a choice that is never exercised by the game, which
refuses them).

**Groups from the generator.** Parameters, keys and ciphertexts carry the description `d` of the
group they live in (a dependent pair), since the group is drawn by `Setup` from the generator
(`Pairing.BilinearGen`). Decryption of a ciphertext whose description differs from the key's is
`⊥`.

**Deviation:** abstract bilinear groups drawn by a generator; depth-1 identities given as
`ℓ(κ)`-bit strings and embedded into `Z_p` by their binary value; messages as encodings of `G_T`;
parameters, keys and ciphertexts tagged with the group's description.

## Main definitions

* `BB1.Params`, `BB1.Key`, `BB1.Ciphertext` — `params`, `d_ID` and `C`.
* `BB1.F`, `BB1.setup`, `BB1.keyGen`, `BB1.encrypt`, `BB1.decrypt` — the
  algorithms of [BB04, §4.1] over one bilinear group.
* `BB1.idToZ`, `BB1.decodeT` — identities in `Z_p` and messages in `G_T`.
* `bb1Scheme` — BB1 as an `IBEScheme` over a generator.
* `BB1SimState`, `bb1SimParams`, `bb1SimKey`, `bb1SimInit`, `bb1SimKeyQ`,
  `bb1SimCt`, `bb1SimChal`, `bb1SimImpl`, `bb1SimGame` — the simulator of
  [BB04, proof of Theorem 4.1] and its game, with ideal exponents.

## Main results

* `BB1.decrypt_encrypt` — decryption inverts encryption [BB04, §4.1, "for a valid
  ciphertext"].
* `bb1_correct` — BB1 is perfectly correct.
* `bb1_encPP_inj`, `bb1_encSK_inj`, `bb1_encCT_inj` — BB1's encodings are injective on
  parameters of the advertised description length and on keys and ciphertexts in one group.
* `bb1SimInit_none`, …, `bb1SimChal_invalid` — the simulator's handlers case by case.

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §2.1 (pp. 2–4), §4.1 (pp. 5–6:
  the construction), §4.2 (pp. 6–8: the simulator in the proof of Theorem 4.1), §4.4 (p. 8:
  arbitrary identities).
-/

namespace TCSlib.Cryptography.AdvancedEncryption.IdentityBased

open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing
  TCSlib.Cryptography.Composability

namespace BB1

variable {wG wT : ℕ} (B : BilinearGroup wG wT)

/-- **System parameters** `params = (g, g_1, g_2, h)` of BB1 [BB04, §4.1, `Setup` at depth 1]. -/
structure Params where
  /-- The generator `g ∈ G^*`. -/
  g : B.G
  /-- `g_1 = g^α`. -/
  g1 : B.G
  /-- The random element `g_2`. -/
  g2 : B.G
  /-- The random element `h = h_1`. -/
  h : B.G

/-- **A private key** `d_ID = (d_0, d_1)` of BB1 [BB04, §4.1, `KeyGen` at depth 1]. -/
structure Key where
  /-- `d_0 = g_2^α · F(ID)^r`. -/
  d0 : B.G
  /-- `d_1 = g^r`. -/
  d1 : B.G

/-- **A ciphertext** `C = (A, B, C_1)` of BB1 [BB04, §4.1, `Encrypt` at depth 1]. -/
structure Ciphertext where
  /-- `A = e(g_1, g_2)^s · M`. -/
  a : B.GT
  /-- `B = g^s`. -/
  b : B.G
  /-- `C_1 = F(ID)^s`. -/
  c : B.G

variable {B}

/-- **The function** `F(x) = g_1^x h` [BB04, §4.1, `F_1 : Z_p → G`]. -/
def F (pp : Params B) (x : ZMod B.order) : B.G := pp.g1 ^ x.val * pp.h

/-- `F pp x = pp.g1 ^ x.val * pp.h`. -/
theorem F_eq (pp : Params B) (x : ZMod B.order) : F pp x = pp.g1 ^ x.val * pp.h := rfl

variable (B)

/-- **Setup** [BB04, §4.1, depth 1]: a uniform generator `g ∈ G^*`, a uniform `α ∈ Z_p`, uniform
`h, g_2 ∈ G`; returns `params = (g, g^α, g_2, h)` and `master-key = g_2^α`. -/
noncomputable def setup : ProbComp (Params B × B.G) :=
  (ProbComp.sample {x : B.G // x ≠ 1}).bind fun g =>
  (ProbComp.sample (ZMod B.order)).bind fun α =>
  (ProbComp.sample B.G).bind fun h =>
  (ProbComp.sample B.G).bind fun g2 =>
    .pure (⟨g.1, g.1 ^ α.val, g2, h⟩, g2 ^ α.val)

/-- `setup B` draws `g ∈ G^*`, `α ∈ Z_p`, `h, g_2 ∈ G` and returns
`((g, g^α, g_2, h), g_2^α)`. -/
theorem setup_eq :
    setup B =
      (ProbComp.sample {x : B.G // x ≠ 1}).bind fun g =>
      (ProbComp.sample (ZMod B.order)).bind fun α =>
      (ProbComp.sample B.G).bind fun h =>
      (ProbComp.sample B.G).bind fun g2 =>
        .pure (⟨g.1, g.1 ^ α.val, g2, h⟩, g2 ^ α.val) := rfl

variable {B}

/-- **KeyGen** [BB04, §4.1, depth 1]: from the parameters, the master key `mk = g_2^α` and an
identity `ID ∈ Z_p`, a uniform `r ∈ Z_p` and `d_ID = (mk · F(ID)^r, g^r)`. -/
noncomputable def keyGen (pp : Params B) (mk : B.G) (id : ZMod B.order) : ProbComp (Key B) :=
  (ProbComp.sample (ZMod B.order)).bind fun r => .pure ⟨mk * F pp id ^ r.val, pp.g ^ r.val⟩

/-- `keyGen pp mk id` draws `r ∈ Z_p` and returns `(mk · F(id)^r, g^r)`. -/
theorem keyGen_eq (pp : Params B) (mk : B.G) (id : ZMod B.order) :
    keyGen pp mk id =
      (ProbComp.sample (ZMod B.order)).bind fun r => .pure ⟨mk * F pp id ^ r.val, pp.g ^ r.val⟩ :=
  rfl

/-- **Encrypt** [BB04, §4.1, depth 1]: for an identity `ID ∈ Z_p` and a message `M ∈ G_T`, a
uniform `s ∈ Z_p` and `C = (e(g_1, g_2)^s · M, g^s, F(ID)^s)`. -/
noncomputable def encrypt (pp : Params B) (id : ZMod B.order) (M : B.GT) :
    ProbComp (Ciphertext B) :=
  (ProbComp.sample (ZMod B.order)).bind fun s =>
    .pure ⟨B.pair pp.g1 pp.g2 ^ s.val * M, pp.g ^ s.val, F pp id ^ s.val⟩

/-- `encrypt pp id M` draws `s ∈ Z_p` and returns `(e(g_1, g_2)^s · M, g^s, F(id)^s)`. -/
theorem encrypt_eq (pp : Params B) (id : ZMod B.order) (M : B.GT) :
    encrypt pp id M =
      (ProbComp.sample (ZMod B.order)).bind fun s =>
        .pure ⟨B.pair pp.g1 pp.g2 ^ s.val * M, pp.g ^ s.val, F pp id ^ s.val⟩ := rfl

/-- **Decrypt** [BB04, §4.1, depth 1]: `A · e(C_1, d_1) / e(B, d_0)` for `d_ID = (d_0, d_1)` and
`C = (A, B, C_1)`. -/
def decrypt (d : Key B) (C : Ciphertext B) : B.GT := C.a * B.pair C.c d.d1 / B.pair C.b d.d0

/-- `decrypt d C = C.a * e(C.c, d.d1) / e(C.b, d.d0)`. -/
theorem decrypt_eq (d : Key B) (C : Ciphertext B) :
    decrypt d C = C.a * B.pair C.c d.d1 / B.pair C.b d.d0 := rfl

/-- **Decryption inverts encryption** [BB04, §4.1, "for a valid ciphertext, we have
`e(C_1, d_1) / e(B, d_0) = 1 / e(g_1, g_2)^s`"]: for the parameters `(g, g^α, g_2, h)`, the
master key `g_2^α`, the private key with exponent `r` and the ciphertext with exponent `s` of
`M` for the same identity, `Decrypt(d_ID, C) = M`.

**Proof sketch.** The proof is the paper's computation:
`e(F(ID)^s, g^r) = e(g, F(ID))^{sr}` (bilinearity and symmetry) and
`e(g^s, g_2^α F(ID)^r) = e(g, g_2)^{αs} · e(g, F(ID))^{sr}`, while the mask of `A`
is `e(g^α, g_2)^s = e(g, g_2)^{αs}`. -/
theorem decrypt_encrypt (g g2 h : B.G) (α r s id : ZMod B.order) (M : B.GT) :
    decrypt (⟨g2 ^ α.val * F ⟨g, g ^ α.val, g2, h⟩ id ^ r.val, g ^ r.val⟩ : Key B)
      ⟨B.pair (g ^ α.val) g2 ^ s.val * M, g ^ s.val, F ⟨g, g ^ α.val, g2, h⟩ id ^ s.val⟩ = M := by
  rw [decrypt_eq]
  dsimp only
  have h1 : B.pair (g ^ α.val) g2 ^ s.val = B.pair g g2 ^ (α.val * s.val) := by
    rw [B.pair_pow_left, ← pow_mul]
  have h2 : B.pair (F ⟨g, g ^ α.val, g2, h⟩ id ^ s.val) (g ^ r.val) =
      B.pair g (F ⟨g, g ^ α.val, g2, h⟩ id) ^ (s.val * r.val) := by
    rw [B.bilinear_pow, B.pair_comm (F ⟨g, g ^ α.val, g2, h⟩ id) g]
  have h3 : B.pair (g ^ s.val) (g2 ^ α.val * F ⟨g, g ^ α.val, g2, h⟩ id ^ r.val) =
      B.pair g g2 ^ (α.val * s.val) * B.pair g (F ⟨g, g ^ α.val, g2, h⟩ id) ^ (s.val * r.val) := by
    rw [map_mul (B.pair (g ^ s.val)), B.bilinear_pow, B.bilinear_pow, mul_comm s.val α.val]
  rw [h1, h2, h3, mul_right_comm]
  exact mul_div_cancel_left _ _

variable (B)

/-- **An identity as an element of `Z_p`**: the residue of the binary value of an `ℓ`-bit string,
the injective encoding `{0,1}^ℓ → {0, …, 2^ℓ − 1}` of [BB04, §4.4] read in `Z_p`. -/
def idToZ {ℓ : ℕ} (id : Fin ℓ → Bool) : ZMod B.order := (bitsToNat id : ZMod B.order)

/-- `idToZ id` is the cast of `bitsToNat id` into `Z_p`. -/
theorem idToZ_eq {ℓ : ℕ} (id : Fin ℓ → Bool) :
    idToZ B id = (bitsToNat id : ZMod B.order) := rfl

/-- **A message from its encoding**: the element of `G_T` with encoding `w`, and `1` when `w`
encodes none. -/
noncomputable def decodeT (w : Fin wT → Bool) : B.GT := (Function.partialInv B.encT w).getD 1

/-- `decodeT B w = (Function.partialInv B.encT w).getD 1`. -/
theorem decodeT_eq (w : Fin wT → Bool) : decodeT B w = (Function.partialInv B.encT w).getD 1 :=
  rfl

/-- Decoding an encoding returns the element: `decodeT B (B.encT u) = u`. -/
theorem decodeT_encT (u : B.GT) : decodeT B (B.encT u) = u := by
  rw [decodeT_eq, Function.partialInv_left B.encT_injective, Option.getD_some]

end BB1

/-! ### The encodings of BB1 lose no information

The wire formats of `bb1Scheme` below, before the scheme is assembled: each is injective on the
objects it is used for, which gives the fields `encPP_inj`, `encSK_inj` and `encCT_inj`. -/

section Encodings

variable (G : BilinearGen)

/-- **Parameters with a description of the advertised length are determined by their
encoding** (the encoding of `bb1Scheme`'s parameters): for `pp, pp'` whose descriptions have
`descLen(κ)` bits, equal padded words `d ‖ g ‖ g_1 ‖ g_2 ‖ h` give `pp = pp'`.

**Proof sketch.** Both words have exactly `descLen(κ) + 4 · wG(κ)` bits, so they are equal before
padding (`ofFn_padFin_of_length`). Splitting off the last four blocks of `wG(κ)` bits
(`List.append_inj'`) leaves equal descriptions; in the one group they describe, the four element
encodings are equal, so the elements are (`List.ofFn_inj`, `encG_injective`). -/
theorem bb1_encPP_inj {κ : ℕ} {pp pp' : Σ d : List Bool, BB1.Params (G.group κ d)}
    (h : padFin ((PolyExpr.add G.descLen (.mul (.const 4) G.wG)).eval κ)
        (pp.1 ++ List.ofFn ((G.group κ pp.1).encG pp.2.g) ++
          List.ofFn ((G.group κ pp.1).encG pp.2.g1) ++
          List.ofFn ((G.group κ pp.1).encG pp.2.g2) ++
          List.ofFn ((G.group κ pp.1).encG pp.2.h)) =
      padFin ((PolyExpr.add G.descLen (.mul (.const 4) G.wG)).eval κ)
        (pp'.1 ++ List.ofFn ((G.group κ pp'.1).encG pp'.2.g) ++
          List.ofFn ((G.group κ pp'.1).encG pp'.2.g1) ++
          List.ofFn ((G.group κ pp'.1).encG pp'.2.g2) ++
          List.ofFn ((G.group κ pp'.1).encG pp'.2.h)))
    (hl : pp.1.length = G.descLen.eval κ) (hl' : pp'.1.length = G.descLen.eval κ) :
    pp = pp' := by
  obtain ⟨d, ⟨g, g1, g2, x⟩⟩ := pp
  obtain ⟨d', ⟨g', g1', g2', x'⟩⟩ := pp'
  dsimp only at hl hl' h
  have hw := congrArg List.ofFn h
  rw [ofFn_padFin_of_length (by simp only [List.length_append, List.length_ofFn, hl,
      PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]; omega),
    ofFn_padFin_of_length (by simp only [List.length_append, List.length_ofFn, hl',
      PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]; omega)] at hw
  obtain ⟨hw, hx⟩ := List.append_inj' hw (by simp only [List.length_ofFn])
  obtain ⟨hw, hg2⟩ := List.append_inj' hw (by simp only [List.length_ofFn])
  obtain ⟨hw, hg1⟩ := List.append_inj' hw (by simp only [List.length_ofFn])
  obtain ⟨rfl, hg⟩ := List.append_inj' hw (by simp only [List.length_ofFn])
  rw [List.ofFn_inj, (BilinearGroup.encG_injective _).eq_iff] at hx hg2 hg1 hg
  rw [hx, hg2, hg1, hg]

/-- **Two keys in one group with equal encodings are equal** (the encoding of `bb1Scheme`'s
private keys, which omits the description).

**Proof sketch.** Both words `d_0 ‖ d_1` have exactly `2 · wG(κ)` bits, so they are equal
before padding (`ofFn_padFin_of_length`); splitting at `wG(κ)` (`List.append_inj'`) gives equal
encodings of `d_0` and of `d_1`, hence equal elements (`List.ofFn_inj`, `encG_injective`). -/
theorem bb1_encSK_inj {κ : ℕ} {d : List Bool} {k k' : BB1.Key (G.group κ d)}
    (h : padFin ((PolyExpr.mul (.const 2) G.wG).eval κ)
        (List.ofFn ((G.group κ d).encG k.d0) ++ List.ofFn ((G.group κ d).encG k.d1)) =
      padFin ((PolyExpr.mul (.const 2) G.wG).eval κ)
        (List.ofFn ((G.group κ d).encG k'.d0) ++ List.ofFn ((G.group κ d).encG k'.d1))) :
    k = k' := by
  obtain ⟨a, b⟩ := k
  obtain ⟨a', b'⟩ := k'
  dsimp only at h
  have hw := congrArg List.ofFn h
  rw [ofFn_padFin_of_length (by simp only [List.length_append, List.length_ofFn,
      PolyExpr.eval_mul, PolyExpr.eval_const]; omega),
    ofFn_padFin_of_length (by simp only [List.length_append, List.length_ofFn,
      PolyExpr.eval_mul, PolyExpr.eval_const]; omega)] at hw
  obtain ⟨ha, hb⟩ := List.append_inj' hw (by simp only [List.length_ofFn])
  rw [List.ofFn_inj, (G.group κ d).encG_injective.eq_iff] at ha hb
  rw [ha, hb]

/-- **Two ciphertexts in one group with equal encodings are equal** (the encoding of
`bb1Scheme`'s ciphertexts, which omits the description).

**Proof sketch.** Both words `A ‖ B ‖ C_1` have exactly `wT(κ) + 2 · wG(κ)` bits, so they are
equal before padding (`ofFn_padFin_of_length`); splitting off the last two blocks of `wG(κ)` bits
(`List.append_inj'`) gives equal encodings of the three components, hence equal components
(`List.ofFn_inj`, `encT_injective`, `encG_injective`). -/
theorem bb1_encCT_inj {κ : ℕ} {d : List Bool} {c c' : BB1.Ciphertext (G.group κ d)}
    (h : padFin ((PolyExpr.add G.wT (.mul (.const 2) G.wG)).eval κ)
        (List.ofFn ((G.group κ d).encT c.a) ++ List.ofFn ((G.group κ d).encG c.b) ++
          List.ofFn ((G.group κ d).encG c.c)) =
      padFin ((PolyExpr.add G.wT (.mul (.const 2) G.wG)).eval κ)
        (List.ofFn ((G.group κ d).encT c'.a) ++ List.ofFn ((G.group κ d).encG c'.b) ++
          List.ofFn ((G.group κ d).encG c'.c))) :
    c = c' := by
  obtain ⟨a, b, x⟩ := c
  obtain ⟨a', b', x'⟩ := c'
  dsimp only at h
  have hw := congrArg List.ofFn h
  rw [ofFn_padFin_of_length (by simp only [List.length_append, List.length_ofFn,
      PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]; omega),
    ofFn_padFin_of_length (by simp only [List.length_append, List.length_ofFn,
      PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]; omega)] at hw
  obtain ⟨hw, hx⟩ := List.append_inj' hw (by simp only [List.length_ofFn])
  obtain ⟨ha, hb⟩ := List.append_inj' hw (by simp only [List.length_ofFn])
  rw [List.ofFn_inj, (G.group κ d).encG_injective.eq_iff] at hx hb
  rw [List.ofFn_inj, (G.group κ d).encT_injective.eq_iff] at ha
  rw [ha, hb, hx]

end Encodings

/-- **The BB1 IBE system** over the bilinear group generator `G`, for `ℓ(κ)`-bit identities
[BB04, §4.1 at depth 1, with the identity encoding of §4.4]: `Setup` runs the generator and BB1's
`Setup` in the group it describes; the parameters are `⟨d, (g, g_1, g_2, h)⟩`, the master key
also carries the parameters; `KeyGen` and `Encrypt` read the identity through `idToZ` and the
message through `decodeT`; `Decrypt` returns the encoding of BB1's decryption, or `⊥` if the key
and the ciphertext name different descriptions. The message space at `⟨d, params⟩` is the set
of encodings of `G_T` of the group `d` describes. Parameters are encoded as `d` followed by the
four elements, keys as two elements, ciphertexts as `A, B, C_1`.

The encodings are injective where the interface asks: generated descriptions have `descLen(κ)`
bits (`BilinearGen.length_desc`, `bb1_encPP_inj`), and the keys and ciphertexts of one possible
output of `Setup` carry its description, in whose group the element encodings are injective
(`bb1_encSK_inj`, `bb1_encCT_inj`). -/
noncomputable def bb1Scheme (G : BilinearGen) (ℓ : PolyExpr) : IBEScheme where
  idLen := ℓ
  msgLen := G.wT
  ppLen := .add G.descLen (.mul (.const 4) G.wG)
  skLen := .mul (.const 2) G.wG
  ctLen := .add G.wT (.mul (.const 2) G.wG)
  PP κ := Σ d : List Bool, BB1.Params (G.group κ d)
  MSK κ := Σ d : List Bool, BB1.Params (G.group κ d) × (G.group κ d).G
  SK κ := Σ d : List Bool, BB1.Key (G.group κ d)
  CT κ := Σ d : List Bool, BB1.Ciphertext (G.group κ d)
  setup κ :=
    (ProbComp.sample (G.gen.Coins κ)).bind fun r =>
    (BB1.setup (G.group κ (G.desc κ r))).bind fun k =>
      .pure (⟨G.desc κ r, k.1⟩, ⟨G.desc κ r, k⟩)
  keyGen _ msk id :=
    (BB1.keyGen msk.2.1 msk.2.2 (BB1.idToZ _ id)).bind fun d => .pure ⟨msk.1, d⟩
  enc _ pp id m :=
    (BB1.encrypt pp.2 (BB1.idToZ _ id) (BB1.decodeT _ m)).bind fun c => .pure ⟨pp.1, c⟩
  dec κ sk c :=
    if h : c.1 = sk.1 then
      some ((G.group κ sk.1).encT (BB1.decrypt sk.2 (h ▸ c.2)))
    else none
  MsgSpace κ pp m := ∃ u, (G.group κ pp.1).encT u = m
  encPP κ pp := padFin _ (pp.1 ++ List.ofFn ((G.group κ pp.1).encG pp.2.g) ++
    List.ofFn ((G.group κ pp.1).encG pp.2.g1) ++ List.ofFn ((G.group κ pp.1).encG pp.2.g2) ++
    List.ofFn ((G.group κ pp.1).encG pp.2.h))
  encSK κ sk := padFin _ (List.ofFn ((G.group κ sk.1).encG sk.2.d0) ++
    List.ofFn ((G.group κ sk.1).encG sk.2.d1))
  encCT κ c := padFin _ (List.ofFn ((G.group κ c.1).encT c.2.a) ++
    List.ofFn ((G.group κ c.1).encG c.2.b) ++ List.ofFn ((G.group κ c.1).encG c.2.c))
  encPP_inj κ := by
    refine (OracleComp.allOutputs_true _).bind fun r _ =>
      (OracleComp.allOutputs_true _).bind fun k _ => OracleComp.allOutputs_pure.2 ?_
    refine (OracleComp.allOutputs_true _).bind fun r' _ =>
      (OracleComp.allOutputs_true _).bind fun k' _ => OracleComp.allOutputs_pure.2 ?_
    exact fun h => bb1_encPP_inj G h (G.length_desc κ r) (G.length_desc κ r')
  encSK_inj κ := by
    refine (OracleComp.allOutputs_true _).mono fun k _ id id' => ?_
    refine (OracleComp.allOutputs_true _).bind fun a _ => OracleComp.allOutputs_pure.2 ?_
    refine (OracleComp.allOutputs_true _).bind fun a' _ => OracleComp.allOutputs_pure.2 ?_
    exact fun h => congrArg (Sigma.mk k.2.1) (bb1_encSK_inj G h)
  encCT_inj κ := by
    refine (OracleComp.allOutputs_true _).mono fun k _ id id' m m' => ?_
    refine (OracleComp.allOutputs_true _).bind fun a _ => OracleComp.allOutputs_pure.2 ?_
    refine (OracleComp.allOutputs_true _).bind fun a' _ => OracleComp.allOutputs_pure.2 ?_
    exact fun h => congrArg (Sigma.mk k.1.1) (bb1_encCT_inj G h)

attribute [simps (config := { isSimp := false }) idLen msgLen ppLen skLen ctLen PP MSK SK CT
  setup keyGen enc dec MsgSpace encPP encSK encCT] bb1Scheme

/-- **BB1 is perfectly correct** [BB04, §4.1, "Indeed, for a valid ciphertext …"]: every
honest run with a message of the message space decrypts to that message.

**Proof sketch.** Every possible outcome of an honest run has parameters
`⟨d, (g, g^α, g_2, h)⟩`, key `⟨d, (g_2^α F(ID)^r, g^r)⟩` and ciphertext
`⟨d, (e(g^α, g_2)^s · M', g^s, F(ID)^s)⟩` with the same description `d` and
`M' = decodeT M`, so `Decrypt` takes its first branch and returns the encoding of `M'` by
`BB1.decrypt_encrypt`. A message of the message space is an encoding `encT u`, so
`M' = u` (`decodeT_encT`) and its encoding is `M`. -/
theorem bb1_correct (G : BilinearGen) (ℓ : PolyExpr) : (bb1Scheme G ℓ).Correct := by
  rw [IBEScheme.correct_iff]
  intro κ id m
  rw [IBEScheme.honestRun_eq, bb1Scheme_setup]
  simp only [OracleComp.bind_assoc, OracleComp.pure_bind, BB1.setup_eq, bb1Scheme_keyGen,
    bb1Scheme_enc, BB1.keyGen_eq, BB1.encrypt_eq]
  refine (OracleComp.allOutputs_true _).bind fun r _ => ?_
  refine (OracleComp.allOutputs_true _).bind fun g _ => ?_
  refine (OracleComp.allOutputs_true _).bind fun α _ => ?_
  refine (OracleComp.allOutputs_true _).bind fun h _ => ?_
  refine (OracleComp.allOutputs_true _).bind fun g2 _ => ?_
  refine (OracleComp.allOutputs_true _).bind fun ρ _ => ?_
  refine (OracleComp.allOutputs_true _).bind fun σ _ => ?_
  refine OracleComp.allOutputs_pure.2 fun hm => ?_
  obtain ⟨u, hu⟩ := hm
  rw [bb1Scheme_dec, dif_pos rfl]
  dsimp only
  rw [← hu, BB1.decodeT_encT, BB1.decrypt_encrypt]

/-! ### The simulator of [BB04, proof of Theorem 4.1]

The Decision BDH algorithm `B` of the proof, as typed oracle handlers over the parameters of
`bb1Scheme`, with ideal uniform exponents; `bb1SimGame` runs the adversary against them. The
security argument is in `AdvancedEncryption.IdentityBased.BonehBoyenSecurity`. -/

section Simulator

variable (G : BilinearGen) (ℓ : PolyExpr)

/-- The simulator's state at parameter `κ` in the group described by `d`: the committed identity
with the simulator's exponent `α_1` (once `Init` is asked), and the issued challenge. -/
abbrev BB1SimState (κ : ℕ) (d : List Bool) : Type :=
  Option ((Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) × ZMod (G.group κ d).order) ×
    Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)

/-- `BB1SimState G ℓ κ d` is the optional pair of the committed identity and `α_1`, with the
optional encoded challenge. -/
theorem bb1SimState_eq (κ : ℕ) (d : List Bool) :
    BB1SimState G ℓ κ d =
      (Option ((Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) × ZMod (G.group κ d).order) ×
        Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) := rfl

/-- The simulated parameters `(g, X, Y, X^{−ID*} g^{α_1})` for the committed identity `ID*` and
the exponent `α_1` [BB04, proof of Theorem 4.1, *Setup*]. -/
noncomputable def bb1SimParams {κ : ℕ} {d : List Bool} (g X Y : (G.group κ d).G)
    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (α₁ : ZMod (G.group κ d).order) :
    BB1.Params (G.group κ d) :=
  ⟨g, X, Y, X ^ (-BB1.idToZ (G.group κ d) t).val * g ^ α₁.val⟩

/-- `bb1SimParams G ℓ g X Y t α₁ = (g, X, Y, X ^ (−idToZ t).val · g ^ α₁.val)`. -/
theorem bb1SimParams_eq {κ : ℕ} {d : List Bool} (g X Y : (G.group κ d).G)
    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (α₁ : ZMod (G.group κ d).order) :
    bb1SimParams G ℓ g X Y t α₁ =
      ⟨g, X, Y, X ^ (-BB1.idToZ (G.group κ d) t).val * g ^ α₁.val⟩ := rfl

/-- The simulated private key of `ID ≠ ID*` with exponent `r` [BB04, proof of Theorem 4.1,
*Phase 1*]: `(Y^{−α_1/(ID − ID*)} F(ID)^r, Y^{−1/(ID − ID*)} g^r)`, with `F` of the simulated
parameters and the identities read in `Z_p`. -/
noncomputable def bb1SimKey {κ : ℕ} {d : List Bool} (g X Y : (G.group κ d).G)
    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (α₁ : ZMod (G.group κ d).order)
    (id : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (r : ZMod (G.group κ d).order) :
    BB1.Key (G.group κ d) :=
  ⟨Y ^ (-α₁ / (BB1.idToZ (G.group κ d) id - BB1.idToZ (G.group κ d) t)).val *
      BB1.F (bb1SimParams G ℓ g X Y t α₁) (BB1.idToZ (G.group κ d) id) ^ r.val,
    Y ^ (-1 / (BB1.idToZ (G.group κ d) id - BB1.idToZ (G.group κ d) t)).val * g ^ r.val⟩

/-- `bb1SimKey G ℓ g X Y t α₁ id r` is
`(Y^{(−α₁/(id − t)).val} · F(id)^{r.val}, Y^{(−1/(id − t)).val} · g^{r.val})`. -/
theorem bb1SimKey_eq {κ : ℕ} {d : List Bool} (g X Y : (G.group κ d).G)
    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (α₁ : ZMod (G.group κ d).order)
    (id : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (r : ZMod (G.group κ d).order) :
    bb1SimKey G ℓ g X Y t α₁ id r =
      ⟨Y ^ (-α₁ / (BB1.idToZ (G.group κ d) id - BB1.idToZ (G.group κ d) t)).val *
          BB1.F (bb1SimParams G ℓ g X Y t α₁) (BB1.idToZ (G.group κ d) id) ^ r.val,
        Y ^ (-1 / (BB1.idToZ (G.group κ d) id - BB1.idToZ (G.group κ d) t)).val * g ^ r.val⟩ :=
  rfl

/-- **The simulator's `Init`** [BB04, proof of Theorem 4.1, *Initialization* and *Setup*] on the
description `d` and `g, X = g^a, Y = g^{b'}`: before any commitment, draw `α_1 ∈ Z_p`, record
`(ID, α_1)` and answer the simulated parameters; afterwards answer the recorded identity's. -/
noncomputable def bb1SimInit (κ : ℕ) (d : List Bool) (g X Y : (G.group κ d).G)
    (id : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (s : BB1SimState G ℓ κ d) :
    ProbComp ((Fin ((bb1Scheme G ℓ).ppLen.eval κ) → Bool) × BB1SimState G ℓ κ d) :=
  match s.1 with
  | none => (ProbComp.sample (ZMod (G.group κ d).order)).bind fun α₁ =>
      .pure ((bb1Scheme G ℓ).encPP κ ⟨d, bb1SimParams G ℓ g X Y id α₁⟩, (some (id, α₁), s.2))
  | some (t, α₁) => .pure ((bb1Scheme G ℓ).encPP κ ⟨d, bb1SimParams G ℓ g X Y t α₁⟩, s)

/-- `Init` before any commitment draws `α_1` and answers the simulated parameters. -/
theorem bb1SimInit_none (κ : ℕ) (d : List Bool) (g X Y : (G.group κ d).G)
    (id : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) :
    bb1SimInit G ℓ κ d g X Y id (none, c) =
      (ProbComp.sample (ZMod (G.group κ d).order)).bind fun α₁ =>
        .pure ((bb1Scheme G ℓ).encPP κ ⟨d, bb1SimParams G ℓ g X Y id α₁⟩, (some (id, α₁), c)) :=
  rfl

/-- `Init` after a commitment answers the recorded identity's simulated parameters. -/
theorem bb1SimInit_some (κ : ℕ) (d : List Bool) (g X Y : (G.group κ d).G)
    (id t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (α₁ : ZMod (G.group κ d).order)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) :
    bb1SimInit G ℓ κ d g X Y id (some (t, α₁), c) =
      .pure ((bb1Scheme G ℓ).encPP κ ⟨d, bb1SimParams G ℓ g X Y t α₁⟩, (some (t, α₁), c)) :=
  rfl

/-- **The simulator's `KeyGen`** [BB04, proof of Theorem 4.1, *Phase 1*]: when `ID*` is recorded
and `ID ≠ ID*`, draw `r ∈ Z_p` and answer `⟨1, bb1SimKey … ID r⟩`; otherwise `⊥`. -/
noncomputable def bb1SimKeyQ (κ : ℕ) (d : List Bool) (g X Y : (G.group κ d).G)
    (id : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (s : BB1SimState G ℓ κ d) :
    ProbComp ((Fin ((bb1Scheme G ℓ).skLen.eval κ + 1) → Bool) × BB1SimState G ℓ κ d) :=
  match s.1 with
  | some (t, α₁) =>
    if id = t then .pure (zeroBits _, s)
    else (ProbComp.sample (ZMod (G.group κ d).order)).bind fun r =>
      .pure (FixedLengthScheme.decAnswer
        (some ((bb1Scheme G ℓ).encSK κ ⟨d, bb1SimKey G ℓ g X Y t α₁ id r⟩)), s)
  | none => .pure (zeroBits _, s)

/-- `KeyGen` before `Init` answers `⊥`. -/
theorem bb1SimKeyQ_none (κ : ℕ) (d : List Bool) (g X Y : (G.group κ d).G)
    (id : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) :
    bb1SimKeyQ G ℓ κ d g X Y id (none, c) = .pure (zeroBits _, (none, c)) := rfl

/-- `KeyGen` for the committed identity answers `⊥`. -/
theorem bb1SimKeyQ_target (κ : ℕ) (d : List Bool) (g X Y : (G.group κ d).G)
    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (α₁ : ZMod (G.group κ d).order)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) :
    bb1SimKeyQ G ℓ κ d g X Y t (some (t, α₁), c) = .pure (zeroBits _, (some (t, α₁), c)) := by
  simp [bb1SimKeyQ]

/-- `KeyGen` for `ID ≠ ID*` draws `r` and answers the simulated key. -/
theorem bb1SimKeyQ_ne (κ : ℕ) (d : List Bool) (g X Y : (G.group κ d).G)
    (id t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (α₁ : ZMod (G.group κ d).order)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) (h : id ≠ t) :
    bb1SimKeyQ G ℓ κ d g X Y id (some (t, α₁), c) =
      (ProbComp.sample (ZMod (G.group κ d).order)).bind fun r =>
        .pure (FixedLengthScheme.decAnswer
          (some ((bb1Scheme G ℓ).encSK κ ⟨d, bb1SimKey G ℓ g X Y t α₁ id r⟩)),
          (some (t, α₁), c)) := by
  simp [bb1SimKeyQ, h]

/-- The simulated challenge `(M · T, Z, Z^{α_1})` [BB04, proof of Theorem 4.1, *Challenge*] of the
message string `m`, encoded. -/
noncomputable def bb1SimCt (κ : ℕ) (d : List Bool) (Z : (G.group κ d).G) (T : (G.group κ d).GT)
    (α₁ : ZMod (G.group κ d).order) (m : Fin ((bb1Scheme G ℓ).msgLen.eval κ) → Bool) :
    Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool :=
  (bb1Scheme G ℓ).encCT κ ⟨d, ⟨BB1.decodeT _ m * T, Z, Z ^ α₁.val⟩⟩

/-- `bb1SimCt G ℓ κ d Z T α₁ m` is the encoding of `(decodeT m · T, Z, Z ^ α₁.val)`. -/
theorem bb1SimCt_eq (κ : ℕ) (d : List Bool) (Z : (G.group κ d).G) (T : (G.group κ d).GT)
    (α₁ : ZMod (G.group κ d).order) (m : Fin ((bb1Scheme G ℓ).msgLen.eval κ) → Bool) :
    bb1SimCt G ℓ κ d Z T α₁ m =
      (bb1Scheme G ℓ).encCT κ ⟨d, ⟨BB1.decodeT _ m * T, Z, Z ^ α₁.val⟩⟩ := rfl

open Classical in
/-- **The simulator's `Challenge`** [BB04, proof of Theorem 4.1, *Challenge*] with challenge bit
`b`, on `Z = g^c` and `T`: with `ID*` recorded and no challenge yet, if `M₀, M₁` are in the
message space, answer and record `(M_b · T, Z, Z^{α_1})`, and otherwise `⊥`; once a challenge is
recorded, repeat it; before `Init`, `⊥`. -/
noncomputable def bb1SimChal (b : Bool) (κ : ℕ) (d : List Bool) (g X Y Z : (G.group κ d).G)
    (T : (G.group κ d).GT)
    (mm : Fin ((bb1Scheme G ℓ).msgLen.eval κ + (bb1Scheme G ℓ).msgLen.eval κ) → Bool)
    (s : BB1SimState G ℓ κ d) :
    ProbComp ((Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool) × BB1SimState G ℓ κ d) :=
  match s.1, s.2 with
  | some _, some c => .pure (c, s)
  | some (t, α₁), none =>
    if (bb1Scheme G ℓ).MsgSpace κ ⟨d, bb1SimParams G ℓ g X Y t α₁⟩
          (FixedLengthScheme.splitHalf mm).1 ∧
        (bb1Scheme G ℓ).MsgSpace κ ⟨d, bb1SimParams G ℓ g X Y t α₁⟩
          (FixedLengthScheme.splitHalf mm).2 then
      .pure (bb1SimCt G ℓ κ d Z T α₁ (if b then (FixedLengthScheme.splitHalf mm).2
          else (FixedLengthScheme.splitHalf mm).1),
        (s.1, some (bb1SimCt G ℓ κ d Z T α₁ (if b then (FixedLengthScheme.splitHalf mm).2
          else (FixedLengthScheme.splitHalf mm).1))))
    else .pure (zeroBits _, s)
  | none, _ => .pure (zeroBits _, s)

/-- `Challenge` before `Init` answers `⊥`. -/
theorem bb1SimChal_none (b : Bool) (κ : ℕ) (d : List Bool) (g X Y Z : (G.group κ d).G)
    (T : (G.group κ d).GT)
    (mm : Fin ((bb1Scheme G ℓ).msgLen.eval κ + (bb1Scheme G ℓ).msgLen.eval κ) → Bool)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) :
    bb1SimChal G ℓ b κ d g X Y Z T mm (none, c) = .pure (zeroBits _, (none, c)) := rfl

/-- `Challenge` after a recorded challenge repeats it. -/
theorem bb1SimChal_repeat (b : Bool) (κ : ℕ) (d : List Bool) (g X Y Z : (G.group κ d).G)
    (T : (G.group κ d).GT)
    (mm : Fin ((bb1Scheme G ℓ).msgLen.eval κ + (bb1Scheme G ℓ).msgLen.eval κ) → Bool)
    (t : (Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) × ZMod (G.group κ d).order)
    (w : Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool) :
    bb1SimChal G ℓ b κ d g X Y Z T mm (some t, some w) = .pure (w, (some t, some w)) := rfl

/-- The first `Challenge` with both messages in the message space answers and records
`(M_b · T, Z, Z^{α_1})`. -/
theorem bb1SimChal_fresh (b : Bool) (κ : ℕ) (d : List Bool) (g X Y Z : (G.group κ d).G)
    (T : (G.group κ d).GT)
    (mm : Fin ((bb1Scheme G ℓ).msgLen.eval κ + (bb1Scheme G ℓ).msgLen.eval κ) → Bool)
    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (α₁ : ZMod (G.group κ d).order)
    (h : (bb1Scheme G ℓ).MsgSpace κ ⟨d, bb1SimParams G ℓ g X Y t α₁⟩
          (FixedLengthScheme.splitHalf mm).1 ∧
        (bb1Scheme G ℓ).MsgSpace κ ⟨d, bb1SimParams G ℓ g X Y t α₁⟩
          (FixedLengthScheme.splitHalf mm).2) :
    bb1SimChal G ℓ b κ d g X Y Z T mm (some (t, α₁), none) =
      .pure (bb1SimCt G ℓ κ d Z T α₁ (if b then (FixedLengthScheme.splitHalf mm).2
          else (FixedLengthScheme.splitHalf mm).1),
        (some (t, α₁), some (bb1SimCt G ℓ κ d Z T α₁ (if b then (FixedLengthScheme.splitHalf mm).2
          else (FixedLengthScheme.splitHalf mm).1)))) := by
  simp only [bb1SimChal]
  rw [if_pos h]

/-- The first `Challenge` with a message outside the message space answers `⊥`. -/
theorem bb1SimChal_invalid (b : Bool) (κ : ℕ) (d : List Bool) (g X Y Z : (G.group κ d).G)
    (T : (G.group κ d).GT)
    (mm : Fin ((bb1Scheme G ℓ).msgLen.eval κ + (bb1Scheme G ℓ).msgLen.eval κ) → Bool)
    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (α₁ : ZMod (G.group κ d).order)
    (h : ¬ ((bb1Scheme G ℓ).MsgSpace κ ⟨d, bb1SimParams G ℓ g X Y t α₁⟩
          (FixedLengthScheme.splitHalf mm).1 ∧
        (bb1Scheme G ℓ).MsgSpace κ ⟨d, bb1SimParams G ℓ g X Y t α₁⟩
          (FixedLengthScheme.splitHalf mm).2)) :
    bb1SimChal G ℓ b κ d g X Y Z T mm (some (t, α₁), none) =
      .pure (zeroBits _, (some (t, α₁), none)) := by
  simp only [bb1SimChal]
  rw [if_neg h]

/-- **The simulator's oracles** [BB04, proof of Theorem 4.1] with challenge bit `b`, at
parameter `κ`, on the description `d` and the Decision BDH tuple `(g, X, Y, Z, T)`: the three
handlers `bb1SimInit`, `bb1SimKeyQ`, `bb1SimChal` as an implementation of the game's oracles. -/
noncomputable def bb1SimImpl (b : Bool) (κ : ℕ) (d : List Bool) (g X Y Z : (G.group κ d).G)
    (T : (G.group κ d).GT) :
    QueryImpl ((bb1Scheme G ℓ).sidSpec κ) (BB1SimState G ℓ κ d) unifSpec :=
  (bb1Scheme G ℓ).oracleImpl κ (bb1SimInit G ℓ κ d g X Y) (bb1SimKeyQ G ℓ κ d g X Y)
    (bb1SimChal G ℓ b κ d g X Y Z T)

/-- `bb1SimImpl` is `oracleImpl` of the three simulator handlers. -/
theorem bb1SimImpl_eq (b : Bool) (κ : ℕ) (d : List Bool) (g X Y Z : (G.group κ d).G)
    (T : (G.group κ d).GT) :
    bb1SimImpl G ℓ b κ d g X Y Z T =
      (bb1Scheme G ℓ).oracleImpl κ (bb1SimInit G ℓ κ d g X Y) (bb1SimKeyQ G ℓ κ d g X Y)
        (bb1SimChal G ℓ b κ d g X Y Z T) := rfl

/-- **The simulation game** [BB04, proof of Theorem 4.1] for the adversary `A` with budget `q`,
challenge bit `b`, on `P_BDH` (`real`) or `R_BDH`: draw the generator's coins `r`, `g ∈ G^*`,
`a, b', c ∈ Z_p`, `T ∈ G_T` and `A`'s coins, run `A(1^κ)` against the simulator's oracles on
`(g, g^a, g^{b'}, g^c, T')` with `T' = e(g, g)^{ab'c}` if `real` and `T` otherwise, and return
`A`'s guess. -/
noncomputable def bb1SimGame (A : NUPPT) (q : ℕ) (b real : Bool) (κ : ℕ) : ProbComp Bool :=
  (ProbComp.sample (G.gen.Coins κ)).bind fun r =>
  (ProbComp.sample {x : (G.group κ (G.desc κ r)).G // x ≠ 1}).bind fun g =>
  (ProbComp.sample (ZMod (G.group κ (G.desc κ r)).order × ZMod (G.group κ (G.desc κ r)).order ×
    ZMod (G.group κ (G.desc κ r)).order)).bind fun abc =>
  (ProbComp.sample (G.group κ (G.desc κ r)).GT).bind fun t =>
  (ProbComp.sample (A.Coins κ)).bind fun ρ =>
  (simulate (bb1SimImpl G ℓ b κ (G.desc κ r) g.1 (g.1 ^ abc.1.val) (g.1 ^ abc.2.1.val)
      (g.1 ^ abc.2.2.val)
      (if real then (G.group κ (G.desc κ r)).pair g.1 g.1 ^ (abc.1 * abc.2.1 * abc.2.2).val
        else t))
    (A.toComp ((bb1Scheme G ℓ).sidCodec κ) κ q ρ) (none, none)).bind fun res => .pure (res.1 0)

/-- The simulation game draws the generator's coins, `g ∈ G^*`, `(a, b', c)`, `T` and `A`'s
coins, and simulates `A` against `bb1SimImpl` on the Decision BDH tuple. -/
theorem bb1SimGame_eq (A : NUPPT) (q : ℕ) (b real : Bool) (κ : ℕ) :
    bb1SimGame G ℓ A q b real κ =
      (ProbComp.sample (G.gen.Coins κ)).bind fun r =>
      (ProbComp.sample {x : (G.group κ (G.desc κ r)).G // x ≠ 1}).bind fun g =>
      (ProbComp.sample (ZMod (G.group κ (G.desc κ r)).order × ZMod (G.group κ (G.desc κ r)).order ×
        ZMod (G.group κ (G.desc κ r)).order)).bind fun abc =>
      (ProbComp.sample (G.group κ (G.desc κ r)).GT).bind fun t =>
      (ProbComp.sample (A.Coins κ)).bind fun ρ =>
      (simulate (bb1SimImpl G ℓ b κ (G.desc κ r) g.1 (g.1 ^ abc.1.val) (g.1 ^ abc.2.1.val)
          (g.1 ^ abc.2.2.val)
          (if real then (G.group κ (G.desc κ r)).pair g.1 g.1 ^ (abc.1 * abc.2.1 * abc.2.2).val
            else t))
        (A.toComp ((bb1Scheme G ℓ).sidCodec κ) κ q ρ) (none, none)).bind
        fun res => .pure (res.1 0) := rfl

end Simulator

end TCSlib.Cryptography.AdvancedEncryption.IdentityBased
```

## ===== TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine.lean (Lean, at 9e7a96481785d6cac4dea3b2e990c49ac278b060) =====

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyen
import TCSlib.Cryptography.Pairing.Assumptions
import TCSlib.Cryptography.Pairing.Operations

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The BB1 simulator as a Decision BDH distinguisher

Step 3 of the security proof of [BB04, Theorem 4.1] at depth `ℓ = 1`; the other steps and the
assembled theorem `bb1_sidSecure` are in
`AdvancedEncryption/IdentityBased/BonehBoyenSecurity.lean`. The paper's algorithm `B`
[BB04, pp. 7–8] is efficient: given `(g, g^a, g^b, g^c, T)` it runs the adversary with the
simulated `Setup`, private keys and challenge, using only group operations, exponent arithmetic
modulo `p` and fresh random exponents. Here the simulation game
`bb1SimGame` (defined beside the scheme in `AdvancedEncryption/IdentityBased/BonehBoyen.lean`)
uses ideal uniform exponents, and the step shows that it is, up to a negligible statistical term,
the Decision BDH experiment of a non-uniform PPT distinguisher (the machine step: handler theorem
T1 with exponents drawn from coin blocks).

This step is its own module so that it can be filled independently of the coupling steps
`bb1_sim_real` and `bb1_sim_random` (ruling Q11 of `PairingCryptographyPlan.md`).

## Main definitions

None.

## Main results

* `exists_bb1_distinguisher` — the simulation is a Decision BDH distinguisher (step 3).

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §4.2 (pp. 6–8): Theorem 4.1 and
  its proof.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Definition 26.8, non-uniform PPT.)
-/

namespace TCSlib.Cryptography.AdvancedEncryption.IdentityBased

open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing
  TCSlib.Cryptography.Composability

variable (G : BilinearGen) (ℓ : PolyExpr)

/-- **Step 3: the simulation is a Decision BDH distinguisher** [BB04, §4.2, the algorithm `B`
in the proof of Theorem 4.1, whose cost is the theorem's `Θ(τ ℓ q_S)` with the paper's hierarchy
depth `ℓ = 1`]: with efficient group operations `O` and the arithmetic bundle `H`, for every
adversary `A` and polynomial budget `q` there are non-uniform PPT distinguishers `D_b` and a
negligible `σ` with `|Pr[bb1SimGame … b real = 1] − Pr[dbdhGame (D_b) real = 1]| ≤ σ(κ)` for
both tuple distributions.

**Proof sketch.** `D_b` parses `⟨d, ⟨g, ⟨X, ⟨Y, ⟨Z, T⟩⟩⟩⟩⟩` and runs `A` with the handler of
`bb1SimImpl`: group operations by `O.mulG`, `O.powG`, `O.mulT`, membership by `O.memT`, and
exponent arithmetic modulo `p = O.orderStr d` with `H`: products by `mulStr` and `divModStr`;
negation and differences of residues `x, y < p` as `(p − x) mod p` and `(x + (p − y)) mod p`
with `H`'s natural-number functions `addStr`, `subStr`, `divModStr` (truncated subtraction
alone is not modular subtraction); and the field inverse by `xgcdStr`, which returns the
inverse of zero as zero, as `Z_p` does. Let `n = κ + wG(κ) + 1`. Each of `α_1` and the `r`s
is drawn as `(Candidates.sampleBelowL p (Nat.size p) n n w).getD 0` on its own block `w` of
`n²` fresh coin bits. Since `encG` is injective, `p ≤ 2^{wG(κ)} < 2^n`, and
`0 < p`, so `statClose_sampleBelowL` puts each draw within `(1/2)^n ≤ 2^{−κ}` of uniform on
`Z_p`. The handler is polynomial-time with polynomial state, so the handler theorem
`Games.exists_handlerMachine` (T1), applied to the adversary obtained from `A` by
`Games.exists_toCompOn_of_toComp` (its `toCompOn` interface), makes the run a machine whose
output is exactly `A`'s guess in a game equal to `bb1SimGame` with sampled instead of ideal
exponents. A run makes at most `q(κ) + 1` draws, from independent blocks, so the hybrid over the
draws gives `σ(κ) = (q(κ) + 1) · 2^{−κ}`. -/
theorem exists_bb1_distinguisher (H : Candidates.ArithmeticFP) (O : G.Ops) (A : NUPPT)
    (q : PolyExpr) :
    ∃ D : Bool → NUPPT, ∃ σ : ℕ → ℝ, Negligible σ ∧ ∀ (b real : Bool) (κ : ℕ),
      advantage (bb1SimGame G ℓ A (q.eval κ) b real κ) (G.dbdhGame (D b) real κ) ≤ σ κ := by
  sorry

end TCSlib.Cryptography.AdvancedEncryption.IdentityBased
```

## ===== TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity.lean (Lean, at 9e7a96481785d6cac4dea3b2e990c49ac278b060) =====

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyen
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenMachine
import TCSlib.Cryptography.Pairing.Assumptions

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Selective-identity security of BB1 under Decision BDH

[BB04, Theorem 4.1] at depth `ℓ = 1`: if Decision BDH holds in `G`, the BB1 system is
IND-sID-CPA secure. The proof [BB04, pp. 7–8] builds a Decision BDH algorithm `B` that, given
`(g, g^a, g^b, g^c, T)`, plays the selective-identity game with the adversary without knowing the
master key `g^{ab}`:
* **Setup**, once `ID*` is committed: a random `α_1 ∈ Z_p`, `h = g_1^{−ID*} g^{α_1}`,
  `params = (g, g_1 = g^a, g_2 = g^b, h)`, so that `F(x) = g_1^{x − ID*} g^{α_1}`;
* **private keys** for `ID ≠ ID*`: a random `r ∈ Z_p`,
  `(g_2^{−α_1/(ID − ID*)} F(ID)^r, g_2^{−1/(ID − ID*)} g^r)`;
* **the challenge**: `(M_b · T, g^c, (g^c)^{α_1})`.

**The simulation game.** `bb1SimGame` (defined beside the scheme in
`AdvancedEncryption/IdentityBased/BonehBoyen.lean`) is that simulator as a game of the `Games`
framework, with ideal uniform exponents, run against the adversary machine on a Decision BDH
tuple drawn from `P_BDH` (`real`) or `R_BDH`. The security proof has three named steps:
1. `bb1_sim_real`: on `P_BDH`, the simulation is the real game, except when distinct
   identities collide in `Z_p` (the generator's coins with `p < 2^ℓ`);
2. `bb1_sim_random`: on `R_BDH`, the simulation does not depend on the challenge bit;
3. `exists_bb1_distinguisher`: the simulation is, up to a negligible statistical term, the
   Decision BDH experiment of a non-uniform PPT distinguisher (the machine step: handler theorem
   T1 with exponents drawn from coin blocks). It is stated in its own module,
   `AdvancedEncryption/IdentityBased/BonehBoyenMachine.lean`, so that it can be filled
   independently of steps 1 and 2 (ruling Q11 of `PairingCryptographyPlan.md`).
`bb1_sidSecure` assembles them by the triangle inequality.

**Deviation:** the paper's `B` draws the challenge bit itself and outputs `[b = b']`; here there
is one simulation per value of `b`, and the advantage of the two-experiment form is bounded by
the sum of two Decision BDH advantages; the paper's statement is concrete (`t' < t − Θ(τ ℓ q_S)`).

## Main definitions

None: the simulator (`bb1SimImpl`, `bb1SimGame`) is defined beside the scheme, in
`AdvancedEncryption.IdentityBased.BonehBoyen`.

## Main results

* `bb1_sim_real`, `bb1_sim_random` — steps 1 and 2 (step 3, `exists_bb1_distinguisher`, is in
  `AdvancedEncryption.IdentityBased.BonehBoyenMachine`).
* `bb1_sidSecure` — [BB04, Theorem 4.1] at depth 1.

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §4.2 (pp. 6–8): Theorem 4.1 and
  its proof; §4.4 (p. 8).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Definition 26.8, non-uniform PPT.)
-/

namespace TCSlib.Cryptography.AdvancedEncryption.IdentityBased

open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing
  TCSlib.Cryptography.Composability

variable (G : BilinearGen) (ℓ : PolyExpr)

/-- **Step 1: on `P_BDH` the simulation is the real game** [BB04, proof of Theorem 4.1, "When
the input 5-tuple is sampled from `P_BDH` … `A`'s view is identical to its view in a real attack
game"], except on the generator's coins where `p < 2^ℓ`, where distinct identities may collide
in `Z_p`.

**Proof sketch.** Fix coins with `2^ℓ ≤ p`, so `idToZ` is injective on `ℓ`-bit strings
(`bitsToNat_lt`, `bitsToNat_injective`). Couple the two games: the real `Setup` draws
`(g, α, h, g_2)`, the simulation `(g, a, b', c)` and, at `Init`, `α_1`. Map `α ↦ a`,
`g_2 ↦ g^{b'}` and `h ↦ g_1^{−ID*} g^{α_1}` (a bijection in `α_1` for each `ID*`, so `h` is uniform
and independent; `expect_sample_equiv`). Answers to `Init` agree. For `ID ≠ ID*` the simulated
key with exponent `r` is the real key with exponent `r̃ = r − b'/(ID − ID*)`, a bijection of
`Z_p` (the paper's computation, `pow_val_mul`, `bilinear_pow`). The challenge is `Encrypt` with
`s = c`, since `F(ID*) = g^{α_1}` and `e(g, g)^{ab'c} = e(g_1, g_2)^c`. The state machines agree
step by step (`simulate` with matched implementations, `Games.expect_simulate_congr`), so the
acceptance probabilities differ only on the excluded coins, of probability
`Pr_r[p < 2^ℓ]`. -/
theorem bb1_sim_real (A : NUPPT) (q : ℕ) (b : Bool) (κ : ℕ) :
    advantage ((bb1Scheme G ℓ).sidGame A q b κ) (bb1SimGame G ℓ A q b true κ) ≤
      uprob (fun r : G.gen.Coins κ => (G.inst κ r).order < 2 ^ ℓ.eval κ) := by
  sorry

/-- **Step 2: on `R_BDH` the simulation does not depend on the challenge bit** [BB04, proof of
Theorem 4.1, "when `T` is uniform and independent in `G_1` … `C` is independent of `b` in the
adversary's view"].

**Proof sketch.** In the `R_BDH` game, `T` is uniform in `G_T` and is used only in the first
component `M_b · T` of the challenge. For each fixed run up to the challenge, `T ↦ M_b · T` is a
bijection of `G_T`, so exchanging the sample of `T` with the rest of the game
(`expect_expect_sample`) and reindexing it by `T ↦ M_b^{−1} M_{1−b} · T`
(`expect_sample_equiv`) turns the game with `b = 0` into the game with `b = 1`. Challenges
outside the message space are refused in both games. -/
theorem bb1_sim_random (A : NUPPT) (q : ℕ) (κ : ℕ) :
    advantage (bb1SimGame G ℓ A q false false κ) (bb1SimGame G ℓ A q true false κ) = 0 := by
  sorry

/-- **BB1 is IND-sID-CPA secure under Decision BDH** [BB04, Theorem 4.1, at depth `ℓ = 1`]: if
the generator's groups have efficient operations, the arithmetic bundle holds, the order is at
least `2^{ℓ(κ)}` except with negligible probability, and Decision BDH holds, then the BB1 system
for `ℓ(κ)`-bit identities is IND-sID-CPA secure.

**Deviation:** asymptotic form of the paper's concrete bound (`(t', q_S, ε)`-security from
`(t, ε)`-Decision BDH); the efficiency hypotheses `O` and `H` make the paper's simulator a
non-uniform PPT; `hN` makes distinct `ℓ`-bit identities distinct in `Z_p` (the condition
`2^b < p` of [BB04, §4.4]); the advantage is bounded by two Decision BDH advantages, one per
challenge bit, instead of one.

**Proof sketch.** By the triangle inequality through the simulation games and the Decision BDH
experiments of the two distinguishers `D_0`, `D_1` of step 3,
`advantage (sidGame … false) (sidGame … true)` is at most
`2 Pr_r[p < 2^ℓ] + 4σ(κ) + dbdhAdv D_0 κ + dbdhAdv D_1 κ` (steps 1 and 3 for each bit, step 2
in the middle). Each term is negligible (`hN`, step 3, `h`). -/
theorem bb1_sidSecure (H : Candidates.ArithmeticFP) (O : G.Ops)
    (hN : ∃ δ : ℕ → ℝ, Negligible δ ∧ G.OrderAtLeastExcept (fun κ => 2 ^ ℓ.eval κ) δ)
    (h : G.DBDHAssumption) : (bb1Scheme G ℓ).SIDSecure := by
  rw [IBEScheme.sidSecure_iff]
  intro A q
  obtain ⟨δ, hδ, hN⟩ := hN
  obtain ⟨D, σ, hσ, hD⟩ := exists_bb1_distinguisher G ℓ H O A q
  refine ⟨fun κ => 2 * δ κ + 4 * σ κ + (G.dbdhAdv (D false) κ + G.dbdhAdv (D true) κ),
    ((hδ.const_mul 2).add (hσ.const_mul 4)).add
      ((G.dbdhAssumption_iff.1 h (D false)).add (G.dbdhAssumption_iff.1 h (D true))), fun κ => ?_⟩
  have hu := (G.orderAtLeastExcept_iff _ δ).1 hN κ
  have t := fun G₀ G₁ G₂ : ProbComp Bool => advantage_triangle G₀ G₁ G₂
  have hc := fun G₀ G₁ : ProbComp Bool => advantage_comm G₀ G₁
  have s0 := bb1_sim_real G ℓ A (q.eval κ) false κ
  have s1 := bb1_sim_real G ℓ A (q.eval κ) true κ
  have s2 := bb1_sim_random G ℓ A (q.eval κ) κ
  have d0T := hD false true κ
  have d0F := hD false false κ
  have d1T := hD true true κ
  have d1F := hD true false κ
  have a0 := G.dbdhAdv_eq (D false) κ
  have a1 := G.dbdhAdv_eq (D true) κ
  set S0 := (bb1Scheme G ℓ).sidGame A (q.eval κ) false κ
  set S1 := (bb1Scheme G ℓ).sidGame A (q.eval κ) true κ
  set M0T := bb1SimGame G ℓ A (q.eval κ) false true κ
  set M0F := bb1SimGame G ℓ A (q.eval κ) false false κ
  set M1T := bb1SimGame G ℓ A (q.eval κ) true true κ
  set M1F := bb1SimGame G ℓ A (q.eval κ) true false κ
  set E0T := G.dbdhGame (D false) true κ
  set E0F := G.dbdhGame (D false) false κ
  set E1T := G.dbdhGame (D true) true κ
  set E1F := G.dbdhGame (D true) false κ
  have := t S0 M0T S1
  have := t M0T E0T S1
  have := t E0T E0F S1
  have := t E0F M0F S1
  have := t M0F M1F S1
  have := t M1F E1F S1
  have := t E1F E1T S1
  have := t E1T M1T S1
  have := hc E0T E0F
  have := hc E0F M0F
  have := hc E1T M1T
  have := hc M1T S1
  linarith

end TCSlib.Cryptography.AdvancedEncryption.IdentityBased
```

## ===== TCSlib/Cryptography/Pairing.lean (Lean, at 9e7a96481785d6cac4dea3b2e990c49ac278b060) =====

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Pairing.Group
import TCSlib.Cryptography.Pairing.Assumptions
import TCSlib.Cryptography.Pairing.Operations

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Symmetric bilinear groups and the bilinear Diffie–Hellman assumptions

## Contents

* `Group`: abstract symmetric bilinear groups of prime order, their generators, bilinearity and
  non-degeneracy facts.
* `Assumptions`: the BDH and Decision BDH experiments and assumptions; Decision BDH implies BDH.
* `Operations`: the efficiency contract of a generator (group operations and pairing as
  polynomial-time string functions).

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004,
  §2.2 and §3.1.
* [Jou00] A. Joux, *A One Round Protocol for Tripartite Diffie–Hellman*, ANTS-IV, LNCS 1838,
  pp. 385–393, Springer, 2000.
-/
```

## ===== TCSlib/Cryptography/KeyExchange.lean (Lean, at 9e7a96481785d6cac4dea3b2e990c49ac278b060) =====

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.KeyExchange.Joux

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Key exchange

## Contents

* `Joux`: Joux's one-round tripartite Diffie–Hellman over a symmetric bilinear group, its
  correctness and its key indistinguishability under Decision BDH.

## References

* [Jou00] A. Joux, *A One Round Protocol for Tripartite Diffie–Hellman*, ANTS-IV, LNCS 1838,
  pp. 385–393, Springer, 2000.
-/
```

## ===== TCSlib/Cryptography/AdvancedEncryption/IdentityBased.lean (Lean, at 9e7a96481785d6cac4dea3b2e990c49ac278b060) =====

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.Defs
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyen
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenMachine
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Identity-based encryption

## Contents

* `Defs`: IBE systems, perfect correctness and selective-identity chosen-plaintext security
  (IND-sID-CPA).
* `BonehBoyen`: the Boneh–Boyen BDH-based system (BB1) over a bilinear group generator and its
  correctness.
* `BonehBoyenMachine`: the simulator as a non-uniform PPT Decision BDH distinguisher (step 3 of
  the security proof).
* `BonehBoyenSecurity`: the coupling steps of the security proof, and IND-sID-CPA security of
  BB1 under Decision BDH.

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004.
-/
```

## ===== TCSlib/Cryptography/AdvancedEncryption.lean (Lean, at 9e7a96481785d6cac4dea3b2e990c49ac278b060) =====

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Advanced encryption primitives

Encryption primitives beyond private-key and public-key encryption.

## Contents

* `Homomorphic`: homomorphic encryption; leveled Gentry–Sahai–Waters encryption from LWE.
* `IdentityBased`: identity-based encryption, selective-identity security and the Boneh–Boyen
  system (BB1).

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004.
* [GSW13] C. Gentry, A. Sahai, B. Waters, *Homomorphic Encryption from Learning with Errors:
  Conceptually-Simpler, Asymptotically-Faster, Attribute-Based*, CRYPTO 2013; author version
  dated 8 June 2013.
-/
```
