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
