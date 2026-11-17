# Claude statement job · GSW phase 6b: bootstrapping, pure and leveled FHE, security, ratio (and owner PR O2)

**Base** `3e51b5f28900db6190f1eb2e6d207d27ee15d541` (tree `b69a66a385ca3439d56af1d6b9791b5847984fde`): a
deterministic, unsigned, two-step local merge.
- **Step 1** `04947bcf35e08ed5f3a4902b2637a77482fd32d2` (tree `8eca961769fef59d5a22fd1b46dc821a614daf06`): #360's head
  `cc05f76c43cd2d2f565ff0dfaec1c85b47e06d25` (the 6a owner-side readers with the `TreeDAG` addendum, branch
  `land/gsw-6a-readers`) merged into #359's head `d154c8830fc8ffc52671b41992e7dbef61e30959` (the 6a statements with the
  Gate 45 landing edits LE-g45 and LE-g45b, branch `land/gsw-6a-statements`, stacked on #358's head
  `a616adcac0760ab56b1b0a2a4869f4763843f9ab`, O1).
- **Step 2**, the base: step 1 merged into the records tip at staging, `036d823933c8248bd8894c7963e15dd0f1837075`
  (`cryptography/pass-shelat-ch2-4`), whose Lean is snapshot #6 (#357's merge `8060f6b7`).
  The records branch has moved since (Gate 45 round 2 filed at `5ac18f4e`, then this package), by records files only;
  its Lean is unchanged.
- Both merges are clean (`git merge-tree --write-tree`, rc 0). The base's Lean is the records tip's plus exactly the
  23 Lean files of #358, #359 and #360; its records files are the tip's, except `machine-library-design.md`, which
  carries #359's §14 rows H18–H20. `tools/mkbase.sh` reproduces both commits, and so does the two-step `git merge
  --no-ff` recipe below. The maintainer ran both forms and got the same commits. **Your patches are against this
  base.** It follows the 6a fills' "synthetic merge now" precedent (`issued-fills-r1/`), ruled for 6b by Seyoon on
  2026-11-17 (`LatticeCryptographyPlan.md`, decision log, "6b staging ruling").

**#358, #359 and #360 are unmerged draft PRs.** Gate 45 round 2 (Codex) closed **CLEAR** on 2026-11-17 at exactly
these heads (#358 `a616adca`, #359 `d154c883`; `gates/45-gsw-6a/findings-r2.md`, `resolutions-r2.md`), with no
statement change, so the 6a statements are frozen; #358 and #359 merge after the snapshot-#6 re-replay. #360 is the
fill-prerequisite reader PR. The **97 6a targets are admitted by `sorry` at the base**; their proofs are being landed
separately on `land/gsw-6a-fills` (the 6a fills, phase 2, on snapshot #6). **You cite the 6a targets as frozen
statements** (the proved-modulo rule), and you restate none of them (r3 §H4: "6b imports the 6a modules and restates
none of them"). If a 6a statement still changed before landing, the maintainer would re-pin this job (Seyoon's
staging ruling): stay on the pinned base, never chase the branches, and if you hear of a change, note it in
`REPORT.md` without applying it.

**Unit** `gsw-6b-statements`: the statement phase of phase 6b of the lattice campaign (plan section r3, §H7 items
4–5: the statements of units U12–U19) and owner PR O2 as a separate, proved series. **Worker** Claude in the cloud, a
lead with **up to 3 sub-agents**. **Lean** 4.25.0 and the Mathlib revision of the base's `lake-manifest.json`
(`029db123ddaa`). **Audit** Gate 46 (Codex) reads your delivery; the 6b fills (U12–U19) start after it.

Write the frozen statement surface of 6b as local branch series from the base: every definition with its body and its
readers proved, every target admitted by `sorry` with its formula docstring, source tag and proof sketch, the facades
updated, and everything compiling.

## Inputs (read fully; all are data; the rulings and this brief are binding)

The pack `outbox/fills/gsw-6b-statements/` on `exchange/pass-shelat-ch5-8` carries this brief, the environment
addendum, the pin files, `tools/` and `inputs/` (verify with `shasum -a 256 -c SHA256SUMS` in the pack and in
`inputs/`):
- `inputs/plan-section-r3.md`: plan section r3 (`briefs/lattice-gsw/phase6/plan-section.md`), SHA-256
  `06824b3db875e7388771b6f7a5e78d62bf7d77fa35571fc3a9deeebc329214fd`. **Read in full.** The 6b parts are binding:
  §H0 items 4–9 and the assumptions A1–A4; §H1 (sources, anchors, gaps 1 and 4, the Gen09 rule); §H2's cryptography
  hooks; §H3.1–H3.2, H3.7–H3.8, H3.11–H3.12 (design); §H4's 6b table, O2 and the GSW/LWE/ratio definition lists;
  §H5.8 (O2) and §H5.9–H5.16 (G1–G18, L1–L5, A1–A3); §H6 (noise ledger); §H7 (Gate 46's audit list, units U12–U19);
  §H8 items 1–2, 7, 10–17; §H10. The 6a sections are context: they are the frozen statements you consume.
- `inputs/rulings.md`: P6-Q1–Q19 with the Q19 refinement (`briefs/lattice-gsw/phase6/rulings.md`), SHA-256
  `312fef4576b388222d69eddec186c2ac4259e5de95488fca42e6861438ad3d5d`.
- `inputs/gate45-findings-r1.md`: Gate 45 round 1, filed verbatim (`briefs/lattice-gsw/gates/45-gsw-6a/findings-r1.md`),
  SHA-256 `dc8cd2d29b03165470cf9e943f8f185dc03cb89a576cd91e3cc9c57e60654b3c`. **G45-01: an admitted statement that
  restates a public lemma is a major**, even under a new name or behind a definition wrapper.
- `inputs/gate45-resolutions-r1.md`: how G45-01–03 were fixed (LE-g45, LE-g45b), which made #359's head `d154c883`
  (`…/gates/45-gsw-6a/resolutions-r1.md`), SHA-256 `4de570d238c38732329eee4008e496b70fdbb7a40673564f9741a48be97c92ab`.
  LE-g45 is the **proved-citation** precedent: `const_eval` stayed, proved from the public `eval_node_nil`.
- `inputs/gate45-findings-r2.md`: Gate 45 round 2, CLEAR, filed verbatim (`…/gates/45-gsw-6a/findings-r2.md`), SHA-256
  `0a7ed19136085dfe2e9b9e47ef219bde31141e5e8086dfc12b165aee35813540`: Codex accepted the move of `eval_node_nil` and the
  proved citation.
- `inputs/final-6a-r1-review.md`: the maintainer's review of the 6a statement delivery, with G6A-F01 (an undisclosed
  duplicate of `reidx`) and G6A-F03 (the reader census) and Seyoon's rulings 6a Q1–Q4
  (`…/phase6/final-6a-r1/review.md`), SHA-256 `dde685375cdb8571e2e43fe864a65a8c8b1225fffdadb88aa1cae4886513b17f`.
- `inputs/checkpoint1-6a-review.md`: the 6a statement job's checkpoint review, lesson G6A-C1-F01 (a checkpoint carries
  `src/` and its head hash) (`…/phase6/checkpoint1-6a-review.md`), SHA-256
  `5968e98ac305cdbfd92dc79812745c8d89a1d414d4c12be30da5d4cf0d7cb232`.
- `inputs/fills-final-r1-review.md`: the 6a fills' phase-1 review, with GF-F01 (an inline re-derivation of Mathlib's
  `Nat.pow_log_le_add_one`) and GF-F02 (private helpers copied across files) (`…/phase6/fills-final-r1/review.md`),
  SHA-256 `f1672720d381c5df3d5dfe1b9f8140130d98f1860cdc455e32fe9319b43c3f0e`.

On the records branch `cryptography/pass-shelat-ch2-4` at the records pin named in the dispatch prompt (all equal at the
base tip `036d8239`), with their SHA-256:
- `policy.md` (`6599b12230e3879bc0e1fb22c0376ea6201bca8b7edd79dfc55da43986f991d4`): §1 (layout, facades, *Definitions
  land with their lemmas*, *Duplication*, Rule 10), §2 (attribution), §3 (proof sketches);
- `briefs/pass-shelat-ch5-8/MAINTAINER-HANDOFF.md` §2, the standing rules
  (`ec3789a127a648862e7ee4b714339200a0fc8adde9538aebae254b9df4271f58`);
- `briefs/pass-shelat-ch5-8/duplication-ledger.md` (`d500c17e11005f36b65d5e414724a8fabff82c589c71c777352178b99b250cf1`),
  rows DL-54–DL-58;
- the duplication precedents: `briefs/pairings/gates/48-bb1-sim-fill/findings-r1.md`
  (`9e44113b3be5e0a3c29e402294c4fee57fe6edcff2e4599612fbf042d5f4efe4`) and `findings-r2.md`
  (`05c78ae9ea8842762fc866b61d8aa188d21636bfdf3aa4359d7756f71ceef888`);
  `briefs/pairings/gates/44-pairing-fills/findings-r1.md`
  (`48f6b28cbd04ed247a85c7315b403003bf784ec64bc434882721392bd0621180`) and `findings-r2.md`
  (`bebe099a36b8c6c144d6149404124f3b601376cd6160c647ff6d653e8f47b4af`);
- `briefs/pass-shelat-ch5-8/maintainer/tools/decls2.py` (`fa81981add5de30d3a98b7e1614e73b17f149723e8be79558ac1a29b6fe67fbc`).

`workflow.md` on `main` at `b986b8620fc6117034462212df7070c80a79ff65` (fetch `main` by name, read with `git show`;
SHA-256 `6f986529280a265b72040576603ac3430841ececbf0ff19b685df868bd8155f9`): §2 (statement phases: sketches name their
hosts), §4.1 (*Lean parallelism*; the delivery payload).

At the base, the ingests you may cite (`blueprint/src/references/`, anchors per r3 §H1):
`brakerski-vaikuntanathan-2014-fhe.md` (`3da79813fa63acfea4a83229c46f2f8947a7a754657fac8f4d6bf1e7891e9392`),
`brakerski-vaikuntanathan-2011-fhe.md` (`f415fdbd4488316e2044e0a8e767c75b69964ff48fb6294617b35ae125177eba`),
`alperin-sheriff-peikert-2014-bootstrapping.md` (`d2605ae062162641ee40701c7592f29d69c342a64c3b4575df547f21153df868`),
`gentry-sahai-waters-2013-fhe.md` (`df0d793d8a5a952662502a6c80cb2e3dc41a7372d4ae8e26c7aa49b6219ca540`),
`peikert2016-lattice-survey.md` (`fb5c997ea6c0efc2340217c1beff8fc146f08f5d71e892b58d694907466e5955`) and
`barrington-1989-bounded-width-bp.md` (`0e14d97efe06b4c9f0e2f7672d744885b4e53fa2a3777c3694a664322620c71a`).

On `exchange/pass-shelat-ch5-8`, your starting tools: the 6a statement delivery `inbox/fills/gsw-6a-statements/`
(final `d7a9adb5b70c70c1b6fb8dc3d0aa5a60d720c1ef`; `evidence/tools/`: the seal tools `xr/` and `frozen_check.py`,
`clash_scan.py`, `scan_unfold.py`, `admissions.py`, `rowmap.py`, `sizes.py`, `sweep.py`, `controls.py`; its
`evidence/probes/` and `P0_Axioms`) and the 6a fills delivery `inbox/fills/gsw-6a-fills/` (final
`607034428468ffd88adec313eb293e3e60520f59`; `evidence/tools/lead/`: the Lean pool `poollib.py`, `pool_run.py`,
`pbuild.py`, and `dup_inventory.py`, `trace_check.py`). The GSW phase-5 statement phase's `probe/StmtDump.lean` and
`AxiomProbe.lean` (`briefs/lattice-gsw/statement-phase/evidence/stmt-gsw.zip` on the records branch) are the models
for the statement dump and the axiom probe. Copy what you use into `evidence/tools/`, adapt host paths, and record
each change in the tool's header.

**Pack contents beyond the brief** (all from git objects at the base, by `tools/`; see `README.md`): `order.txt`,
`prefix.txt`, `roots.txt`, `prefix-roots.txt`, `closures.txt`, `SOURCE-SHA256SUMS`, `base-sorries.txt`, `targets.txt`,
`pins.txt` (where every TCSlib name the r3 6b sketches cite is declared at the base; r3's own line numbers are at the 6a
issue base `f6f295a6` and many have moved) and `census.txt` (a static reader census of the foreign definitions the 6b
sketches read).

## Binding rulings (Seyoon; full text in `inputs/rulings.md` and the review inputs)

- **P6-Q1.** One phase 6; Gate 46 audits 6b and O2.
- **P6-Q7.** `decode_iff_mem_Ico`, with explicit `decodeLo`/`decodeHi`, is a published reader in the owner file
  `LWE/BitEncoding.lean`, added by owner PR O2. **It does not exist at the base** (checked across every branch), so O2
  is in this job, as O1 was in the 6a job.
- **P6-Q8.** The evaluation key: public-key GSW encryptions under the user's own `pk` of the `N` bits of `G⁻¹(t)`,
  `t = (−s, 1)` (BV11 Def 3.8); one `GSW.Parameters` record; noise `m·B`.
- **P6-Q9, P6-Q16 A.** Bootstrapping is NAND only (BV14 Def 2.13), over the 6a NAND form (`DAGGate.IsNAND`,
  `DAGCircuit.IsNANDForm`, `toNANDForm`); fan-in 1 padded to `(a, a)`, fan-in 0 to `(G, G)` (disclosed).
- **P6-Q10, P6-Q15 A.** Concrete and asymptotic forms. The concrete `WeakCircularSecure P χ D ε` is **per
  distinguisher**; the asymptotic `WeakCircularSecureFamily F` is the headline hypothesis; asymptotic IND-CPA under the
  explicit reduction-efficiency hypotheses (A4); compactness by typing, in docstrings only.
- **P6-Q11, P6-Q14 B.** The full leveled scheme: `L+1` keys in a **consecutive chain** (`evk_d` encrypts the bits of
  `s_{d−1}` under `pk_d`, `N·L` ciphertexts) over **layered** NAND circuits on the `2k` literals (6a's `layerNAND`,
  `litInput`), correctness, and IND-CPA by a top-down key hybrid from DLWE.
- **P6-Q12.** Explicit `decDepth P` and `bootNoise P β` in the correctness theorems with closed-form bounds proved
  separately; `RatioBounded F B p` in a new `LWE/Ratio.lean`; a family theorem with an explicit `PolyExpr` `pBoot`.
- **P6-Q13.** `barrington` is computable, so `fheEval` is.
- **P6-Q19 B with Seyoon's refinement.** Gen09 blocks nothing. **No docstring cites `[Gen09]`.** The leveled-scheme
  docstrings (`Leveled`, `LeveledSecurity`, A3) cite only [BV11, Thm 3.1, Def 3.6], [BV14, Thm 2.14 first part,
  Thm 3.7] and [AP14, §5.3], and carry r3 §H5.13's disclosure: "The key-chain construction and the hybrid order are
  reconstructed: no ingested passage gives them. BV11 and BV14 attribute leveled bootstrapping to Gentry's work; that
  passage will be cited here once it is ingested."
- **6a Q1 A (LE-ren).** No `TreeCircuit.rename`; reindex with the public `TreeCircuit.reidx`.
- **6b staging ruling (2026-11-17).** This base; the 6a targets as frozen statements; a re-pin if Gate 45 round 2
  changes anything (it closed CLEAR with no change).
- **Gate 45 G45-01 and the duplication standard** (G44-01, G48-01, GF-F01, GF-F02): see *Duplication* below.

## Ruling Q-6B-1 (staging question; the brief implements the recommended option)

r3's **G14** (`distAdv_fheView_le (h : WeakCircularSecure P χ D ε) : distAdv (fheView P χ false) (fheView P χ true) D ≤
ε`) is, word for word, the forward direction of `WeakCircularSecure`'s own `_iff` reader, and **A2**
(`fheView_negligible (h : WeakCircularSecureFamily F) (D) : Negligible …`) is the same for
`WeakCircularSecureFamily`. Under G45-01 neither may be an admitted target. The maintainer asked Seyoon:
- **A (recommended; implemented here).** No theorem: the readers `weakCircularSecure_iff` and
  `weakCircularSecureFamily_iff` are the statements, and the predicates' docstrings say that they are the security
  half of [BV11, Thm 3.2] and [BV14, Thm 2.14 second part]. `targets.txt` marks G14 and A2 *reader-only*.
- **B.** Keep both names as **proved citations** (`:= (weakCircularSecure_iff …).1 h`), never admitted, disclosed in
  *Overlap and reuse*, as LE-g45 kept `const_eval`.
- **C.** Keep them as r3 sketches them (admitted targets). Not recommended: G45-01 grades it a major.

A and B leave the admissions unchanged. If the dispatch prompt names a ruling other than A, follow it.

## Feasibility and size (maintainer's assessment)

Feasible as one job. Everything is statements and definitions; the only proofs are the readers (mostly `rfl` or
`Iff.rfl`), the definitions' own obligations (structure fields, `NeZero` instances, termination), the citations of
`targets.txt` and O2 (r3: 60–90 proved lines). Estimated surface: about **1,300–1,800 statement lines** in 9 new files
(8 under `GSW/`, `LWE/Ratio.lean`), O2 (about 60–90 lines in `BitEncoding.lean`) and the two facades. The heavy items
are the definitions with bodies: `select`, `homEvalPBP`, `homEvalFormula`, `decConstants`, `decryptFormula`,
`nandFormula`, `bootGate`, `fheEval` (computable through `runWith`), the leveled `levelKey`/`literalCts`/`leveledEval`
with their seed and view types, the hybrid `levelReduction`/`levelTerm`, the encodings and the A4 hypotheses. r3 §H7
projects 1,390–2,310 fill lines for U12–U19 later; every file must stay under 1,000 lines filled, so state compactly.

**Targets** (`targets.txt`, 25 r3 rows): **23 admitted targets** (24 if G17 is split into a pure and a leveled lemma),
**2 citations** (G11, L1: proved now if one step from `encrypts_encrypt`/`encrypts_keygen_encrypt`, else admitted),
**2 reader-only rows** (G14, A2; Q-6B-1), and O2's `decode_iff_mem_Ico` **proved**. Per unit: U12 3, U13 6, U14 5 + 1
citation, U15 1 (+ G14 reader-only), U16 2 + 1 citation, U17 2, U18 2 (or 3), U19 2 (+ A2 reader-only).

## Branches, series and delivery

- **Checkout.** In your own clone, fetch by name `cryptography/pass-shelat-ch2-4`, `land/gsw-6a-statements` and
  `land/gsw-6a-readers`. If a `land/` branch has moved past its pinned head, fetch `refs/pull/359/head` and
  `refs/pull/360/head`, or the pinned commits by hash; if you cannot get all three pinned commits (`d154c883…`,
  `cc05f76c…`, `036d8239…`), stop with **E-BASE**.
- **The base.** Run `bash <pack>/tools/mkbase.sh` in the clone: it must print
  `STEP1 04947bcf35e08ed5f3a4902b2637a77482fd32d2 tree 8eca961769fef59d5a22fd1b46dc821a614daf06` and
  `BASE 3e51b5f28900db6190f1eb2e6d207d27ee15d541 tree b69a66a385ca3439d56af1d6b9791b5847984fde`. Equivalently, with a
  work tree:

  ```sh
  export GIT_AUTHOR_NAME='TCSlib gsw-6b-statements staging' GIT_AUTHOR_EMAIL='staging@tcslib.invalid'
  export GIT_COMMITTER_NAME='TCSlib gsw-6b-statements staging' GIT_COMMITTER_EMAIL='staging@tcslib.invalid'
  export GIT_AUTHOR_DATE='2026-11-17T18:00:00+00:00' GIT_COMMITTER_DATE='2026-11-17T18:00:00+00:00'
  git checkout -b gsw-6b-step1 d154c8830fc8ffc52671b41992e7dbef61e30959
  git -c commit.gpgsign=false -c merge.log=false merge --no-ff --no-edit \
    -m 'gsw-6b statements base, step 1: merge #360 head cc05f76c (6a readers) into #359 head d154c883 (6a statements)' \
    cc05f76c43cd2d2f565ff0dfaec1c85b47e06d25
  git checkout -b gsw-6b-base 036d823933c8248bd8894c7963e15dd0f1837075
  git -c commit.gpgsign=false -c merge.log=false merge --no-ff --no-edit \
    -m 'gsw-6b statements base, step 2: merge the 6a drafts (step 1) into records tip 036d8239 (snapshot #6 Lean)' \
    gsw-6b-step1
  git rev-parse HEAD HEAD^{tree} HEAD^2   # 3e51b5f2…, b69a66a3…, 04947bcf…
  ```

  If a tree or a commit differs, stop with **E-BASE**. Record the output in `REPORT.md`. The base is not delivered as a
  patch.
- **Series 1, O2** (`owner/o2-decode`, from the base): only O2 (*O2* below). Proved; no `sorry`.
- **Series 2, statements** (`stmt/gsw-6b`, from series 1's head): every 6b file and the facades. Suggested commits,
  each compiling: (1) `GSW/Branching`, `GSW/DecryptFormula`; (2) `GSW/Bootstrap`, `GSW/Circular`; (3) `GSW/Leveled`,
  `GSW/LeveledSecurity`; (4) `LWE/Ratio`, `GSW/PolyRatio`, `GSW/Asymptotic`; (5) the facades `GSW.lean` and
  `LWE.lean`.
- Keep both branches local. Commit them with `git -c commit.gpgsign=false`: the series must be **unsigned**, so that
  `git am` reproduces every hash. The maintainer opens O2 and the statement PR (stacked on O2) after review; Seyoon
  approves and merges.
- **Deliver** every checkpoint and the final only under `inbox/fills/gsw-6b-statements/` on
  `exchange/pass-shelat-ch5-8`, in the standard payload (`workflow.md` §4.1):
  - `REPORT.md` (*Report*), naming the **full hashes of both branch heads it describes**;
  - `patches/o2/` (`git format-patch <base>..owner/o2-decode`) and `patches/stmt/`
    (`git format-patch owner/o2-decode..stmt/gsw-6b`), each with a `COMMITS.tsv`: one row per commit with its hash, the
    author's name, email and date, the committer's name, email and date, and its **signing** (`none`, or the format).
    Check in a scratch clone that `git am` at the base reproduces every hash of both series, and say so;
  - `src/`: every new or changed file at the `stmt/gsw-6b` head, under its repository path; `src-o2/`:
    `TCSlib/Cryptography/LWE/BitEncoding.lean` at the `owner/o2-decode` head;
  - `evidence/`, with its manifest `evidence/SHA256SUMS` (*Evidence completeness*);
  - a top-level `SHA256SUMS` of every delivered file except itself. The delivered paths must **equal** the manifests'
    paths: nothing missing, nothing extra, no leading `./`. Check this before each push.
- **Every checkpoint is a full payload for what it claims** (lesson G6A-C1-F01): its `REPORT.md` names the head hashes,
  its `patches/` run to those heads, and its `src/` holds every file it claims compiles, with the build logs that bind
  those sources to that head. A claim without `src/` and patches is not a claim.
- **Exchange commits.** Commit on the exchange as `stmt gsw-6b: checkpoint N` and `stmt gsw-6b: final`, with
  `git -c commit.gpgsign=false`. Pull with `git -c commit.gpgsign=false pull --rebase` (BSF-F01). After the rebase and
  before the push, `git cat-file -p HEAD | grep -c gpgsig` must print `0`. **The maintainer expects unsigned commits
  throughout**; if the platform signs one anyway, disclose it in the next commit, never rewrite or force-push.
- Push only your path; never force-push; never touch another path (other fills, gates, `outbox/`, `arora-barak-ch3-4/`,
  `lwe-sis-constructions/`). **Never push a campaign branch.** If a push is refused, keep the commit and say so.

## Base and parallel work

- **Open PRs at staging** (2026-11-17): #358, #359, #360 (in your base); #355 (cleanup Stage 1 promotions, stacked on
  #347): it adds declarations to `Cryptography/Asymptotic/Adversary.lean`, which 6b imports but does not edit, and none
  of its new names collides with a 6b name of r3; #347 (DW-5) and #362 (Arora–Barak blueprint) touch no 6b path.
- **Not at the base, reserved:** the GF-W1 promotions that land with the 6a fills (`TreeCircuit.maxDepth_le_of_forall`,
  `maxFaninL_le_of_forall` in `Basic.lean`; `prefixVal_eq_of_false`, `prefixVal_testBit` in `Adder.lean`; CarrySave's
  `depth_getD_le`, `maxFanin_getD_le` made public). Declare none of these names; if 6b needs such a fact, it is a scope
  request, never a restatement.
- If any PR merges during the job, **stay on the base**; the maintainer replays at landing (`workflow.md` §6.1). At
  delivery, record `git merge-tree --write-tree` of your head with the then records tip (information only).

## Scope

**New files** (namespace `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW`, except `LWE/Ratio.lean` in
`TCSlib.Cryptography.LWE`; r3 §H4):
- `TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/{Branching,DecryptFormula,Bootstrap,Circular,Leveled,
  LeveledSecurity,PolyRatio,Asymptotic}.lean`;
- `TCSlib/Cryptography/LWE/Ratio.lean`.

**Changed files:**
- `TCSlib/Cryptography/LWE/BitEncoding.lean`: O2 only (series 1).
- `TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW.lean` (facade): the eight new imports and their `## Contents`
  entries; its title and opening line may say that the folder now also covers bootstrapping and pure and leveled FHE.
- `TCSlib/Cryptography/LWE.lean` (facade): `import TCSlib.Cryptography.LWE.Ratio` and its `## Contents` entry.

`TCSlib.lean` already imports both facades' parents; it is **not** changed. No model or conversion is registered (6b
adds none), and `machine-library-design.md` is not changed: 6b consumes the registered hosts H18 (`evalWith`, in
`homEvalPBP`) and H19 (`runWith`, in `fheEval` and `leveledEval`), which name these consumers already. Each new
sketch names the host it uses (`workflow.md` §2).

**Frozen:** everything else, including every phase-5 GSW file (`Gadget`, `Noise`, `Scheme`, `Eval`, `Security`,
`Symmetric`), every other `LWE/` file, `Encoding/`, `Asymptotic/`, `Foundations/`, `Encryption/`, every 6a file and
everything #358, #359 and #360 touch, `ComputationalModels.lean`, `TCSlib.lean`, `machine-library-design.md`,
`blueprint/` and `audits/`.
- **Scope requests.** If a definition or statement needs a change to a frozen file (a reader, a promotion, an import
  that would create a cycle, a new module because a file would pass 1,000 lines), stop that line of work and ask
  Seyoon in your session, giving the file, the diff and the reason; proceed only on his approval. Record the request
  and his answer verbatim under `evidence/scope-request/` and in `REPORT.md`. Seyoon prefers routes with no frozen-file
  edit. A missing reader is never worked around by unfolding.
- **Known reader gap** (`census.txt`): `hybridPlant` (`Encryption/PublicKey/EnsembleSecurity.lean:110`) has no
  `_eq`/`_apply` reader. Your statements need not unfold it (define `levelReduction`/`levelTerm` through
  `hybridPlant` and phase-5 `reduction` as terms, as r3 §H5.14 says); list the gap in the census with the proposed
  one-line reader. It is the 6b analogue of 6a's `GadgetCorrect` gap, for an owner-side reader before the L4 fill.

## What to write

**For every new file:** the policy header (copyright block, precise imports, the three `set_option` lines, a module
docstring with `# Title`, `## Main definitions`, `## Main results`, `## References` with full citations of every tag
used: [BV14], [BV11], [AP14], [GSW13], [Pei16], [Bar89] as cited). Lines of at most 100 characters (Python `len`); every
file under 1,000 lines, target 150–600 filled (r3 §H7's estimates). No `@[simp]`, no global attribute. Identifiers
use the Greek `μ` (U+03BC), never the micro sign.

**Definitions.** Every r3 §H4 definition gets its body now, total and, where r3 says so, computable (`select`,
`homEvalPBP`, `homEvalFormula`, `bootNAND`, `bootGate`, `fheEval`, `leveledEval`; `fheEvalCircuit` and
`leveledEvalCircuit` are computable bodies around `toNANDForm`/`layerNAND`). Each new public `def` lands with its
readers, **proved**: `_eq` by `rfl` where that holds, case lemmas covering every input, `_iff` for predicates
(`Iff.rfl`), non-simp `simps` for structures and pairs (phase-5 `Security.lean` is the model:
`@[simps! (config := { isSimp := false }) fst snd]`). Each reader's docstring states its formula. Types that r3 names
loosely (`PublicKey P`, `Secret P`, `Seeds P χ`, `FheView P`, `LevelCoins P L`, `LeveledSeeds P χ L`,
`LeveledView P L`) are reducible abbreviations or definitions with readers, built from phase 5's types
(`Security.lean`'s view and seed types, `Regev.keygen`'s seed). Where a definition must carry a proof (an instance
such as `NeZero P.columns`, a structure field), prove it now; if you cannot, state it as a **target** lemma that the
definition cites, and list every such definition in the axiom report. Termination proofs are never admitted.

**Expected `sorryAx` dependents** (not targets): `fheEvalCircuit` reaches `sorryAx` through 6a's N2
(`nandGadget_correct`, via `toNANDForm`), and `leveledEvalCircuit` through N2 and N12–N13 (`layerGates_acyclic`,
`layerOutput_lt`, via `layerNAND`): Gate 45 r1 lists exactly `toNANDForm`, `toNANDForm_eq`, `layerNAND`,
`layerNAND_gates`, `layerNAND_output` as the 6a non-target constants that reach `sorryAx`. Any further 6b definition
that reaches `sorryAx` must be named, with the admitted declarations it goes through, in the dependency trace.

**Targets.** Every `target` row of `targets.txt` is a `theorem` whose body is `sorry`, with a docstring that:
1. opens with the statement in words, its formula written out (arguments in Lean order);
2. gives the `[TAG, location, anchor]` tag from r3 §H5 (anchors per r3 §H1), or says "Glue" for technical lemmas;
3. states every deviation from the source (r3 §H8 item 17: BV14's coordinate 1 against `σ 0`; the fan-in padding;
   literal inputs and layering; the carry-save tree inside `decryptFormula`; the reconstructed key chain and hybrid
   order; worst case against probabilistic, r3 §H8 item 10; the public output level; the evaluation key under the
   user's own `pk`);
4. ends with a `**Proof sketch.**` paragraph naming the steps a fill will follow (policy §3), with the readers, host
   lemmas and phase-5/6a lemmas it will use (by name; `pins.txt` gives where they are). The sketch is the fill's plan;
   a target whose sketch you cannot write is not ready.

**Citations** (`targets.txt` kind `citation`: G11, L1) are stated, and **proved now** when the proof is one step from
the public lemma after reading the file's own definition (LE-g45's `const_eval`); otherwise admitted. `REPORT.md` says
which, and *Overlap and reuse* names the public lemma.

**Names and shapes** are fixed now. Adjust a name, binder or argument order where Lean requires it, keeping the
meaning; record each change in `REPORT.md` § *Statement changes against r3* with the reason. A change of meaning (a
weaker or stronger statement, a new hypothesis) needs a probe that shows r3's form false or unprovable, and goes to
Seyoon as a question in the report; never silently. Settle every constant marked *(fix)* (`decDepth_le`,
`bootNoise_le`, `pBoot`) by hand and with `decide`/`#eval` checks, and record the derivation; the ledger of r3 §H6 is
the target, with **no depth term linear in `ℓ`** (r3 §H3.3, §H8 item 1).

**File-specific notes** (r3 §H5 has the sketches; these are the known pitfalls):
- **Branching (G1–G3).** `select P C U V := mul P (gadget P − C) U + mul P C V` (fresh selector on the left, Gate 41).
  `homEvalPBP P B cts V := B.evalWith (select P) cts V` consumes the H18 host; G2 is stated for
  `B.IsPermutation`, start `Pi.single s₀ (gadget P)`, noise `B.length * (2 * (P.columns * β))`. `homEvalFormula`
  runs `barrington c σ` for one fixed five-cycle (`sigma1` is fine) and reads **coordinate `σ 0`**, not BV14's
  coordinate 1 (C16 `barrington_yield_zero`; G6A-F11, Gate 45 r1 "C16 reading": coordinate `0` would encode the
  complement). Barrington needs `[NeZero k]`.
- **DecryptFormula (G5–G8).** `keyBits P s := decomposeVec P (secretVector P s)` (the bits `evk` encrypts, P6-Q8);
  `decConstants P C : Fin P.columns → ZMod q` is `Gᵀ` applied to `decryptColumn P C` (r3 §H3.2);
  `decryptFormula P C := modSumInterval (fun i => (decConstants P C i).val) q (decodeLo P.lwe) (decodeHi P.lwe)` (F9
  with O2: `modSumInterval_eval` needs `a i < q`, `lo ≤ hi ≤ q`); `nandFormula P C₁ C₂ :=
  (and2 (decryptFormula P C₁) (decryptFormula P C₂)).neg`, **one key block** (r3 G7). `decDepth P` is built from
  `modSumDepth` (F10). The formulas' input count `P.columns` needs `NeZero` for Barrington; `P.lwe.modulus ≥ 2` and
  `modulus ≤ 2 ^ width` give `width ≥ 1`.
- **Bootstrap (G9–G13, G18).** `bootNoise P β = 4 ^ (decDepth P + 1) * (2 * (P.columns * β))`; G9 in the
  key-switching form (`evk` under `t'`, decryptions under `s`, no hypothesis on `C₁, C₂`); `bootGate` pads fan-in 1 to
  `(a, a)` and fan-in 0 to `(G, G)` and is the `runWith` gate function of `fheEval` (H19); `fheEvalCircuit P evk Cc hC
  cts := fheEval P evk (Cc.toNANDForm hC) cts`; `evalKey P pk s R i := encrypt P pk (keyBits P s i) (R i)` (P6-Q8).
  Compactness by typing goes in the docstrings of `fheEval`, `fheEvalCircuit` (and `leveledEval`), no theorem.
- **Circular (G14–G15).** `fheView P χ μ` samples honest keys and returns `(pk, evalKey …, encrypt pk μ R)`
  [BV14, §2.5, p007-b001]. `WeakCircularSecure P χ D ε` per distinguisher (P6-Q15 A), with its `_iff` reader; its
  docstring explains why per distinguisher (an unbounded function recovers `s`). G14 per Q-6B-1. **G15** is stated
  over the evk-dropped projection of `fheView` (the view `(pk, encrypt pk μ R)` read off `fheView`'s seeds), so that its
  content is the transport of phase-5 `distAdv_encrypt_le` (`Security.lean:248`) along the coin regrouping; stated over
  `realView` it would restate that theorem (G45-01).
- **Leveled (L1–L3).** r3 §H5.13 exactly: `levelKey … (d : Fin L)` encrypts `keyBits P (ss d.castSucc)` under
  `pks d.succ`; `literalCts P cts := Fin.append cts (fun j => homNot P [cts j])` in `litInput`'s order;
  `leveledEval` runs `runWith` over a layered NAND circuit on `k + k` inputs, a gate at level `d ≥ 1` (its `depthAt`) is
  `bootGate` with `levelKey ⟨d − 1, _⟩`; `leveledEvalCircuit := leveledEval … ((Cc.toNANDForm hC).layerNAND)
  (literalCts P cts)` with `[NeZero k]`. Decryption uses the public output level `Cc.depth` (disclosed; BV11 Def 3.6's
  `Dec` is level-agnostic). The P6-Q19 disclosure in every docstring of this file.
- **LeveledSecurity (L4–L5).** The view of the `L+1` public keys, the `L` level keys and `Enc_{pk_0}(μ)`; the
  hybrid top-down (`d = L, …, 1`, then the phase-5 challenge step); `levelReduction` composes `hybridPlant` with
  phase-5 `reduction`, and `levelTerm` is its two DLWE advantages plus `2 · (N · Regev.extractionError)` (the shape of
  `distAdv_encrypt_le`'s right-hand side); r3 §H8 item 12: each step's messages are random bits of `s_{d−1}`, fixed
  inside the reduction's coins. Reuse `distAdv_multi_le_sum` and `abs_sub_le_sum_hybrids`, never a local hybrid lemma.
- **Ratio and PolyRatio (G16–G17).** `LWE.Family.RatioBounded F B p` with `_iff`; `Parameters.ofFamily F κ` with
  `lwe := F.parameters κ`, `width := F.residueBits.eval κ`, `modulus_le := F.modulus_le_pow κ`, non-simp `simps`
  (type-level Rule 10: `(ofFamily F κ).lwe` against `F.parameters κ` only through those readers); `pBoot` an explicit
  `PolyExpr`.
- **Asymptotic (A1–A3).** Encodings from `LWE.encodeChallenge` and `Encoding.Modular.encodeMatrix` (with `_eq` and
  `_length` readers); `WeakCircularSecureFamily`, `ReductionEfficient`, `LeveledReductionEfficient` exactly in r3
  §H5.16's quantifier structure (domination, not construction; the advice remark), each with `_iff`. A1 and A3 from the
  unchanged `LWE.DLWEAssumption` (`dlweAssumption_iff`, `Family.advantageAt_eq`; `Pseudorandom/Generators/LWE/
  Basic.lean`'s `pseudorandom_under_DLWE` is a model of the reading). `negligible_polyExpr_mul` exists twice
  (`Asymptotic/EnsemblesLemmas.lean:377`, `SecureComputation/ComposeSecurity/Probability.lean:110`) and as
  `Negligible.polyExpr_mul` (`Asymptotic/ReductionSupport.lean:267`): cite one in the sketches (r3: `EnsemblesLemmas`)
  and add no fourth.

## O2 (series 1; owner-side, proved)

In `TCSlib/Cryptography/LWE/BitEncoding.lean` (namespace `TCSlib.Cryptography.LWE.BitEncoding`), after `decode_eq`,
add r3 §H5.8:
- `def decodeLo (P : Parameters) : ℕ` with `decodeLo_eq : decodeLo P = P.modulus / 2 / 2 + 1`;
- `def decodeHi (P : Parameters) : ℕ` with `decodeHi_eq : decodeHi P = (P.modulus + P.modulus / 2 + 1) / 2`;
- `theorem decode_iff_mem_Ico (P : Parameters) (v : ZMod P.modulus) :
  decode P v = true ↔ decodeLo P ≤ v.val ∧ v.val < decodeHi P`, **proved** (r3: 60–90 lines), reading `decode`,
  `distance` and `codepoint` through `decode_eq`, `distance_eq`, `codepoint_eq` and Mathlib's `ZMod.valMinAbs` lemmas.
  `tools/o2check.py` finds 0 mismatches for every residue of every `2 ≤ q ≤ 2000`.

Each with a formula docstring ("Glue for the file's `decode`", r3), and a `**Proof sketch.**` on the theorem. Update the
module docstring's `## Main definitions`/`## Main results`. Nothing else in the file changes. Evidence: decls2 exactly
5 ADDED, 0 CHANGED, 0 REMOVED; the frozen check of `BitEncoding.lean` (insertions only); axioms standard only; the
seal of `BitEncoding.lean` with a paired control on `decodeLo`/`decodeHi`; the sweep of its 18 `DOWN` modules.

## Multi-agent work (up to 3 sub-agents) and Lean parallelism

- **The lead owns the job:** both branches, every commit, the integration, the sweep, the root build, the seals, the
  delivery and `REPORT.md`. Only the lead commits on `owner/o2-decode` and `stmt/gsw-6b`, runs `lake`, fetches the cache
  and pushes.
- **Suggested split** (disjoint files; record any other split in `REPORT.md`). The files depend on each other's
  definitions (statements, not proofs), so order matters: the lead does O2, `Branching`, `DecryptFormula`,
  `Bootstrap` and `Circular` first (checkpoint 1); then sub-agent `lev` writes `Leveled` and `LeveledSecurity`, and
  sub-agent `asy` writes `LWE/Ratio`, `PolyRatio` and `Asymptotic` (its `LeveledReductionEfficient` waits for `lev`'s
  `levelReduction`); sub-agent `probe` writes the probes and the census, clash and duplication scans under
  `evidence/`. Sub-agents may draft from r3 before checkpoint 1 but compile only from the lead's commits.
- **No cross-file copies** (GF-F02): a definition or lemma that two files need is stated once, public, with its
  reader, in the upstream file, and imported; never a `private` copy in each.
- Each sub-agent owns its files exclusively, works in its own git worktree with its own TCSlib olean tree and
  `.lake/packages` linked to the lead's, and hands its files to the lead as patches. Sub-agent logs go under
  `evidence/subagents/<name>/`; `REPORT.md` records who wrote what.
- **Lean pool** (addendum, *Adaptation*; `workflow.md` §4.1): all agents share one memory-sized pool of Lean processes
  (a counting semaphore), at most `nproc` and keeping about 2 GB or 15% of memory available, in dependency order,
  never two processes on one module or one output file. Record the pool size, its changes and peak memory.

## Proof discipline for the proofs this job does write (readers, obligations, citations, O2)

- **Rule 10 (readers only; policy §1).** Read other files' definitions only through their published readers and
  lemmas, including generated matchers and projections. Core and Mathlib definitions may reduce in a `rfl`, `decide` or
  `show` step but are never passed to `simp`, `rw` or `unfold`. Each new file may read its own definitions directly;
  the new files are foreign to each other and to every other file.
- **Duplication (binding; policy §1; G45-01, G44-01, G48-01, GF-F01, GF-F02).** **Search TCSlib, core, Batteries and
  Mathlib before stating any definition, helper or target that might already exist**: by name, by `exact?`/`apply?`
  on its statement in a scratch probe, and by grep for its conclusion's shape. Then:
  - **No restatement of a public lemma.** A target, citation or helper whose statement is a public lemma's (exactly,
    up to argument order, or behind a new definition that unfolds to the old one) is not written: cite the existing
    lemma. An admitted restatement is a major (G45-01), disclosed or not; disclosure is not acceptance (G44-01).
  - **No re-derivation.** An inline proof of a Mathlib or TCSlib fact is a major (G48-01, GF-F01): use the lemma.
  - Specializations to a new definition are allowed as *citations* (above) and disclosed in *Overlap and reuse*.
  - Known near-relatives to check and disclose: phase-5 `eval_encrypts`/`decrypt_keygen_eval` (the leveled
    multiplicative evaluation, a different scheme from `fheEval`); `homGate`/`homNot` (reuse `homNot` for the negative
    literals, never a copy); `encrypts_encrypt`/`encrypts_keygen_encrypt` (G11, L1); `distAdv_encrypt_le` (G15);
    `view`/`realView`/`reduction` (reuse in `fheView` and the hybrid); `Regev.extractionError`; `decode_codepoint_add`
    (O2 must not re-prove it); `vecMul_secretVector_augmented`, `gadget_mulVec_decomposeVec` (G5);
    `Encrypts.nand` (the leveled multiplicative NAND, r3 §H2, not bootstrapping's); the three `polyExpr_mul` copies.
- **Docstrings and sketches (policy §2–§3).** Every public declaration has a docstring stating it in words with its
  formula. Every proof of about 20 lines or more has a `**Proof sketch.**`. Never fabricate a quotation, location or
  anchor; glue says "Glue".

## Checks and evidence

Run Python as `python3 -I`. Never run `lake build` or an unfiltered `lake exe cache get`; compile each module with
`scripts/lean_check_tree.sh` (the addendum). Count errors in both forms (`^\S+\.lean:\d+:\d+: error[:(]`) in every
log, and keep every raw log.

1. **Bootstrap and sweep.** Bootstrap `prefix.txt` (288 modules) at the base: rc 0, 0 errors, and exactly the `sorry`
   warnings of `base-sorries.txt` restricted to it. Insert the new modules after their imports (facades after their
   children; `evidence/build/order-final.txt`). At the O2 head and at the final head, rebuild every module whose source
   differs from its olean's, then check every `DOWN` module of `closures.txt` (18) and the 9 new ones, each rc 0 and 0
   errors in both forms. Bind every checked source to `git show HEAD` (`evidence/build/summary.txt`: module, rc, errors
   in both forms, `sorry` warnings, source SHA-256).
2. **Root build.** Build the rest of `order.txt` (1,443 modules) and the root `TCSlib` last, from the final head:
   `evidence/build/root/summary.txt`. If the host cannot finish, follow the addendum (marked incomplete, not a failure).
3. **Statements.** `python3 -I briefs/pass-shelat-ch5-8/maintainer/tools/decls2.py . <base> <files…>` over every new
   and changed Lean file (ADDED/CHANGED/REMOVED against the base: only ADDED, and in `BitEncoding.lean` exactly O2's
   five), and a `StmtDump` probe printing every new constant with its full name and type. `REPORT.md` maps every row of
   `targets.txt` to its declarations (kind as delivered: target, citation proved, citation admitted, reader-only), and
   lists every definition with its readers.
4. **Admissions, exact.** At the O2 head: exactly `base-sorries.txt` (289 declarations in 55 modules). At the final:
   exactly those plus the delivered targets, **23 to 26 declarations in the 8 new GSW files** (`targets.txt`, *Counts*),
   none in `LWE/Ratio.lean`, `BitEncoding.lean` or a facade. A script compares the root build's `sorry` warnings (or,
   if the root is incomplete, the sweep's plus the syntactic scan of `tools/graph.py`) with that list name for name.
5. **Axioms.** Print the axioms of every declaration and auxiliary constant of the new and changed modules. Expect
   `propext`, `Classical.choice`, `Quot.sound` only, except `sorryAx` in exactly the targets and in the definitions and
   readers that reach an admitted proof (expected: `fheEvalCircuit` through N2; `leveledEvalCircuit` through N2, N12,
   N13; their readers and anything stated through them, named). Run a **dependency trace** that walks each constant's
   closure and names, for every constant reaching `sorryAx`, the admitted declarations through which it does (6a
   targets or 6b targets). O2's constants: standard axioms only.
6. **Rule 10.**
   - **Seals** A and B, strict and coe (**coe-A canonical**), with `-DmaxErrors=0`, over the full TCSlib import closure,
     of every new file, of `BitEncoding.lean` at the O2 head and the final head, and of the two facades. Report each
     seal's request count and every failing declaration, attributed by its raw log; **no failing declaration**. Use
     chunking (`SEAL_CHUNK`) if a run overflows.
   - **Paired controls on every new owner** (the 9 new files and `BitEncoding.lean` for O2): a negative control that
     reads one of its new definitions from another file by `rfl`/`Iff.rfl`/`unfold` (passes unsealed, fails sealed
     exactly once) and a positive control through its published reader (passes sealed). Pretest unsealed; strict and
     coe both. A file that defines nothing gets no pair, and the report says so.
   - **Notation, never sealed:** reducible abbreviations (`Parameters.columns`, `Ciphertext`, the new type
     abbreviations), `PolyExpr.eval`, projection coercions, the `FinDist` coercion (DW-10 Q3).
   - **Explicit-unfold scan** over the new and changed files: 0 foreign.
   - **Reader census** (G6A-F03): for every foreign definition a definition body or a target's sketch reads, its
     reader (`path:line`) or MISSING with the proposed one-line reader. `census.txt` is the staging census (static;
     confirm each entry and add what it misses). Expected MISSING: `hybridPlant`. Every MISSING reader is listed in
     `REPORT.md` as a fill prerequisite for Seyoon (6a's Q3 precedent), never worked around.
7. **Probes** (under `evidence/probes/`, outside the library, against the final tree; kernel `decide` or `rfl` where the
   kernel can reduce, otherwise `#eval` output recorded as evidence, never as a proof; never `native_decide`). One probe
   for each statement that could be wrong, on toy parameters (for example `n = 1`, `q ∈ {4, 5, 8}`, `ℓ = 3`):
   - P1 *selector*: `select` on noise-free encryptions of bits gives `(1 − b)·u + b·v`; G1's noise bound on small
     error vectors.
   - P2 *PBP and formula*: `homEvalPBP` on a permutation program and `homEvalFormula` on a depth-2 formula, noise-free:
     coordinate `σ 0` encrypts the formula's value (and coordinate 0 its complement), on every input.
   - P3 *O2*: `decode_iff_mem_Ico` by kernel `decide` for every `q < 64` (and `#eval` beyond).
   - P4 *decryption formula*: `decryptFormula P C` on `keyBits P s` equals `decrypt P s C` for every `s` and sampled
     `C`; `nandFormula`; `decConstants` against G5's sum.
   - P5 *bootstrapping*: `bootNAND` and `fheEval` noise-free on an XOR circuit in NAND form, including fan-in 1 and 0
     gates (the padding).
   - P6 *leveled*: `literalCts`, `leveledEval` and `leveledEvalCircuit` on the XOR and odd-gap circuits of 6a's probe P9
     with noise-free keys: the output decrypts under the key of the circuit's depth.
   - P7 *constants*: `decDepth_le`, `bootNoise_le` and `pBoot` numerically over a range of `(n, q, ℓ)`; no term linear
     in `ℓ` in `decDepth`.
   - P8 *types*: every asymptotic statement instantiated at a sample `LWE.Family` elaborates; `ofFamily`'s readers.
8. **Frozen-file check.** A `python3 -I` script that extracts every declaration of each changed existing Lean file at
   base and final and compares headers and whole definitions byte for byte, allowing only O2's insertions in
   `BitEncoding.lean` and the imports and docstring in the two facades; with controls (one altered character reports
   exactly one difference; one deleted reader reports exactly one removal). `git diff --stat <base>` lists only the
   9 new files and the 3 changed ones. Output under `evidence/headers/`.
9. **Lint.** `python3 -I scripts/style_lint.py <new and changed Lean files>`: 0 findings (0 in the three changed files
   at the base). `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography --check8b` at base and final; the
   maintainer's run at the base: **92 FAIL / 104 WARN over 529 files** (`AdvancedEncryption/Homomorphic` 0 / 0 over
   7; `LWE` 0 / 1 over 9, the pre-existing `DLWEAssumption` check-8 WARN). Diff the line sets: no new FAIL line, and
   no new WARN line except one you disclose and justify.
10. **File sizes.** Lines and maximum width of every new and changed file, at both heads, with a `python3 -I` script,
    against r3 §H7's fill estimates (every file must stay under 1,000 lines filled).
11. **Name-clash and shadow scans.** (a) No new full name, public or private (namespaces resolved), is already declared
    in `TCSlib/` or `audits/` at the base, or in #355's head `d3c7cb00092ad5913904654d922f30fc7d5fce4a`, or is a GF-W1
    reserved name. (b) List every new short name that exists elsewhere (`pins.txt` shows several: `encrypt`, `view`,
    `realView`, `reduction`, `decrypt_eq`). (c) Show that no unqualified use in a `DOWN` module changes its resolution.
12. **Reuse and overlap** (`REPORT.md` § *Overlap and reuse*), with the searches you ran: for every new declaration that
    restates, specializes or re-proves existing material, its nearest relative (`path:line`), the relation and why it
    is not reused; confirm or correct each r3 §H2 cryptography finding and every near-relative listed under
    *Duplication*. Any exact restatement found is removed before delivery, not disclosed.
13. **Reproduction.** `git am` of both patch series at the base, in a scratch clone with `COMMITS.tsv`'s committer data,
    reproduces every hash; `src/` and `src-o2/` equal the heads' files byte for byte.

**Checkpoints** (at least one mid-way): checkpoint 1 is O2 complete (its series, checks 1, 3–6, 8 for it) with
`Branching`, `DecryptFormula`, `Bootstrap` and `Circular` compiled, delivered with `src/`, both patch series and the
head hashes; the final has everything.

If a probe shows an r3 statement false, stop that line, keep r3's form out of the branch, and put the counterexample
and your proposed statement in `REPORT.md` as a question for Seyoon. Do not weaken a statement silently.

## Sources and citations

- Cite only ingested passages: [BV14], [BV11], [AP14], [GSW13], [Pei16], [Bar89] at the base, with the anchors of
  r3 §H1. **Never fabricate** a quotation, location or anchor. **No `[Gen09]`** anywhere (P6-Q19 B); the leveled
  disclosure text instead. Glue declarations carry no tag and say "Glue".
- Record point (r3 §H1): BV14's "[BV11, Lemma 4.1]" (Prop 3.4) is **Lemma 4.5** in the BV11 version held; cite
  [BV11, Lemma 4.5] and note BV14's numbering.
- Do not add reference files, edit `blueprint/` or run `scripts/sources.py`.

## Report

`REPORT.md` gives: the base (`mkbase.sh` output or the merge reproduction), the records tip seen at delivery and the
merge-tree with it, both heads (full hashes) and every commit; the preflight figures, the pool and peak memory, and
who wrote what; the statement list (check 3) with the `targets.txt` row map; the definitions and their readers;
§ *Statement changes against r3*; the constants settled with their derivations; Q-6B-1 as applied; the builds (checks
1–2); admissions (check 4); axioms and the dependency trace (check 5); the Rule 10 seals, controls and reader census
(check 6); the probes (check 7); the frozen-file check; lint; sizes; the clash scans; § *Overlap and reuse*;
§ *Scope requests* (none, or each with Seyoon's answer); the reproduction; questions for Seyoon, if any, numbered
`G6B-W1`, … with the recommended option first; the evidence, with its manifest.

### Evidence completeness

Every file that `evidence/SHA256SUMS` names is delivered: build, sweep and root logs with their summaries, the
admission comparison, decls2 output, the `StmtDump`, the axiom prints and the trace, seal and control sources,
manifests, request records and raw logs, the unfold scan, the census, the probes and their outputs, the frozen check
with its controls, lint outputs, the size script and output, the clash and shadow scans, the duplication searches, the
reproduction log, sub-agent logs, `pool.log` and the tools used. If the evidence is too large for one commit, deliver
it in several commits or numbered ZIP parts, each with an entry list; leave nothing out for size.

## Blockers: stop and report

- **E-RES (environment).** The addendum's preflight or cache rules fail. Stop and report the numbers.
- **E-BASE.** The pinned commits cannot be fetched, or `mkbase.sh` (or the merge recipe) gives another tree or commit.
- **E-SCOPE (frozen files).** A definition or statement needs a reader, promotion, import or module the *Scope* does
  not permit. Stop that line and ask Seyoon (*Scope*); continue the other files meanwhile.
- **E-ROUTE (statement).** An r3 statement looks false, vacuous or unstatable as sketched, or its only form restates a
  public lemma. State the exact issue with a counterexample probe or the existing lemma, and propose a form.
- **How to report.** Push a checkpoint `stmt gsw-6b: checkpoint N (blocked: <code>)` whose `REPORT.md` opens with the
  blocker, the exact obligation or request, and the logs. Keep everything that already passes. Never work around a
  blocker by weakening a statement, editing a frozen file without approval, unfolding a foreign definition, or using a
  private stand-in.

The maintainer replays both series on the then records tip, reviews them (static, then a merged-tree replay), and
opens O2 and the statement PR for Seyoon; Gate 46 follows.

**Ready to dispatch**
