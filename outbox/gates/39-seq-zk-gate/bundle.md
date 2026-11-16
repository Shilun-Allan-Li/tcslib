## ===== briefs/pass-shelat-ch5-8/gates/39-seq-zk/pack.md =====

# Gate 39 · Sequential repetition preserves zero knowledge and interactive proofs (`seq-zk`, [PS10, Theorem 175.1])

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews).

- **PR:** draft [PR #327](https://github.com/Shilun-Allan-Li/tcslib/pull/327) at
  `bd19c433a4cf3d4027ffc891d7d3c06e927e9dfa` (branch `land/pass-shelat-seq-zk`, tree
  `cc520026f83524433328359af759084d23cabd0e`).
- **Target and base:** the PR targets `cryptography/pass-shelat-ch2-4` on base
  `05d26fe5b41fcb9426ec220d877d03264b9c8e8c` (the merge base).
  - The fill was issued on `107f1e8c218733eac12d6b9bee6fece441271317`. The 41 PR paths are byte-identical at the
    issue base and at `05d26fe5` (`pack-checks/rebase.txt`). The Lean delta between them (29 files) is covered by the
    review's build.
  - The records tip is now `c2f6adeb3f3de2a21352a57e64c6a11a79cc220e`. Since `05d26fe5` it has merged #313
    (learning) and, on 2026-11-16, #318 (sc-ot), #319 (canonizer) and #323 (sc-garble).
  - `pr.diff.txt` is `git diff origin/cryptography/pass-shelat-ch2-4...bd19c433`, which equals `05d26fe5..bd19c433`
    byte for byte (41 paths, 6652 insertions, 14 deletions).
  - **Open PRs and the tip.** `git merge-tree --write-tree` of the head with the tip, #324 and #326 (and with the merged
    heads of #318, #319, #323) is clean in each case, and no path is shared. The combined build of all open PRs covers
    the merged state (question 9). **Pending merge condition** (not an audit item): the merge order, #324 last.
- **Commits:** 7 (`pack-checks/rebase.txt`), all committed by Claude and SSH-signed.
  - The Codex worker's 6 commits, made by a lead and three sub-agents on Seyoon's Mac. The author, Seyoon Ragavan,
    is kept. They were applied with `git am` with the delivered committer data; the 6 worker hashes reproduce
    unsigned.
  - They were rebased onto `05d26fe5`: `git range-diff 107f1e8c..d842dc8f 05d26fe5..e9b5ea47` is 6/6 `=`. At
    `e9b5ea47` the 41 files are byte-identical to the worker's `src/` (exchange `a6be22fa`).
  - Landing edit **LE-doc** `bd19c433a4cf3d4027ffc891d7d3c06e927e9dfa` (S-02): formula docstrings for 81 new public
    declarations, docstrings only. Author and committer Claude.
- **Scope:** a **proof audit** of five admitted, frozen statements in `Composability/SequentialZK.lean`
  ([PS10, §7.2.1, Theorem 175.1]; [Gol01, §4.3.4]):
  - `ZK.seqRep` (:866);
  - `StatZK.seqRep` (:884), with error `Q · δ`;
  - `InteractiveProof.seqRep` (:930);
  - `InteractiveProofErr.seqRep` (:958), with soundness error `s^Q`;
  - `EfficientProverProofErr.seqRep` (:976).

  They passed the prong C statement phase, Gate 03 (rulings G3-3, G3-4, G3-7d) and Gate 06, and are frozen. Their
  proved consumers `PerfectZK.seqRep`, `PerfectZKAbort.seqRep` and `Composability/ThreeColoring.lean` (Theorem 124.1)
  become standard with them.
- **Brief:** `fills/seq-zk/issued-r1/brief.md` on the records branch (SHA-256 `d8b9feec…`), in `verification.zip`.
  It sets four checkpoints (the IP case; the error and efficient-prover cases; StatZK; ZK) and the owned file plus
  `SequentialZK/`. It also sets the frozen-statement rule, the edge cases, Rule 10 (projection coercions and
  `PolyExpr.eval` as notation, coe seals canonical), the docstring and sketch rules, the G26-N1 error count and the
  evidence-completeness rule.

Lean paths below are under `TCSlib/Cryptography/`; `SQ/` is `Composability/SequentialZK/`.

## What changed

41 Lean files (`source-head.json`; every line at most 100 characters; the largest file is the owned one, 990 → 992
lines):
- the owned `Composability/SequentialZK.lean`: the five proofs; 12 new declarations (execution readers such as
  `exec_boundary_lengths` and `seqRep_outV_eq`, `seqRep_complete`, `seqRep_sound_first`, `seqProver_efficient`,
  `seqVerifier_efficient`, `ProverBounded.seqRep`, `seqRep_proverSpec`, `seqRep_verifierSpec`); the imports and the
  module docstring;
- **39 new helpers under `SQ/`** (60–370 lines each). They cover the phase structure, the repeated verifier and its
  soundness, the continuation probability and endpoint sampling, the prefix and suffix laws, the normalized simulator
  `S_Q` (`SQ/Normalization*`, `SQ/SuffixMachine`, `SQ/SimulatorMachine`), the statistical recursion and the
  computational hybrid with its non-uniform phase reduction (`SQ/Computational*`, `SQ/WrappedVerifier`);
- `ZeroKnowledge/Defs.lean`, **+11 lines**: the `Iff.rfl` reader `StatZK_iff` (S-01) with its formula docstring.

**The proof** (review § *content*; the worker's REPORT): each target is a short instantiation.
- `ZK.seqRep` is `SequentialZK.zk_of_padded_spec h hB Q (fun x => π.seqRep_proverSpec Q x)`. It uses the wrapped
  verifier `V*` and the normalized simulator `S_Q` (one verifier tape, `Q(|x|)` calls of `S` on fresh coin blocks,
  canonical normalization and fallback). It applies `ZK π R` at the enlarged auxiliary bound `Lz'`, with a non-uniform
  phase reduction that fixes a maximizing phase and bounded prefix as advice. The sum of the `Q(n)` gaps is
  `Q(n) · ε(n)`.
- `StatZK.seqRep` is `statZK_of_padded_spec`: the conditional hybrids and the triangle inequality give exactly
  `Q(|x|) · δ(|x|)`.
- `InteractiveProof.seqRep` uses `seqVerifier_efficient`, `PaddedProverSpec.complete` and soundness from phase 0
  (`seqRep_sound_first`).
- `InteractiveProofErr.seqRep` uses `(seqRep_verifierSpec Q x).sound`: soundness `s^Q` by conditioning on the prefix
  and induction on the phases. `hQ` is unused, which is disclosed.
- `EfficientProverProofErr.seqRep` adds `seqProver_efficient`, `ProverBounded.seqRep` and `seqRep_complete`.

**Statements** (`evidence/statements/`, re-checked in `pack-checks/headers.txt`, `shared.txt` and `decls2-*.tsv`):
- decls2 from the issue base and from `05d26fe5` to the head gives **196 ADDED, 0 CHANGED, 0 REMOVED**; 0 rows for
  LE-doc.
- The frozen check (`landing/frozen-check.txt`) takes `SequentialZK` from 27 to 39 declarations and `Defs` from 35 to
  36. It finds 0 header, prose or definition-body differences; the control (one header character of `ZK.seqRep`)
  gives exactly 1.
- `touched`: 5 CHANGED (the targets), 13 ADDED in existing files (12 owned, plus `StatZK_iff`), 190 in new files and
  57 UNCHANGED.
- Re-checked from git objects:
  - the 27 + 35 pre-existing headers and every definition block are identical, in order;
  - the five targets' headers are byte-identical and their bodies have no `sorry`;
  - **of the five target docstrings, only `StatZK.seqRep`'s differs from the issue base** (one sketch hunk). The other
    four are the statement-phase sketches, unchanged. LE-doc touched none of the five.

## Rulings and records in force

1. **S-01, confirmed by Seyoon (2026-11-16):** `StatZK_iff` (`Iff.rfl`) in the frozen `ZeroKnowledge/Defs.lean`, as
   approved in the worker's session (`worker/evidence/scope-request/`). Its added lines equal the approved patch apart
   from the position of one blank line (`pack-checks/shared.txt`); LE-doc adds its formula.
2. **The worker was Codex**, on Seyoon's Mac, as a lead with up to three sub-agents and a host-wide 3-slot Lean cap
   (Seyoon, 2026-11-15; `records/…/fills/codex-host-2026-11-15/`). The brief's header line "Worker Claude" is from
   issue.
3. **Rule 10 notation** (as the brief):
   - `PolyExpr.eval` (Q1, the user, 2026-11-07): seal A exempts it and is canonical;
   - reducible abbreviations;
   - projection coercions such as `FinDist`'s `⟨FinDist.prob⟩` (Seyoon, 2026-11-14). **coe-A is canonical**.
4. **The deviations in the owned file's module docstring** were fixed at the statement phase: filler moves;
   **strict-PPT simulators and bounded abort retries** (ruling G02-#4, D8); bounded prover messages (`ProverBounded`,
   G3-3); at least one phase for soundness.
5. **LE-doc (the maintainer's landing edit, S-02): docstrings only.**
   - For 81 of the review's 88 NO-FORMULA rows, it adds the declaration's own Lean conclusion (60 rows), or for a
     `def`/`abbrev` its `_eq` reader's (13), as a backticked formula at the end of the statement prose. 8 are written by
     hand (`statements/seq-zk-overrides.tsv` in `landing-ledoc/`).
   - The other 7 rows are the **5 frozen targets**, whose statement prose the brief freezes (left as is, as the
     sc-compose LE-doc did), and `ProverBounded.seqRep` and `zk_of_padded_spec`, which already state their conclusion.
   - **11 conclusions longer than 240 characters are cut at a space and end in " …"** (the sc-compose LE-doc rule;
     question 7).
6. **Uniformity (the uniformity audit of 2026-11-16, findings `7d398d16`, in `verification.zip`).** The convention is
   uniform simulators, with adversaries and distinguishers non-uniform.
   - #327's `exists_phaseSimulator` builds `SQ` with `SQ.Uniform` explicitly, by `NUPPT.ofPolyTimeUniform`
     (`SQ/SimulatorMachine.lean:310–344`). The audit grades it **OK**: lifted verifiers use auxiliary data, and the
     phase and repeated simulators are explicitly uniform; no new uniformity defect.
   - Its other findings (DW-1 to DW-3) concern HBC and non-malleability definitions and are deferred.
7. **The facade-completeness lint baseline (#305):** 92 FAIL / 101 WARN (Cryptography), 25 / 391 (Complexity).

## What is frozen

- **The five targets' statements and statement prose**, and every pre-existing declaration of `SequentialZK.lean` and
  `ZeroKnowledge/Defs.lean` (header bytes, order, whole definitions), in particular the construction (`seqProver`,
  `seqVerifier`, `seqRep`) and its readers, and `ZK`, `StatZK`, `PerfectZK`, `PerfectZKAbort` and `AbortRetry`.
- **Every other file**, in particular `ZeroKnowledge/Interaction.lean`, `InteractiveProofs.lean`,
  `Composability/ThreeColoring.lean`, `Asymptotic/*` and `Games/*`.
- **The landing edit:** LE-doc, 81 docstrings.

## Questions for the audit

**1. Correctness against [PS10, Theorem 175.1] and [Gol01, §4.3.4]**
- **`ZK.seqRep`:**
  - Is the normalized simulator `S_Q` a **uniform strict PPT**, with one verifier tape, `Q(|x|)` calls of `S` on
    fresh coin blocks, and canonical normalization and fallback?
  - Are the auxiliary-input bounds `Lz` and `Lz'` right?
  - Do the hybrids `H_i` (first `i` phases real) have the endpoints `H_Q` = real and `H_0` = `S_Q`?
  - Is the non-uniform phase reduction sound: advice of polynomial length, no witness, no trust in simulated
    metadata?
  - Is the total `Q(n) · ε(n)` negligible?
- **`StatZK.seqRep`:** is the error exactly `Q(|x|) · δ(|x|)`, by the triangle inequality over the `Q(|x|)` hybrids?
- **The proof-system cases:**
  - completeness from `seqRep_exec_phase`;
  - soundness from phase 0 (`InteractiveProof`), and `s^Q` by conditioning on the prefix and induction, with the
    prover that hard-wires the prefix (`InteractiveProofErr`);
  - the efficiency of `V_Q` and `P_Q` from the iterate hosts and `coinBlock` slices.
- **The brief's edge cases:** `k = 0` rounds; `Q(n) = 0` for the ZK statements (empty history; the proof-system
  statements assume `1 ≤ Q(n)`); odd `k`; `verifierFirst` true and false; a cheating verifier's filler replies;
  malformed or non-canonical simulator outputs; the honest prover's `[]` fillers.
- Do the sketches describe the delivered proof? Only `StatZK.seqRep`'s was rewritten; the other four are the
  statement-phase sketches.

**2. Frozen-statement integrity: 196 / 0 / 0**
- Are the five targets' headers, the 27 + 35 pre-existing declarations and their statement prose byte-identical
  (`landing/frozen-check.txt`, `pack-checks/headers.txt`)? Is decls2 **196 ADDED / 0 CHANGED / 0 REMOVED** from both
  bases?

**3. `StatZK_iff` (S-01)**
- `ZeroKnowledge/Defs.lean` gains exactly `StatZK_iff` (`:191`), +11/−0, lines inserted only (`pack-checks/shared.txt`).
  The other 35 declarations are unchanged.
- Is it exactly `StatZK`'s body by `Iff.rfl`, with a formula docstring and no attribute? The Rule-10 controls show the
  sealed `Iff.rfl` form of `StatZK` failing and `StatZK_iff` passing: the reader is needed and sufficient.

**4. The multi-agent provenance**
- `evidence/logs/ownership-check.txt`: the REPORT's table gives each of the 39 helpers exactly one owner: the lead 5,
  `seq-zk-a` 10, `seq-zk-b` 9, `seq-zk-c` 15. `SequentialZK.lean` and `Defs` are the lead's. The worker's
  `evidence/subagents/seq-zk-{a,b,c}` exist in the delivery on the exchange (`a6be22fa`, `inbox/fills/seq-zk/`; 221, 173
  and 222 files).
- `evidence/logs/final-sweep-attribution.txt`: all 276 final-sweep checks match a slot acquisition of the same module
  with the lead's tag. `evidence/logs/slots-check.txt`: never above 3 slots.
- The table is consistent with the delivered file set; it is not independently verifiable beyond the records. Is the
  provenance adequate?

**5. Rule 10: only the pre-existing `Defs` failures?**
- The seals cover the 41 files over the full closure, at the head and the base files at the base, in four variants,
  run with `-DmaxErrors=0`, with install and EOF records in every row (`pack-checks/rule10.txt`; 154 head probes, 10
  coe probes byte-identical to strict not re-run).
- **The only failing probe is `ZeroKnowledge/Defs`:** 10 errors in A and in B, strict and coe, at the head **and at
  the base**. They are the same 6 declarations, whose headers and docstrings are unchanged:
  - `perfectZK_zeroRounds` (:294);
  - `AbortRetry.attempt_poly` (:395), `AbortRetry.exists_retrySimulator` (:444) and `AbortRetry.statClose_retry` (:516);
  - `PerfectZKAbort.statZK` (:604);
  - `negligible_inv_pow_sqrt_div` (:682).

  `SequentialZK` and every helper give 0. **New failing declarations: 0**; `StatZK_iff` passes.
- **The controls** (`evidence/logs/ctlcheck.log` ALL_OK). Coe has 10 probes and 9 sealed negatives; strict has 14 and
  15, and `ctlCoeReader` fails in the 6 strict sealed probes (the harness effect). Rows: `PolyExpr.eval`, the
  `FinDist` CoeFun instance, `ZK`/`ZK_iff`, `StatZK`/`StatZK_iff` and `Composability.prefixProver`/`prefixProver_coins`.
- **The explicit-unfold scan:** 1245 items. The 13 "foreign" are local `let F`/`let g` bindings resolved by name to
  globals (`evidence/logs/scan-foreign-attribution.txt`): 0 real foreign definitions.
- Does any proof read a foreign definition other than through a published reader (`Interaction`'s `exec`, `viewV`,
  `withV`, `encodeMsgs`; `InteractiveProofs`; `Defs`; the `NUPPT` layer; one helper's definitions read from another)?

**6. Duplication (recent gates graded undisclosed re-proofs of public lemmas as majors)**
- Does any new declaration, or any part of a proof, duplicate a public TCSlib or Mathlib lemma, or copy a private
  one, beyond the worker's overlap disclosures (`worker-report.md`; the checkpoint REPORTs in `worker/`)? **Anything
  undisclosed is a major.** The review's spot checks (`evidence/logs/duplication-review.txt`) found nothing undisclosed.
- Search in particular:
  - the hybrid argument (`exists_hybrid_gap`, the multicopy lemmas, sc-compose's `abs_chain_le`) against the
    statistical and computational hybrids;
  - prefix and suffix laws against `Games/*`;
  - `StatClose`/`distAdv_le_of_statClose` uses;
  - coin blocks (`coinBlock`, `FunFamily.blocks`);
  - the history encoding: the PR uses the public `CommitmentLemmas.encodeMsgs_append` and `length_encodeMsgs_le`
    directly (`pack-checks/dupscan.txt` B);
  - `getD` readings (two `List.getD_eq_getElem?_getD` rewrites, no DL-47-class copy).
- Mechanical aids (`pack-checks/dupscan.txt`): a statement scan (binders and type, whitespace-normalised) of the 175
  new theorems has **0 hits**, both against the files the tip, #324 and #326 changed and against all 20686 theorems
  of the other 1278 TCSlib files. No new name is declared in a file another comparator changed
  (`pack-checks/namecheck.txt`).

**7. The docstrings: S-02 and the strict-PPT note**
- **LE-doc (ruling 5):** `e9b5ea47..bd19c433` changes 23 files, +222/−61. Every file is identical with doc comments
  deleted, 81 docstrings change, docstring counts are unchanged, and the max width is 100 (`pack-checks/lecheck.txt`;
  `landing-ledoc/`: `landing/seq-zk-le-doc.diff`, `seq-zk-le-doc-plan.tsv`, `checks/seq-zk-doconly.txt`).
  - Does each of the 81 formulas state what its declaration says, in Lean argument order?
  - The post-edit docaudit (`statements/seq-zk-post/docaudit.tsv` there) gives 190 OK and 2 LABEL. It has 1 NO-DOC,
    `prefixProver`, whose docstring precedes `@[simps]` (a tool artifact). Its 9 NO-FORMULA are the 5 frozen targets,
    the 2 already stated, and 2 Prop formulas without a relation symbol.
- **The 11 cut formulas.** Each ends in " …`", where the conclusion passed 240 characters. They are in
  `SQ/ComputationalHybrid` (125, 175), `SQ/ComputationalReduction` (62, 189, 253), `SQ/ContinuationProbability` (89,
  103, 171, 321, 337) and `SQ/EndpointSampling` (216), for:
  - `prefix_distAdv_joint_le`, `distAdv_view_endpoints`;
  - `reductionData_fields`, `exists_continuationSampler`, `exists_phaseReduction`;
  - `continuationProb`, `continuationProb_eq`, `continuationProb_real`, `phaseGap`, `phaseGap_eq`;
  - `simulate_eq_simPrefix`.

  Gate 37 round 1 graded this rule's label-and-prefix readers as incomplete (G37-03, minor). For #324 the maintainer
  completed all 20 in LE-gate37. Grade these by the same standard: a truncation is acceptable only where the
  docstring's own prose states the property.
- **The strict-PPT versus expected-PPT note.** The module docstring's *Deviations* states:
  - zero-knowledge is taken with **strict-PPT** simulators and bounded abort retries (G02-#4, D8);
  - `PerfectZKAbort`'s premise is [Gol01, Definition 4.3.1]'s strict-PPT aborting formulation;
  - [PS10]'s expected-polynomial-time wording "is a separate source convention".

  `PerfectZKAbort.seqRep`'s docstring repeats this as a *Source distinction*. Is the note accurate against [PS10,
  Theorem 175.1] and [Gol01, §4.3.4], and is it placed where a reader of the targets will see it?
- Does every proof of 15 lines or more carry a `**Proof sketch.**` (`evidence/statements/sketchaudit.txt`: 48 such
  proofs, all sketched)? A misstated formula or sketch is a minor.
- Does every new public `def` land with its `_eq` reader (lint check 8)? There is no `@[simp]` (only
  `@[simps (config := {isSimp := false})]`). The one instance is the Prop-valued `PhaseMetadata.instNonempty` (S-03).

**8. Simulator uniformity**
- Is `S_Q` uniform as constructed (`SQ.Uniform` by `NUPPT.ofPolyTimeUniform`, `SQ/SimulatorMachine.lean:310–344`), with
  its advice-free coins `CV + Q · S.coins`, and is the bad-prefix advice confined to the computational reduction, never
  to `S_Q` (ruling 6)?

**9. The merge interaction**
- `git merge-tree --write-tree bd19c433 <x>` is clean, and no path is shared (`pack-checks/mergetrees.txt`):

  | `<x>` | head | merged tree | downstream of both (`pack-checks/downstream.txt`) |
  |---|---|---|---|
  | the tip | `c2f6adeb` | `217fd194` | 41 (#323's `DAGCircuit` is in the unit closure) |
  | #324 (sc-compose) | `4bd2d80b` | `ae43ea76` | root `TCSlib` |
  | #326 (derand) | `c27005d6` | `029cdc65` | 52 (`ClassP/DTIME`, `Build/IterateFind` are in the unit closure) |
  | #318 (merged) | `b0bad23a` | `8ddcf527` | root `TCSlib` |
  | #319 (merged) | `47daa907` | `47f23ea6` | 2: root `TCSlib`, `audits/pass-shelat/Checks` |
  | #323 (merged) | `8c3f3e3f` | `295f67b2` | 41 |

  None of the 202 new short names is declared in a file another comparator changed.
- **The integration evidence** (`integration/`, `4f8cb374…`): the combined build of the records tip of that time
  `b0ebd475` plus all six PRs, with #327 at this head, as tree `3fb05ea0`. **694/694 rc 0**, 0 errors in both forms.
  - Re-checked (`pack-checks/integration.txt`): merging #324, #326 and #327 onto the current tip, in all six orders,
    gives `TCSlib` and `audits` trees equal to the built tree, and all 694 built sources equal their blobs there.
  - Its solo check of tip + #327 (on `b0ebd475`) rebuilt the 63 modules downstream of the 23 LE-doc files and #313's
    Learning files: 63/63 rc 0, 0 errors, 0 sorry, every module byte-identical to a reference.
  - **LE-doc's build is the combined build:** the review build ran at `e9b5ea47`, and 280 of its 303 built sources
    equal the head's; the 23 that differ are LE-doc's files (`pack-checks/srcequality.txt`).
- **Pending merge condition (not an audit item):** the merge order, **#324 last**. The intermediate states with the
  current tip are not built as such; any rebuild for whichever of #326 and #327 merges second is the maintainer's, if
  required.

## Known dispositions (not findings)

- **S-01** (minor, confirmed), **S-02** (fixed by LE-doc, with question 7's cut formulas open), **S-03** (info): the
  disclosed unused `hQ` warning (`SequentialZK` 1 warning); the Prop-valued instance `PhaseMetadata.instNonempty`;
  tool artifacts.
- **Admissions:** 23 → 18; only `SequentialZK` (5 → 0) differs; outside the order only `SeedMajority` (#312) and
  `SpecialEncryptionMulti` (#311), base delta (`evidence/logs/sorry-census.txt`).
- **The build:** 303/303 rc 0, 0 errors in both forms, 1670 s, through root `TCSlib` and both `audits/*/Checks`
  (`landing/root-checks.jsonl`). Whole-tree check: 1288 modules, OK. The olean tree was restored to `457ba704…`.
- **Axioms:** the five targets, `PerfectZK.seqRep`, `PerfectZKAbort.seqRep`, `Composability.colSeq_efficientProverProof_zk`,
  `negligible_colSeqSound`, `StatZK_iff` and `zk_of_padded_spec` print `[propext, Classical.choice, Quot.sound]`
  (`landing/census-head.log`). The census has 414 stored constants (= the worker's), the axiom union is standard, and
  there is no `sorryAx`. Against the base: 107 → 414, removed 0, type-changed 0, axioms-changed 7.
- **Lint:** 92/101 at the head and the tip; the only changed line is `Defs`' check-8 list losing `StatZK`
  (`StatZK_iff`). Complexity 25/391, identical.
- **The LE-doc PROVENANCE says +219/−61;** git and its own `landing/seq-zk-le-doc.stat` give **+222/−61**.
- **The PR description** predates LE-doc: it names the head `e9b5ea47` and announces "88 declarations"
  (`pr-description.md`, fetched on 2026-11-16). The maintainer updates it before #327 is marked ready.
- **The review's "target sketches rewritten"** is true of `StatZK.seqRep` only (question 1).

## Evidence

- **`review.md`:** the maintainer's delivery review, verdict ACCEPT (S-01–S-03).
- **`verification.zip`:** every file the review cites and the pack uses, as byte-identical originals. `SHA256SUMS` lists
  every other entry, and `PROVENANCE.txt` gives each source.
  - `review-evidence.zip` (`fills/seq-zk/final-r1/`, SHA-256 `f9c39479…`) and `review-evidence-SHA256SUMS`, its
    manifest: 1107 entries, exactly the 1106 manifest paths plus `SHA256SUMS`; every hash verifies;
  - `landing/PROVENANCE.txt`: the review's PROVENANCE (= the ZIP's);
  - `records/`: the issue package `fills/seq-zk/issued-r1/` and, at records
    `9760e69425babb1bc9ee8b085e227ae3faf6dac5` (local, unpushed: the tip `c2f6adeb` plus the Gate 37 round-2 and Gate 38 records), the duplication ledger, the decision log, the deferred-work register,
    the Codex host addendum and dispatch, and the uniformity audit's findings;
  - `evidence/`: byte copies of the review-evidence entries the pack cites;
  - `worker/`: byte copies from the exchange delivery `a6be22fa` (`inbox/fills/seq-zk/`): `COMMITS.tsv`, the
    scope request (`StatZK-iff.patch`, `request-and-answer.md`) and the five checkpoint REPORTs. The first three are
    each equal to the review's `logs/delivery-extracts/` copy;
  - `pack-checks/`: the re-checks for this pack, from git objects only (no Lean), with their scripts.
- **The worker's own evidence:** on the exchange at `a6be22fa`, under `inbox/fills/seq-zk/` (manifests 3073/3073 and
  3023/3023 in the review; 1.12 GB, verified there without extraction).
- **`landing/`:** byte copies of evidence-ZIP entries: `root-checks.jsonl` (= `build/results.jsonl`),
  `build-summary.txt` (= `logs/build-summary.txt`), `census-head.log` (= `probe-runs/mods/PlProbe_CensusHead.log`),
  `frozen-check.txt` (= `statements/frozen-check.txt`) and `tree-check-head.txt`.
- **`landing-ledoc/`:** LE-doc for derand (F-04) and seq-zk (S-02): `ledoc-derand-seqzk-evidence.zip` (`977bbe89…`),
  its manifest and PROVENANCE.
- **`integration/`:** the combined build of all open PRs (`4f8cb374…`), its manifest and PROVENANCE.
- **`worker-report.md`:** the worker's final `REPORT.md`, at exchange `a6be22fa`.
- **`pr-description.md`:** the PR #327 description as fetched from the GitHub REST API on 2026-11-16 (`.body`, raw).
- **`pr.diff.txt`:** `git diff` from the base to the head (41 paths, 6652 insertions, 14 deletions).
- **`source-head.json`:** the head hashes, line counts and over-width counts of the 41 changed files.
- **`sources.zip`:** the source closure at the head of every changed module, 185 files.
- **The bundle** adds, at the head, `Composability/SequentialZK.lean`, `ZeroKnowledge/Defs.lean` and
  `SQ/SimulatorMachine.lean`.

## Findings delivery

Return `gate39-seq-zk-findings.md` as a Markdown file in this chat. If you have several evidence files, return a ZIP.
The user dispatches and merges.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

**Severities**
- **blocker:** a false or unusable statement, a proof that does not establish the frozen statement, or a scope
  violation.
- **major:** a changed frozen statement, a forbidden read in a touched declaration not covered by the rulings (the 10
  pre-existing `Defs` failures are not new), an undisclosed copied private lemma or undisclosed re-proof of a public
  one, or necessary evidence that cannot be verified.
- **minor:** documentation or API defects, including an inaccurate formula docstring or proof sketch.
- **note:** anything else.

Report the audited head and the counts by severity. The gate closes at zero blockers and zero majors.

## ===== briefs/pass-shelat-ch5-8/gates/39-seq-zk/review.md =====

# seq-zk · maintainer delivery review (r1)

**Verdict: ACCEPT** (all five targets proved). S-01 is confirmed and S-02 is pending as LE-doc. Draft [PR #327](https://github.com/Shilun-Allan-Li/tcslib/pull/327).

## Delivery and landing
- **Delivery:** Codex on Seyoon's Mac, a lead and 3 sub-agents. The final is exchange `a6be22fa`; the checkpoints are `d316d29a`, `36f1896d` and `65bc1c08`. The issue base is `107f1e8c`.
- **Landing:** `land/pass-shelat-seq-zk`, on `05d26fe5`.
  - **Head:** `e9b5ea47a1c3dcd664caf2dbf308f89c1beffbb8`, tree `a6acdfbf`.
  - **Commits:** `1ed5765c`, `29b81e8b`, `9747e27a`, `a1a5c447`, `5fa0430c` and `e9b5ea47`.
- **Files:** 41 files, +6491/−14:
  - `Composability/SequentialZK.lean`;
  - 39 new helpers under `SequentialZK/`;
  - `ZeroKnowledge/Defs.lean`, +9 lines (`StatZK_iff`).
- **Evidence:** `review-evidence.zip`, SHA-256 `f9c394794fd7637237a274163a396eaa78452250c5e31abc5d2878b9e353392f`, with 1107 entries.

## Checks
- **Sub-agents:**
  - `evidence/subagents/seq-zk-{a,b,c}` exist.
  - `REPORT.md` assigns each of the 39 helpers to exactly one agent: the lead 5, a 10, b 9 and c 15.
  - `SequentialZK.lean` and `Defs` are the lead's.
  - The lead ran the final sweep: all 276 checks match lead-tagged slot acquisitions.
  - Never more than 3 slots were held at once.
- **Integrity:** the manifests verify 3073/3073 and 3023/3023. `git am` reproduces the 6 hashes unsigned. The package verifies 7/7 and its sources 237/237.
- **Build:** 303 modules give rc 0 and 0 errors, through root `TCSlib` and both `Checks`, in 1670 s. The whole-tree check covers 1288 modules: OK.
- **Statements:** the header, prose and definition-body checks show 0 differences, and the control reports 1. decls2 gives 196 ADDED and 0 CHANGED. The largest file has 990 lines and the widest line is 99 characters. There is no `@[simp]`.
- **Axioms:** the five targets, `PerfectZK.seqRep`, `PerfectZKAbort.seqRep` and the `ThreeColoring` consumers use only the standard three. 414 constants; no `sorryAx`.
- **Rule 10:** 154 runs. Only `Defs` fails: 10 errors in the same 6 declarations that already fail at the base. `StatZK_iff` is clean. The coe controls are ALL_OK. The scan finds 0 foreign definitions.
- **Admissions:** 23 → 18.
- **Lint:** 92/101 and 25/391.
- **Content:** each target is a thin instantiation of the helper theorems. The sketches describe the delivered route.

## Findings

| # | Severity | Finding | Disposition |
|---|---|---|---|
| S-01 | minor | The frozen `ZeroKnowledge/Defs.lean` gains `StatZK_iff` (`Iff.rfl`). It equals the approved patch, apart from the position of one blank line. The approval had been recorded only in the delivery. | **Confirmed by Seyoon (2026-11-16).** Accepted. |
| S-02 | minor | 88 new public declarations' docstrings give no formula. | LE-doc, pending, before the gate. |
| S-03 | info | A disclosed unused `hQ` warning; the Prop-valued instance `PhaseMetadata.instNonempty`; and some tool artifacts. | None. |

## ===== briefs/pass-shelat-ch5-8/gates/39-seq-zk/worker-report.md =====

# seq-zk final delivery

All five frozen `seqRep` theorems of PS10 Theorem175.1 are proved. This final report's
outcome, revision, inventory and verification sections supersede the historical checkpoint
statuses preserved in the evidence and appendices. No target statement was weakened.

Issue base: `107f1e8c218733eac12d6b9bee6fece441271317`.
Issued exchange pack: `7d85785c2e98f0bfdec081a875a9343f06043a8a`.
Final local proof revision: `d842dc8f681f6b89499129f5b64a50d0e4587935`.
Lean4.25.0; pinned Mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.
The `fill/seq-zk` proof branch remains local. The six unsigned proof commits, in order, are
listed with full identities/dates/signing information in `patches/COMMITS.tsv`:
`a758032d636fd410b0c4b8a1530a96d000cc467a`,
`e978a28274fdeb545e622ae28747221088352512`,
`04c253e48d9c0ebb73943f39412365cd4d8e02db`,
`5a80d36a5a4da1c2906b747dab59251fdd03836a`,
`7cecd426dddac78789c9e7fc627a7cd013d67792`,
`d842dc8f681f6b89499129f5b64a50d0e4587935`.

## Targets and resulting behavior

| Frozen declaration | Final result |
|---|---|
| `ZK.seqRep` | Proved; one uniform strict-PPT simulator, polynomial times negligible advantage |
| `StatZK.seqRep` | Proved; exact statistical error `Q(n)*δ(n)` |
| `InteractiveProof.seqRep` | Proved; perfect completeness and negligible soundness |
| `InteractiveProofErr.seqRep` | Proved; exact soundness error `s(n)^Q(n)` |
| `EfficientProverProofErr.seqRep` | Proved; efficient prover and exact soundness error `s(n)^Q(n)` |

All five statement headers are byte-for-byte identical to the issue base. The new proofs
handle either first mover, odd or zero rounds and zero phases where the frozen hypotheses
allow them. The generic explicit-error engine also covers zero phases with error1; the
original `hQ` hypothesis is retained in `InteractiveProofErr.seqRep`, with a benign native
unused-variable warning disclosed here.

The simulator validates raw phase views and normalizes them to exactly the real prover-slot
count, each message bounded by the original prover-message polynomial. Malformed views use
a canonical fallback. Empty honest-prover fillers pad phases; arbitrary cheating-verifier
filler replies remain unrestricted. Normalization fixes real phase views. One global verifier
tape and independent phase-simulator tapes yield the same uniform strict-PPT simulator before
any auxiliary-input bound or distinguisher is supplied.

For statistical ZK, randomized postprocessing, averaging and the conditional-prefix recursion
sum exactly `Q*δ`. For computational ZK, a finite polynomial metadata domain selects a common
negligible phase bound uniformly over arbitrary witnesses. Neither advice nor simulator stores
or tests the witness. The conditional real-prefix/simulated-suffix hybrid sums `Q*|ε|`; the
published polynomial-times-negligible lemma completes the result. Exact split/block and
endpoint readers identify actual real and simulator views without further error. No efficient
honest-prover or simulated-output-shape premise was introduced.

## Ownership, changed files and sketch edits

Only the lead edited SequentialZK.lean, applied the approved frozen reader, committed the local
proof branch, ran the merged final checks and prepared/pushed delivery. Helpers were split by
module; no two agents edited one helper. Each agent had a separate managed worktree and olean
tree, with packages linked read-only to the lead's pinned packages.

| Worker | Included source and proofs |
|---|---|
| Lead `/root`, `seq-zk` | All five target bodies; main specification/phase bridges; PrefixFolds, PrefixLaws, ProofTransfers, StatisticalTransfer, ComputationalTransfer; approved StatZK_iff |
| `/root/zk_route`, `seq-zk-a` | Normalization, NormalizationMachine, PhaseView, Statistical, ExecutionBounds, NormalizedStep, StatisticalRecursion, StatisticalPrefix, BoundedMetadata, RealPrefixBounds |
| `/root/efficiency`, `seq-zk-b` | Efficiency, WrappedVerifier, SimulatorMachine, RealPhases, PaddedProverSpec, SuffixMachine, ComputationalReduction, ReductionAdvantage, ComputationalPhaseBound |
| `/root/soundness`, `seq-zk-c` | Soundness, Phases, Congruence, VerifierPrefix, ErrSoundness, RepeatedVerifier, RepeatedSoundness, Advice, StatisticalPostprocess, EndpointSampling, HybridRecursion, SuffixLaws, ComputationalAdvice, ContinuationProbability, ComputationalHybrid |

There are41source files: main,39helpers and the approved Defs reader. They total7731lines;
main is990lines; every file is≤1000lines and every line≤100characters (maximum99).
`evidence/final-source-inventory.json` records every path/size/width/SHA.
`evidence/final-stored-constants.tsv` lists all414stored constants, including generated/private
ones. The complete declarations and their public equations/formulas are delivered in `src/`.
The table below is the exact file inventory. New helpers are imported precisely and listed
in the main Contents. The module title/status and all five target sketches describe the
implemented proof. New public definitions/abbreviations have readers; proofs of at least15
lines have English sketches, and long proofs have stage comments. Seven initially missing
stage-comment blocks were fixed in commit4; the later HybridRecursion block was fixed before
commit5. No new global simp attribute was added.

## New declarations

The exact202source-written new declarations are listed, with paths and lines, in
`evidence/subagents/seq-zk-b/final-review-15/new-source-declarations.tsv`.
The414stored-constant inventory additionally includes generated/private constants and retained
original declarations. The new public interfaces comprise bounded phase normalization and
readers, padded prover/verifier contracts and phase/endpoint laws, uniform simulator and
continuation machines, exact adaptive soundness, statistical postprocessing/recursion,
finite metadata/advice selection, computational phase reduction/advantage, conditional hybrid
bounds and the two ZK transfer theorems. Each full statement/docstring is in its source;
no extra axiom, admitted helper or replacement target premise was introduced.

## Verification

* Both issued packs passed native `shasum -a256 -c`; all237base source hashes matched.
  Mac preflight, toolchain/package pins, narrow-root import probe and baseline237-module
  bootstrap passed. The issued76roots were used; only Mathlib.Data.Fintype.Lattice and
  Mathlib.Data.Real.Archimedean were later added as precise direct prerequisites. Lead-only
  cache gets used the issued slot wrapper with `-k3`; no `lake build` or unfiltered cache get.
* Final owned-module recheck passed. The full276-module sweep (original237in exactly their
  supplied relative order, plus39helpers before consumers) passed with zero errors and all
  exits0. The admitted-declaration census changed exactly23→18: only the five targets above
  disappeared. All18inherited admissions are unchanged. See `logs/sweep-final-01/` and
  `logs/final-sorry-census.json` under evidence.
* Final native collector at revision d842 printed all414stored constants, all five targets,
  PerfectZK.seqRep, PerfectZKAbort.seqRep and the ThreeColoring consumers. Every axiom set is
  a subset of `{propext, Classical.choice, Quot.sound}`; no new `sorryAx`. See
  `logs/final-repair-axioms/`, `logs/final-repair-axiom-summary.json` and the TSV inventory.
* The six-commit format-patch series replayed in a clean scratch clone from the exact issue
  base. The resulting full Git tree and all41delivered source bytes matched revision d842.
  Raw commands/results: `logs/final-repair-replay.log`. Signing is explicitly recorded.
* Style lint at base and final:92FAIL/101WARN. Line-set comparison found no new FAIL. The
  sole changed WARN line improves Defs' missing-reader list from3definitions to2, removing
  StatZK. `logs/final-static-audit.json` records frozen headers, size, width and exact line sets.

### Rule10 whole-file seals and controls

All164final cells are accounted for:41owners × strict/coe × eval-excluded A/eval-included B.
The canonical coe/A variant treats projection coercions and PolyExpr.eval as notation.
Both strict and eval-included stress variants also pass every new/changed proof. Each native
probe covers the full transitive TCSlib import closure, not a handpicked subset; exact native
identity, install masks and EOF masks are verified for every request. Diagnostics count
both `error:` and `error(…)` forms. Advice has a legitimately empty TCSlib closure and zero
requests; its native zero-batch install/EOF records are checked explicitly.

160cells have zero errors. The four Defs cells each retain the same10errors in the same six
inherited declarations as the four issue-base Defs cells. The new StatZK_iff reader is clean.
The main's four issue-base cells are clean. The following inherited failures occur identically
in coe/A, coe/B, strict/A and strict/B; none is a new fill failure:

| Defs declaration | Errors per variant at base and final |
|---|---:|
| perfectZK_zeroRounds | 2 |
| AbortRetry.attempt_poly | 1 |
| AbortRetry.exists_retrySimulator | 2 |
| AbortRetry.statClose_retry | 1 |
| PerfectZKAbort.statZK | 3 |
| negligible_inv_pow_sqrt_div | 1 |

The effective final164cells consist of20exact checkpoint1reuses,120unchanged revision5native
cells and24revision6native reruns for the six owners whose import closures meet the repaired
helpers. `rule10/final-repair/selected-matrix.{json,tsv}` links every final record to its
selected native request record, raw log and guard result. The source and every TCSlib import
closure file are byte-identical between each selected native revision and final d842; pins
and exact request rows also match. Full hashes are in final-source-closure-provenance.json.
Earlier superseded failures remain delivered, with source revision and attribution, rather
than being counted as final results.

Whole-file seals found two real implicit-reader violations in revision5: acceptProb_prod in
ContinuationProbability (one error per variant), and distAdv_phaseReduction in
ReductionAdvantage (two errors per variant). Commit6 replaces those implicit reductions with
published acceptProb and Equiv/split-tape readers. Their statements are unchanged. All24cells
in affected owner/import closures were rerun at d842 and pass. Strict/coe and eval A/B introduce
no final new failing declaration or difference beyond the six inherited Defs declarations.

The ten retained native paired controls comprise five clean unsealed probes and five sealed
negative probes, each failing exactly once at the designated negative declaration while its
public-reader positive succeeds. Their complete definition-home import closures and pins are
unchanged at d842, and each sealed identity is present in final requests; reuse is certified
in `rule10/final-repair/control-reuse-provenance.json`. Raw logs, sources, request rows and
native masks are under checkpoint2 controls. padFin and inArg are exercised in A/B; eval is
exercised in B and explicitly excluded in A. Archived CostBoundedBy/hash-sign-only targets
absent from this closure are marked absent, not claimed exercised.

The final explicit-unfold scan covers all41sources. The primary native kind probe classifies
1245items:868theorem references,6owned definitions and371initially unresolved items, with
zero foreign definition items. A complete supplemental source-local review and24-target native
kind/home/projection/type-is-Prop probe resolve the remaining names, including proof-valued
specification fields, exported class-field readers and inherited own AbortRetry definitions.
`rule10/final-repair/explicit/` and `subagents/seq-zk-a/final-review-12/` preserve both initial
and supplemental classifications and sources. The merged result is897public readers,8inherited same-file definition items and340local/inline
proof items, with zero unexplained uses. No unresolved foreign-definition use is waived.

## Scope requests

One frozen-file change was requested and approved: nine lines adding `StatZK_iff` beside the
existing predicate in `TCSlib/Cryptography/ZeroKnowledge/Defs.lean`. It is an `Iff.rfl` reader
analogous to ZK_iff and changes no definition or prior theorem statement. Exact diff and
verbatim request/answer are in `evidence/scope-request/`.

Request (verbatim):

May I add the nine-line `StatZK_iff` reader in frozen `TCSlib/Cryptography/ZeroKnowledge/Defs.lean`? The exact proposed diff is at /Users/seyoonr/.codex/worktrees/seq-zk-a/tcslib-exchange/evidence/subagents/seq-zk-a/scope-StatZK-iff.patch. It exposes the existing simulator property using `Iff.rfl`, analogous to `ZK_iff`, without changing any definition or theorem statement. The issued seq-zk brief’s “Frozen files / Scope requests” rule requires Seyoon’s approval for this edit; Rule 10 prevents adding this reader in a helper. I’ll continue the independent interactive-proof work while this is pending.

Seyoon's answer (verbatim): Approve this reader addition

There were no further frozen-file edits. Frozen Games/Efficiency and all parent facades remain
unchanged. Suggested promotions below are requests for maintainer consideration; they were
implemented only within the authorized helper directory.

## Overlap and reuse

Raw lead searches and every agent's search logs are delivered. The detailed per-declaration
records in the appendices below preserve exact nearest-relative paths/lines, reuse/generalization
relationships and promotion requests, including historical alternatives and corrected attempts.
Their historical status sentences refer only to their stated checkpoint/source cutoff; the
final revision and verification above are authoritative. No foreign private lemma was copied.
The full final ComputationalTransfer addition is described here before those appendices:

* `zk_of_padded_spec` directly reuses the published ZK_iff, phaseVerifier_efficient,
  exists_phaseSimulator, exists_negligible_phase_bound, realPrefix_bounds,
  prefix_distAdv_joint_le, distAdv_view_endpoints and Negligible.polyExpr_mul. Nearest owned
  relative is `Composability/SequentialZK/StatisticalTransfer.lean:49`
  (`statZK_of_padded_spec`), whose statistical-distance contract
  cannot establish computational indistinguishability. The new assembly uses the common
  nonuniform metadata bound and computational hybrid; it copies neither selector, machine,
  prefix induction nor probability host. Nearest existing specialized hybrids are
  `ZeroKnowledge/ThreeColoring/SimulatorLemmas.lean:549` (`exists_hybRed_ge`) and GI ZK hybrids; these have protocol-specific
  view/reduction contracts. `ZeroKnowledge/Defs.lean:602` (`PerfectZKAbort.statZK`) uses abort/retry amplification, which
  does not give this conditional-prefix composition theorem. All are searched/disclosed;
  shared public components are reused directly.
  Polynomial closure directly reuses `Asymptotic/ReductionSupport.lean:267`
  (`Negligible.polyExpr_mul`); no new negligible-times-polynomial proof is added.
* `ZK.seqRep` instantiates that generic theorem with the already published owned
  seqRep_proverSpec. The final proof adds no duplicate semantic or computational host.
* Existing NUPPT.loopState' and Fin.foldl supply the strict-PPT simulator and semantic phase
  recursion. No new repetition host was introduced. The indexed phase tables use canonical
  FunFamily block equivalences and public readers; repeated specializations are disclosed
  in each helper record rather than silently copied.

Promotion/reader requests: normalize/encode glue and uniform phase machinery belong with
future shared games support; the generic acceptance/postprocessing, conditional-family hybrid,
reindexing, finite-selector and length-indexed negligible-bound results belong in shared
probability/advice/reduction modules; padded proof-system contracts belong near InteractiveProofs.
The exact statements and nearest relatives are in the appended agent records. The only reader
needed in an existing defining file was the approved StatZK_iff. No other promotion or reader
request is needed to make this payload compile or satisfy Rule10.

## Host resources, exceptions and evidence completeness

The issued wrapper/default three-slot pool governed every Lean/lake/check command, including
all agent commands. Root tag seq-zk; agent tags seq-zk-a/b/c. Lead-only narrowed cache fetches
reserved3slots. No process belonging to another job was touched. Mac preflight/headroom,
package pins, narrowed roots, seeds and coordination records are delivered. Each olean tree
had one writer; packages were linked, never copied. Final independent seal streams used
separate APFS-cloned completed TCSlib trees under the same shared cap3. A one-second slot-free
gap replaced the earlier six-second gap after derand/sc-garble reported their Lean/cache work
complete. This is disclosed lead implementation judgment under Seyoon's best-judgment/resource
coordination authorization; it changes no proof budget, request, guard, module granularity or
resource cap. The final sweep itself is serial.

Ten pathological own Lean children were gracefully interrupted during development: eight by
a, one c ErrSoundness attempt and one root StatisticalTransfer attempt. Each had concrete
source/process/resource evidence and individual lead authorization under Seyoon's best-judgment
instruction; exact PID/parent/command was reverified before signaling the own child only. Raw
logs, stack/process samples, wrapper flush/release records and corrected clean reruns remain
included. These were not fixed timeouts or E-RES events. The a failure ultimately came from a
missing Defs import leaving NUPPT.simulate invalid in a signature; root/c source review missed
that cause. Root's StatisticalTransfer failure came from a positional argument to implicit V;
root and read-only review missed it until the named argument/typed application exposed it.
Earlier incorrect diagnostic hypotheses are retained and explicitly corrected.

Other preparation/instrumentation corrections are fully retained: missing baseline artifacts
were seeded with source/hash provenance; premature invalid dependency probes are labeled;
one source integration hash mismatch correctly rejected changed author comments; a dispatcher
missing-order-file attempt started no Lean; one JavaScript orchestration parse failure started
no subprocess. An overly strict final-order preparation assertion was corrected while preserving
original237relative order, using previously bootstrapped unchanged late dependencies with
verified source hashes/nonempty artifacts. The final static audit's initial broad simp regex
matched proof text, then was corrected to attribute declarations; no source or Lean change.

The zero-request Advice native seal passed. Its postprocessor initially rejected an empty name
set; the validator was corrected to require the explicit unique zero batch, two zero mask
records and matching install/EOF counts. All nonempty checks and native instrumentation remain
unchanged. Original tool version, trace and valid native log remain delivered. The stopped
dispatcher resumed only remaining cells; no Lean child was interrupted by this harness correction.
Progress-only aggregate attempts while checks were still running are labeled progress; the
final aggregate requires and certifies all164cells. No automatic approval review rejected an
action, no push was refused at the prior checkpoints, and no mathematical/scope exception beyond
the approved reader is claimed.

All evidence is under `evidence/`, including all raw success/failure logs, attempts, probe sources,
request manifests/rows, guards, scripts/tool versions, agent records and immutable receipts.
Append-only receipts resolve exact historical bytes to current files or preserved archives;
no old receipt is silently replaced. Large diagnostic samples are delivered losslessly as
numbered ZIP parts with entry lists, original lengths/hashes and verified extraction; no file
is omitted for size. `evidence/SHA256SUMS` covers exactly evidence files except itself; top-level
`SHA256SUMS` covers exactly every payload file except itself. Both path sets and every digest
are checked before delivery. Checkpoint1,2and3were delivered from the lead's separate delivery
worktree, only under inbox/fills/seq-zk; final delivery follows the same rule, unsigned commit,
pull-with-rebase and ordinary push. No proof branch push or PR/merge is performed.

## Exact final source inventory

| Source | Lines | Max width |
|---|---:|---:|
| `TCSlib/Cryptography/Composability/SequentialZK.lean` | 990 | 98 |
| `TCSlib/Cryptography/Composability/SequentialZK/Advice.lean` | 67 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/BoundedMetadata.lean` | 135 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/ComputationalAdvice.lean` | 74 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/ComputationalHybrid.lean` | 197 | 97 |
| `TCSlib/Cryptography/Composability/SequentialZK/ComputationalPhaseBound.lean` | 184 | 95 |
| `TCSlib/Cryptography/Composability/SequentialZK/ComputationalReduction.lean` | 271 | 99 |
| `TCSlib/Cryptography/Composability/SequentialZK/ComputationalTransfer.lean` | 100 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/Congruence.lean` | 68 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/ContinuationProbability.lean` | 354 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/Efficiency.lean` | 306 | 99 |
| `TCSlib/Cryptography/Composability/SequentialZK/EndpointSampling.lean` | 269 | 95 |
| `TCSlib/Cryptography/Composability/SequentialZK/ErrSoundness.lean` | 85 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/ExecutionBounds.lean` | 88 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/HybridRecursion.lean` | 93 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/Normalization.lean` | 98 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/NormalizationMachine.lean` | 97 | 95 |
| `TCSlib/Cryptography/Composability/SequentialZK/NormalizedStep.lean` | 126 | 96 |
| `TCSlib/Cryptography/Composability/SequentialZK/PaddedProverSpec.lean` | 142 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/PhaseView.lean` | 168 | 95 |
| `TCSlib/Cryptography/Composability/SequentialZK/Phases.lean` | 142 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/PrefixFolds.lean` | 103 | 95 |
| `TCSlib/Cryptography/Composability/SequentialZK/PrefixLaws.lean` | 118 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/ProofTransfers.lean` | 75 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/RealPhases.lean` | 207 | 95 |
| `TCSlib/Cryptography/Composability/SequentialZK/RealPrefixBounds.lean` | 101 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/ReductionAdvantage.lean` | 111 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/RepeatedSoundness.lean` | 218 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/RepeatedVerifier.lean` | 194 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/SimulatorMachine.lean` | 351 | 97 |
| `TCSlib/Cryptography/Composability/SequentialZK/Soundness.lean` | 163 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/Statistical.lean` | 73 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/StatisticalPostprocess.lean` | 60 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/StatisticalPrefix.lean` | 154 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/StatisticalRecursion.lean` | 139 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/StatisticalTransfer.lean` | 115 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/SuffixLaws.lean` | 122 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/SuffixMachine.lean` | 323 | 99 |
| `TCSlib/Cryptography/Composability/SequentialZK/VerifierPrefix.lean` | 89 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/WrappedVerifier.lean` | 207 | 96 |
| `TCSlib/Cryptography/ZeroKnowledge/Defs.lean` | 754 | 99 |

## Historical per-declaration overlap and implementation appendices

### Checkpoint3 overlap compendium (historical cutoff)

## Overlap and reuse

Searches before implementation are in `lead-searches.log` and each subagent's search logs.
Every overlap below is either direct reuse or a disclosed generalization; no foreign private
lemma was copied.

- `ProverBounded.seqRep`: nearest Interaction.lean:383 `ProverBounded.mono` changes the bound,
  not the protocol; the new lemma reads the repeated prover and reuses proverBounded_iff.
- `seqVerifier_exec_first`: nearest owned original `seqRep_exec_phase` (base line 287) assumes
  the honest repeated prover. The new induction covers an arbitrary unchanged prover in
  phase zero, using the published move-index readers rather than that stronger honest premise.
- `seqRep_outV_eq`: combines owned `seqVerdict_eq` (base :233) and Interaction.lean:449 outV_eq
  with the existing move count. It publishes the final-history specialization.
- `seqRep_exec_phase_take`: combines original seqRep_exec_phase, the new generic exec_snd_take,
  and core List.take_drop; it adds final-history restriction, not a duplicate phase induction.
- `seqRep_complete`: nearest graph-specific completeness arguments in
  ZeroKnowledge/ThreeColoring/ProtocolProofs.lean and GraphIsomorphism/Proofs.lean; directly
  reuses HardcoreBit/Basic.lean:110 forall_of_uprob_eq_one and :123 uprob_eq_one_of_forall,
  Adversary.lean:98 length_coinBlock and :216 ofFn_padFin_of_length.
- `seqRep_reject_of_first`: new aggregate-conjunction consequence of the first-phase reader;
  nearest original seqRep_exec_phase has the different honest-prover premise noted above.
- `seqRep_sound_first`: reuses HardcoreBit.pushesUniform_restrict/prodMap and public
  Asymptotic/ReductionSupport.lean:288 take_ofFn_castLE. GI/Proofs.lean:813
  pushesUniform_castLE is a specialization of the same restriction reader, not copied.
- `seqProver_efficient` and `seqVerifier_efficient`: construction-specific bridges directly
  reuse SeqEfficiency.phase_efficient and verifier_efficient; no machine argument is repeated.
- `StatZK_iff`: exact defining reader, analogous to Defs.lean:164 ZK_iff; added only with the
  explicit scope approval below, in its defining file.
- `encodeMsgs_eq_encWords`: exactly matches the local have in SecureComputation/Yao.lean:352,
  outside the allowed closure. It is re-derived from published encoding nil/cons readers.
  ThreeColoring/Machines.lean:911 encodeMsgs_eq_flatMap is another nearest relative.
- `normalizeMsgs` and its reader/invariants are new canonical-slot operations. Their length,
  per-message, fixed-point, and encoding bounds directly reuse decWords_encWords,
  List.take_of_length_le, and BinaryArith/Words.lean:81 length_encWords_le.
  CommitmentLemmas.lean:241 gives the same generic encoding-size bound with a larger dependency;
  no copy is used. `length_encodeMsgs_normalizeMsgs_le` specializes the directly reused bound.
- `polyTimeComputable_encWords_decWords`, `polyTimeComputable_decWords_getD`, and
  `polyTimeComputable_encode_normalizeMsgs`: directly reuse Words.lean:221 mapW,
  BinaryArith/Loops.lean:391 getW, EncodingMachines.lean:459 truncate_poly, and
  ThreeColoring/Machines.lean:159 counted emission, rather than copying hosts.
- `take_encodeMsgs` uses CommitmentLemmas.lean:233 encodeMsgs_append plus List.take_append;
  its new encoded-prefix formula had no public match in the searched closure. `takeMsgs_poly`
  directly composes this with the public drop/count machinery. `phase_poly`,
  `phase_efficient`, `verdict_poly`, and `verifier_efficient` reuse GI/Proofs.lean's
  efficient_of_polyTime and GI/EfficiencyRep.lean's message-count/coin-slice readers and the
  public bounded-index search. All per-declaration details are in seq-zk-b/searches.md.
- `exec_prefix`, `exec_fst_take`, and `exec_snd_take` are execution specializations of
  published exec_succ and core prefix_iff_eq_take, not copies of a prior execution lemma.
- `uprob_adaptive_all_le` generalizes ThreeColoring/Protocol.lean:307 `uprob_adaptive_escape` from rate 1-1/m to arbitrary nonnegative s. It
  directly reuses OneWayFunctions/Basic.lean:90 uprob_and_le_mul and Fin.snocEquiv.
  Its local cast algebra re-derives the general-type versions of private :275/:286
  challengesBefore_snoc_castSucc/last, which are specialized and private. No private lemma
  is referenced or copied; this overlap is explicitly disclosed.


### Additional overlap and reuse in checkpoint 2

Every relative below is direct reuse or an explicitly disclosed generalization. Raw searches
precede implementation in the lead and subagent search logs. No private proof was copied.

- exec_boundary_lengths factors the arithmetic previously local to original
  seqRep_exec_phase (issue-base SequentialZK.lean:280); it reuses owned length/count readers.
- seqRep_verifierSpec and seqRep_proverSpec instantiate each abstract field from the
  construction's published coin/round/mover/next/index/count readers, avoiding import cycles.
- PrefixFolds realStep/simStep and realPrefix/simPrefix are typed semantic counterparts of
  SimulatorMachine.phasePrefix (same helper directory). They directly use existing core
  Fin.foldl, introduce no machine/control host, and give both real and simulated families.
- PrefixLaws zero/succ/snoc readers directly reuse core Fin.foldl_zero/foldl_succ_last and
  Fin.snoc_castSucc/last. simPrefix_eq_phasePrefix directly reuses phasePrefix_succ_simulate;
  it does not repeat tape/block interpretation or a machine-efficiency proof.
- ProofTransfers.next_length_le specializes the PaddedProverSpec next field, analogous to
  owned ProverBounded.seqRep but abstract in the source protocol. The owned construction
  result is unavailable to its imported helper without a cycle. ProofTransfers.complete
  directly reuses Protocol.ProverBounded.exists_complete (InteractiveProofs.lean:249)
  with a local relation pairing the original bound and pointwise complete witness.

Additional per-declaration records are included verbatim below. Source line references
are from the revisions actually searched; their sources/checks are preserved in evidence.

### PaddedProverSpec overlap and reuse

The lead approved this construction contract, including all-natural-index/all-natural-phase
reader fields and the two direct endpoint methods. The structure has no relation or B premise.

New declarations:
- PaddedProverSpec and its nine field projections package direct source construction equations.
  The nearest related contract is seq-zk-c's public Composability.PaddedVerifierSpec at
  SequentialZK/RepeatedVerifier.lean:38. The new structure is its prover-side counterpart:
  it has no terminal-verdict field, fixes the honest prover rather than the verifier, and
  allows any cheating verifier. Its original_count is for fixed π.P and arbitrary V, the
  dual of that contract's arbitrary-P/fixed-π.V local_length field. Its boundary reader holds
  at every natural phase index, as supplied by the owned global length readers. No foreign
  equation theorem is re-proved: the owned module will instantiate each field once from
  seqProver_next, seqRep_P, seqRep_rounds_eval, seqRep_verifierFirst, proverMoveIndex_exec,
  exec_fst_length/exec_snd_length, the public count readers and the mover-period reader.
- PaddedProverSpec.real_phase directly instantiates the new public exec_real_phase
  (RealPhases.lean:~92), with no repeated execution induction or arithmetic proof.
- PaddedProverSpec.padded_phase directly instantiates the new public exec_padded_real_phase
  (RealPhases.lean:~161), using the contract's original_count at phaseVerifier V and its
  phase-boundary fields. It does not repeat any filler or phase proof.

No equivalent padded-prover contract was found in TCSlib or pinned Mathlib. Raw searches are
in padded-prover-spec-searches.log. The contract and its methods are sequential-construction
specific and should remain in this helper; no frozen-file promotion/edit is requested.


### RealPhases overlap and reuse

This helper imports no owned module. Source-only copies of author seq-zk-c's checked stable
Soundness and updated Phases modules were independently compiled in seq-zk-b's olean tree.
Hashes, provenance, and raw successful compile output are retained. Those sources were not
edited and no foreign olean was copied.

Raw searches are in real-phases-searches.log. They found no generic empty-prover suffix reader
or arbitrary-verifier real/padded sequential endpoint in TCSlib or pinned Mathlib.

New declarations:
- exec_snd_empty: nearest relative Composability.exec_prefix
  (SequentialZK/Soundness.lean:42) shows only that both earlier histories remain prefixes.
  Empty contents of all newly received prover messages require the stronger suffix statement.
  The elementary induction uses only public exec_succ, mover readers, and List append/replicate
  equations; no private lemma or proof block is copied. Its arithmetic identification uses
  the public List.length_append/length_replicate and Nat.add_sub_cancel_left readers.
- exec_real_phase: DIRECTLY REUSES the newly checked public
  Composability.exec_phase_of_moves (SequentialZK/Phases.lean:~58), with original P and the
  fixed-tape phaseVerifier V. It does not duplicate that real-phase induction. The verifier
  contract directly reuses phaseVerifier_next_phaseAux (WrappedVerifier.lean:128),
  Composability.exec_snd_take (Soundness.lean:76), and List.take_append_drop.
  Nearest source endpoint is owned Protocol.seqRep_exec_phase (base SequentialZK.lean:280),
  but that theorem couples two honest repeated parties, whereas this theorem handles an
  arbitrary cheating verifier and the zero-coin fixed-prefix wrapper. The new proof's local
  quotient/remainder equalities have the same arithmetic formulas as unexported local hmod/
  hdiv inside that owned proof; they are re-derived using public Nat.add_mul_mod_self_left,
  Nat.add_mul_div_left, Nat.mod_eq_of_lt and Nat.div_eq_of_lt. No private fact is referenced
  or copied. Index recovery and phase-start counts are supplied by the caller.
- exec_padded_real_phase: directly combines exec_real_phase and exec_snd_empty. The shifted
  filler-position remainder is proved through public Nat arithmetic readers. The exact
  number k-p uses caller-provided initial/final/local counts, rather than duplicating owned
  alternating-move count proofs. The arbitrary verifier's filler replies have no premise.

Promotion: exec_snd_empty belongs beside the interactive-execution API in Interaction.lean
at a shared-file window. The two sequential real/padded endpoint results belong in this
source-specific helper. No frozen-file edit or new host is needed.


### SimulatorMachine overlap, reuse and host record

The lead approved phasePrefix as a public mathematical semantic recursion, realized using the
published ColMachines.polyTimeComputable_loopState' host. No new control host, transition
machine, or private machine is built. PhaseView was copied as an authorized stable source;
its hash and independent compile log are retained. It was not edited; no agent-a olean copied.

Raw searches are in simulator-searches.log. Earlier Efficiency/WrappedVerifier searches cover
coin slicing, uniform output/layout combinators, and canonical prefix reencoding. No exact
normalized-prefix simulator was found in TCSlib or pinned Mathlib.

New declaration nearest relatives and reuse:
- phasePrefix / zero / succ / succ_simulate: public mathematical sequence of canonical
  normalized simulator calls, following the issued source sketch. Nearest repeated-simulator
  code is PerfectZKAbort.retry (ZeroKnowledge/Defs.lean:337) and attempt (:319): their input is
  fixed and output stops at the first success, rather than changing auxiliary prefix and
  accumulating normalized messages. S.simulate_eq, S.runAt_eq and S.runAtL readers are reused
  to match the published simulator convention exactly.
- length_phasePrefix: new exact i*k count obtained from public
  length_normalizePhaseMsgs (PhaseView.lean:~97) and List append/replicate length readers.
- length_le_of_mem_phasePrefix: new prefix bound obtained by induction from public
  length_le_of_mem_normalizePhaseMsgs (PhaseView.lean:~105) and empty fillers.
- length_encodeMsgs_phasePrefix_le: direct use of public
  CommitmentLemmas.length_encodeMsgs_le (CommitmentLemmas.lean:241), together with the two
  preceding prefix readers. No generic encoding-size proof is copied.
- encode_emptyMsgs_poly: counted emission of the fixed chunk pairEncode [] [] through public
  ColMachines.polyTimeComputable_flatMap_range (ThreeColoring/Machines.lean:~158).
  Core List.map_const' and flatMap_map identify the result with existing encodeMsgs_eq_flatMap.
  This generic encoding composition has no exact prior counterpart found by the searches.
- phasePrefix_poly: existing ColMachines.polyTimeComputable_loopState' (:101), unary arithmetic,
  GI.coinSlice_poly (GraphIsomorphism/EfficiencyRep.lean:376), agent-a's public normalized-view
  machine, phaseAux_poly, and NUPPT output/layout readers are reused. The only new invariant is
  the exact identity of the existing host's state with the encoded semantic prefix. Nearest
  concrete consumers are ThreeColoring proverRepStr_poly and PerfectZKAbort.retry_poly
  (Defs.lean:412); their fixed protocol/first-success outputs prevent direct reuse.
- exists_phaseSimulator: uses public NUPPT.ofPolyTimeUniform and its uniform/coins/activation
  readers. Nearest relative exists_retrySimulator (Defs.lean:433) uses n retries on the same
  input, whereas this simulator threads phaseAux data and emits the entire canonical view.

Promotion requests: phasePrefix and the simulator construction are source-specific and stay
in this helper. The small encode_emptyMsgs_poly composition could later move beside the shared
encoded-history machines. No frozen-file changes or scope requests are needed.


### WrappedVerifier searches, reuse and overlap

The lead approved this helper and the source-only copies of agent-a Normalization.lean and
NormalizationMachine.lean. Their provenance hashes are in wrapped-dependency-provenance.log.
Each copied source was compiled independently in seq-zk-b's olean tree. They were not edited.

Raw reuse searches are in wrapped-searches.log; additional read-only source comparison:
SecureComputation/Yao.lean:352 derives encodeMsgs=encWords locally before its decodeMsgs reader.
The new helper instead imports and reuses agent-a's public encodeMsgs_eq_encWords and
polyTimeComputable_encWords_decWords, avoiding a fresh encoding-equality proof.

New declaration overlaps:
- phaseAux, phaseAux_eq: phase-specific nested-pair data encoding; nearest construction
  LevinTransfer.liftVerifier (ZeroKnowledge/NPLemmas.lean:268) stores an original input and
  auxiliary input in a pair. This phase construction additionally stores a fixed verifier
  tape, phase index and arbitrary earlier message prefix, so the existing construction does
  not have its required interface.
- phaseAux_fields, phaseAux_z, phaseAux_tape, phaseAux_phase, phaseAux_prefix: specialized
  readers for the new encoding. They reuse public pairFstD_pairEncode/pairSndD_pairEncode,
  agent-a encodeMsgs_eq_encWords, BinArith.decWords_encWords (BinaryArith/Words.lean:116),
  and core List.length_replicate, rather than reproving a generic pair or decoder fact.
- phaseAux_length: specialized exact length, directly reusing Turing.length_pairEncode
  (TuringMachine/Encoding.lean:220). It retains the phase index in unary for later advice bounds.
- phaseVerifier, phaseVerifier_coins, phaseVerifier_next, phaseVerifier_coinLen,
  phaseVerifier_next_phaseAux: new fixed-tape, prefix-extending strategy and its readers.
  Nearest construction LevinTransfer.liftVerifier/liftVerifier_next (:268/:274) changes the
  common input and tape prefix rather than fixing an auxiliary tape and extending history.
  Neither that construction nor its statement can be reused directly.
- phaseVerifier_efficient: nearest relative LevinTransfer.liftVerifier_efficient (:295)
  and earlier SeqEfficiency.phase_poly. It uses the same existing uniform output/layout
  combinators, plus agent-a's canonical prefix reencoding and public
  CommitmentLemmas.encodeMsgs_append (:233). The imported published constituent lemmas
  are reused; no machine, private lemma, host or generic canonicalization proof is copied.

Promotion request: phaseAux and phaseVerifier are specific to this sequential-composition
construction and should stay here. A future shared fixed-tape strategy-preprocessing closure
lemma could subsume phaseVerifier_efficient and LevinTransfer.liftVerifier_efficient; no frozen
file change is needed for this delivery.

- phaseAux_poly: direct repeated use of public PolyTimeComputable.pairEncode followed by
  the new encoding equation. Nearest generic relative NUPPT.polyTimeComputable_layout
  (Randomized/Closure.lean:~180) assembles a different four-field machine layout, so the
  exact phase auxiliary encoding requires this short composition.

- phaseAux_length_le: directly applies the new phaseAux_length and public
  CommitmentLemmas.length_encodeMsgs_le (:241), then monotonicity of multiplication.
  It specializes the generic encoding bound to the new auxiliary layout; the generic
  message bound is reused rather than reproved.


## ExecutionBounds continuation

ExecutionBounds.lean is 88 lines, maximum width 94, with no admissions or simp attributes.
It imports only stable Normalization.lean; the previous four source hashes were asserted
unchanged when this report was finalized. Public searches found no existing generic message
length bound for Cryptography.exec.

New declarations and overlap:

- exec_snd_bounded derives a bound on every verifier-received message from a fixed prover
  tape's uniform next-message bound. It uses only Interaction.lean's exec_zero and exec_succ
  readers (lines 262 and 266 in the base). Related
  Games/Protocols.lean:316 execT_trace bounds concern a different oracle protocol and only message
  counts; they do not provide this statement. No private argument was copied.
- exec_snd_slice_bounded directly specializes exec_snd_bounded through the public core
  List.mem_of_mem_take and List.mem_of_mem_drop readers. It adds no list-membership lemma.
- length_encodeMsgs_exec_snd_le applies Words.lean:81 length_encWords_le through the checked
  encodeMsgs_eq_encWords bridge and exec_snd_bounded. It is execution-specific. No duplicate
  generic encoded-history bound was added; the nearest existing generic
  CommitmentLemmas.lean:241 length_encodeMsgs_le is subsumed by the Words theorem reused.

Promotion request: generic execution-message bounds belong beside the execution readers in
Interaction.lean at a future shared-file window. No frozen-file edit was made or needed.

ExecutionBounds check01 passed with one unused simp argument; the argument was removed in
its single proof block. Check02 passes with no diagnostics, RSS 1,560,723,456 bytes and
1.77 seconds compiler wall time. Both raw attempts, preimplementation searches, width/hash
ledger, diagnostic summary and own-tag slots are retained. No Lake command ran. The hybrid
outline now marks the execution-message-bound obligation resolved by this checked helper;
the separate cheating-verifier padded-phase endpoint reader remains a lead obligation.

## Prefix-hardwired prover and offset execution

After approving the proposed interface, the lead assigned a NEW helper `Phases.lean`,
importing the stable Soundness helper. The new public construction `prefixProver` fixes
an earlier received history, auxiliary input and prover tape; generated `coins` and `next`
readers expose its zero coin polynomial and append contract. The new theorem `exec_phase`
identifies any corresponding segment of the full execution, under the mover and verifier
reply hypotheses, with a run of this prefix-hardwired prover. No owned definitions are
imported or unfolded. The optional bounded verifier-congruence theorem remains a design
proposal only and has not been added.

Overlap and promotion:
- `prefixProver` is a fixed-tape/fixed-prefix strategy wrapper. The nearest owned wrapper is
  `Protocol.seqProver`, original `SequentialZK.lean:200`; the latter slices prover coins and
  drops earlier received messages, while this one fixes the original tape and prepends
  earlier received messages. It does not restate that construction. No equivalent public
  wrapper was found by the recorded searches for `hardwir`, fixed tape, prefix strategy,
  zero-coin strategies, and prover next-message append calls.
- `prefixProver_coins` and `prefixProver_next` are generated field readers of this new
  construction, not re-proved foreign readers.
- `exec_phase` shares the induction architecture of the owned honest-run
  `Protocol.seqRep_exec_phase` (`SequentialZK.lean:280` at issue base), but applies to any
  prover and any two verifier strategies under an explicit real-phase contract. It uses
  only published `exec_zero`/`exec_succ`, generated prefixProver readers, and core List
  append/drop equations. No proof block or private declaration was copied.
- The nearest other general execution comparison is public
  `LevinTransfer.exec_congr` at `ZeroKnowledge/NPLemmas.lean:88`; it compares whole runs
  from empty histories under equality on all histories. It cannot supply an execution
  segment with fixed nonempty earlier histories. It is outside the supplied bootstrap
  closure and is not imported.
- Promotion request: prefixProver and exec_phase belong beside the interactive-execution
  API in `ZeroKnowledge/Interaction.lean` at a shared-file window. The permitted helper
  retains them for this fill.

Phases check history:
- Attempt 01: exit 1 with one unresolved false-mover branch. The branch retained
  `if false = true`; adding the public Bool false-equality and if-false simplification
  closed it. Max RSS 2,147,205,120 bytes. Raw log retained.
- Attempt 02: exit 0 with 0 errors and 0 warnings, fresh olean produced. Max RSS
  2,154,381,312 bytes. Raw log retained.

Final Phases.lean: 96 lines, maximum width 94, SHA-256 `22d94a4e178f0a0f34b4fabb3609a7ca33a171a9e38cf275d8dcf0e79e33a9e2`. No admissions.

## Congruence along the reached source histories

The lead assigned a NEW `Congruence.lean` for checkpoint 2 tape nonanticipation and later
ZK. It imports only `ZeroKnowledge/Interaction.lean` and introduces the public theorem
`exec_congr_reachable`. Its hypotheses compare replies only at active positions before
`g`, on each source execution's actual received history; prover and verifier tapes may
both differ. The conclusion is equality of the complete executions after `g` moves.
It uses only published `exec_zero` and `exec_succ` readers and public Bool equalities.
No previous helper source was changed.

Overlap and promotion:
- Nearest relative: public `LevinTransfer.exec_congr`,
  `TCSlib/Cryptography/ZeroKnowledge/NPLemmas.lean:88`. That theorem permits different
  inputs but requires each party's replies to agree on **every** possible history.
  The new theorem has a weaker reached-history premise at a bounded number of moves,
  and identical common/auxiliary inputs. The published theorem cannot directly discharge
  this premise and is outside the supplied order closure. No existing proof block was
  copied; the standard induction is re-derived from the public execution readers.
- Searches for `exec_congr|exec_eq_of|next_eq_on|reachable.*exec|exec.*reachable` across
  TCSlib and for execution congruence/reachability under pinned Mathlib/Computability
  found no closer reusable theorem. Raw output is in congruence-searches.log.
- Promotion request: `exec_congr_reachable` belongs beside `exec_succ` in
  `ZeroKnowledge/Interaction.lean` in a shared-file window.

Congruence check attempt 01: exit 0 with 0 errors and 0 warnings, fresh olean produced.
Max RSS 1,549,713,408 bytes; raw log and structured result retained. The invocation used
this sub-agent's own olean tree and tag through the host-wide shared slot wrapper.

Final Congruence.lean: 68 lines, maximum width 94, SHA-256 `724fb756e96ac9f210b2a0f75dd9d403bddc2a0c226225a4ba01e9f284efcb56`; no admissions.

## Earlier verifier blocks determine the earlier transcript

The lead assigned NEW `VerifierPrefix.lean`. The public theorem
`exec_eq_of_verifier_blocks` accepts an arbitrary padded verifier, an arbitrary terminal
reply function, and a move-index recovery hypothesis on the actual source run. It proves
that agreement of verifier coin blocks below `j<q` gives equality of the full transcript
before move `2*k*j`, against the same arbitrary prover and fixed prover tape.

The zero-round case has no moves. In the positive-round case the recovered index gives
`2*received.length ≤ t+1`, excluding the terminal history `q*k` before the cutoff. The
phase index is below `j` by the public core theorem `Nat.div_lt_of_lt_mul`. Reusing
`exec_congr_reachable` and the supplied padded reply reader then identifies the runs.
The proof does not unfold any owned definition or the body of `coinBlock`; `dsimp only`
reduces the local `let idx` appearing explicitly in its own hypothesis.

Overlap and reuse:
- Directly reuses this sub-agent's published `Composability.exec_congr_reachable` in
  `SequentialZK/Congruence.lean:42`. No congruence proof is duplicated.
- The nearest owned construction reader is `Protocol.seqRep_exec_phase`, original
  `SequentialZK.lean:280`, which compares an honest phase with an original execution.
  That theorem neither handles arbitrary cheating provers nor compares two full verifier
  tapes, so it cannot give this nonanticipation statement.
- The lead's new `Protocol.seqVerifier_exec_first` handles phase zero against the original
  verifier; it also does not identify earlier transcripts for arbitrary two tapes and a
  phase cutoff. The new helper contains no copy of that proof.
- Specialized earlier transcript readers such as `GI.exec_vfirst_eq` in
  `ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean:90` describe history-independent
  verifier messages. Here the underlying verifier may depend on its within-phase history,
  so that interface cannot be reused. No specialized proof was copied.
- The move-index arithmetic is supplied by the lead, not re-proved from a foreign count
  function. Core `Nat.div_lt_of_lt_mul` is directly reused rather than copied.
- The statement belongs to this fill's padded-phase helper layer; no frozen-file promotion
  or reader request is required for it.

Searches for coin-block execution/prefix and verifier-tape dependencies in TCSlib and
pinned Mathlib/Computability are recorded in verifier-prefix-searches.log. No equivalent
published padded-verifier nonanticipation theorem was found. No new Mathlib root was
added, and no earlier helper was changed.

VerifierPrefix attempt 01: exit 0, 0 errors, 0 warnings, fresh olean produced. Max RSS
2,170,912,768 bytes. Exact invocation, raw log, source audit, and slot lines are included.

Final VerifierPrefix.lean: 89 lines, maximum width 94, SHA-256 `6be4e9f9c220e9ba15798dc0b61bc9a7cafc5c9ea1ec62a673de7c2d5e26c7f7`; no admissions.

## Explicit soundness error and fixed-prefix section bounds

NEW `ErrSoundness.lean` contains three checked declarations:
- `InteractiveProofErr.uprob_accept_le`: for every no-instance and prover, acceptance
  probability is at most the stated error `s(|x|)`.
- `InteractiveProofErr.sound_nonneg`: the error is nonnegative at every no-instance length.
- `Composability.prefixProver_accept_le`: when the earlier received messages and original
  prover tape are hardwired, the acceptance probability over a fresh original verifier
  tape alone is at most `s(|x|)`. The wrapper's public zero-coin reader shows that every
  local prover coin string is empty. Published output/transcript equations, `uprob_prod`,
  and `HardcoreBit.uexp_const` then remove its unused coin coordinate.

Search and overlap disclosure:
- No `InteractiveProofErr` acceptance or nonnegativity bound was found by the recorded
  TCSlib/Mathlib searches. Nearest public relative is
  `InteractiveProof.exists_uprob_accept_lt` at `ZeroKnowledge/InteractiveProofs.lean:193`.
  It returns a strict bound for an existential negligible error; it cannot provide the
  frozen arbitrary explicit-error value `s`. The new acceptance proof adapts the same
  complement-of-rejection argument, directly reusing `uprob_mono`, `uprob_not`, and the
  public soundness field. This overlap is explicit; it is not a copied private theorem.
- `sound_nonneg` directly specializes the public Mathlib order equivalence
  `sub_le_self_iff` generated at
  `Mathlib/Algebra/Order/Group/Unbundled/Basic.lean:214`, using `uprob_le_one`. No order or
  probability fact is re-proved.
- `prefixProver_accept_le` specializes the new acceptance bound to the existing public
  prefixProver wrapper. Its marginalization is direct reuse of the uniform product and
  constant-average readers. It does not re-prove the generic uniform second-projection law
  (`HardcoreBit.pushesUniform_snd`, HardcoreBit/Basic.lean:210) or the averaging statement
  `Protocol.exists_proverCoins_le` (Interaction.lean:548).
- Promotion request: the first two generic methods belong in
  `ZeroKnowledge/InteractiveProofs.lean` at a shared-file window. The prefix-specific bound
  remains in this fill's helper layer. No frozen file was edited.

Diagnosed elaboration and authorized proof-debugging exception:
- Attempt 01 started 09:37:03 UTC, acquired its slot at 09:37:08, and was running rather
  than queued. The sub-agent initially inferred a slot wait from the empty buffered output;
  the lead corrected this status, and the process snapshot confirmed the running child.
- A read-only one-second stack sample showed active `evalCalc`/`elabCalcSteps` and deep
  `isExprDefEqExpensive` recursion in the probability calculation. Mac headroom measured
  by the lead was 6.438 GiB, above the floor; this was not E-RES.
- The lead explicitly authorized a graceful interruption under Seyoon's best-judgment
  exception. Its verbatim instruction is preserved in err-soundness-debug-authorization.md.
  The exact child PID96807 and parent96799 and full Lean command were re-verified before
  SIGINT. Only that child was signaled; no wrapper or other job was touched.
- The complete attempt source, raw checker output, process inspection, interruption record,
  and stack sample are retained. Lean exited130, checker exited1, and no olean was produced.
  It ran619.72s with maxRSS3,831,316,480 bytes. This was diagnosed proof debugging, not an
  elapsed-time timeout, resource shortage, or claimed proof failure.
- Replaced only the pathological probability calc with an explicit reader-based product
  proof. Attempt02 passed with 0 errors and 0 warnings, fresh olean, runtime6.63s,
  CPU1.43s, maxRSS2,164,834,304 bytes. No previous helper source changed.

Large raw diagnostic representation:
- Raw sample size145,047,604 bytes, SHA256
  `440251c95334e50dfb92d8140690daa5315ec081bb69b6135602a9ce0187deec`.
- Deliver the lossless numbered part `err-soundness-diagnostics-01.zip`, with its entry list
  and verification log. Its sole member is the complete original err-soundness-sample.log;
  streamed decompression was SHA256-checked byte-for-byte, with the original length.
- ZIP size1,916,631 bytes. The original raw local sample remains outside the payload at
  `.lake/seq-zk-c-raw-diagnostics/err-soundness-sample.log`. The completed sample was moved
  only after verified compression; no running log was moved. No raw bytes are omitted.

Final ErrSoundness.lean: 85 lines, maximum width 94, SHA-256 `4ada2d316efd3efd4d387dde0880b9360ea66fff55581b2535081dc09ac76705`; no admissions.

## General phase-coupling extension for the simulator worker

At the lead's request, added `exec_phase_of_moves` to Phases.lean with arbitrary local
strategies, auxiliary inputs and tapes. Each supplied active-move equation reads a local
party on the reached source history with its fixed old prefix dropped. The generic
induction proves both prefix-append history decompositions. The previous `exec_phase`
statement is unchanged and now applies this theorem; its prover premise follows from
`exec_prefix`, the public List prefix append equation, and prefixProver_next. Its sketch
was synchronized. There is only one phase induction; no duplicate proof was retained.

Overlap: the new theorem generalizes this same file's prior exec_phase, whose old source
and source audit are retained as phases-before-generalization files. The new generic
induction replaces that old induction; the old API is a direct published-theorem reuse.
No foreign or private proof was copied. This belongs beside the generic interactive
execution API at a shared-file window, extending the prior promotion request.

Phase generalization check01: exit0, no errors/warnings, fresh olean, runtime4.67s,
maxRSS2,155,839,488 bytes. Dependent ErrSoundness recheck: exit0, no errors/warnings,
fresh olean, runtime2.70s, maxRSS2,165,014,528 bytes. It is the only owned helper directly
importing Phases; the simulator worker was sent the exact checked signature and source
and will recheck its new consuming helpers in its own tree. Existing API preserved.

Current Phases.lean: 142lines/max94, SHA256`dcec347fe5aaf7407861a8248809c400c4d1f8ad85b6c6195bacd4a7261d13be`.

## Full generic explicit-error repetition engine

The lead approved the PaddedVerifierSpec interface before substantial implementation.
`RepeatedVerifier.lean` supplies the public proposition-valued structure and its two
phase readers. `RepeatedSoundness.lean` supplies the actual probability engine. Neither
imports or unfolds the owned SequentialZK module, and no target statement is weakened.

New declarations and formulas:
- `PaddedVerifierSpec π ρ x q p terminal`: the nine displayed coin/round/first-mover,
  padded-next, binary-terminal, actual-index, boundary-length, original-length, and mover
  periodicity properties. Every public field has a formula docstring in Lean argument order.
- `PaddedVerifierSpec.phase_exec`: both histories of a real phase equal their fixed earlier
  histories followed by an original-verifier execution against prefixProver.
- `PaddedVerifierSpec.phase_take`: taking the p real prover slots of a final phase history
  recovers that original-verifier history. The k=0 branch is explicit.
- Private `phaseTape` and `phaseTape_block`: table coins are read through the canonical
  FunFamily.blocks equivalence and its published ofFn reader.
- Private `zeroTail`: a finite table with prescribed earlier blocks and explicit all-false
  future blocks. Private `phaseGood`: original acceptance with its induced earlier
  received history and fixed prover tape. Private `phaseGood_section` specializes the
  checked prefixProver acceptance bound. Private `phaseGood_of_test` identifies actual
  phase tests using VerifierPrefix and phase_take.
- `PaddedVerifierSpec.outV_eq`: repeated output equals its terminal function on the
  complete source transcript, through public Protocol output/transcript readers.
- `PaddedVerifierSpec.accept_le`: original explicit error s gives aggregate acceptance
  probability at most s(|x|)^q against every prover.
- `PaddedVerifierSpec.sound`: the binary aggregate verdict gives rejection probability at
  least1-s(|x|)^q. The q=0 branch is explicit. No q-positivity premise is added to this
  helper, and the frozen owned statements retain their original hypotheses.

Overlap and reuse, including every restatement/specialization:
- PaddedVerifierSpec's fields package the owned equations as caller-supplied hypotheses;
  they are not new proofs or claims that an arbitrary protocol satisfies them. Nearest
  original SequentialZK.lean readers: seqVerifier/its generated readers at236;
  seqVerdict_eq at222; seqRep_rounds_eval at261 and seqRep fields at254;
  verifierMoveIndex_eq at117 and verifierMoveIndex_exec at182; exec_fst_length at153 and
  exec_snd_length at163 with countP_moverIsV at133/countP_not_moverIsV at143;
  proverMoves_eq at127; moverIsV_two_mul_add at128. They cannot be imported into a helper
  without a cycle; the lead instantiates each field from exactly these published readers.
- phase_exec directly reuses exec_phase, including its generic induction. Its nearest
  owned relative is honest-only seqRep_exec_phase (issue-base line280); the new reader
  permits an arbitrary prover and an abstract verifier specification. Its quotient and
  remainder arithmetic directly reuses the core Nat add-multiple division/modulo readers;
  it does not copy a private lemma or add another execution induction.
- phase_take directly reuses phase_exec, exec_snd_take and the supplied length readers.
  Nearest lead checkpoint1 reader: Protocol.seqRep_exec_phase_take at owned line478
  (source queried during this work); that theorem is honest-only and unavailable to the
  abstract helper. The new reader generalizes the final-phase restriction to every prover.
- Private phaseTape is a local string alias for (FunFamily.blocks q c).symm. Nearest alias
  is public GI.blocksEquiv at GraphIsomorphism/SoundnessRep.lean:207. Private phaseTape_block
  has nearest relative public GI.coinSlice_blocksEquiv at that file:224. It is not a copy
  of the latter's entrywise proof: it directly specializes the already-imported canonical
  FunFamily.ofFn_blocks reader (Asymptotic/Adversary.lean:277), using Equiv.apply_symm_apply.
  This canonical public reader is the reused interface; no GI implementation is duplicated.
- Private zeroTail has nearest public relative extendStream at
  Pseudorandom/Functions/LazySampling.lean:196 (inside the supplied closure). extendStream
  returns a stream on all naturals and uses Classical.arbitrary beyond its prefix. The new
  finite-table leaf uses the explicitly requested all-false fallback, including truncation
  if i exceeds q; extendStream does not publish that exact fallback. Mathlib Function.extend
  (Logic/Function/Basic.lean:686) is a choice-based extension along a map, not this explicit
  total finite-prefix/truncation leaf. The two-line conditional definition is disclosed;
  no existing extension theorem or private proof was copied or re-proved.
- phaseGood is a local predicate naming the original verifier/prefixProver test, rather
  than a new iteration host. phaseGood_section directly reuses prefixProver_accept_le;
  it merely substitutes the earlier transcript of the zero-tail table as its fixed prefix.
- phaseGood_of_test directly reuses exec_eq_of_verifier_blocks and phase_take. Its only
  extra table fact reads the prescribed prefix of zeroTail; Fin casts reduce by the core
  projection equations. There is no duplicated nonanticipation or phase induction.
- outV_eq's nearest lead reader is Protocol.seqRep_outV_eq, owned line453 when queried.
  The new theorem is the abstract-spec counterpart; it directly reads supplied rounds,
  first-mover, boundary, and next equations through published Protocol readers. It cannot
  import that construction-specific owned theorem without a cycle.
- accept_le directly reuses Protocol.exists_proverCoins_le (Interaction.lean:548), the
  canonical FunFamily.blocks equivalence/readers, VerifierPrefix through the phase-test
  reader, prefixProver_accept_le through phaseGood_section, and uprob_adaptive_all_le.
  Nearest specialized repetition proof is GI.gniRep_accept_le at
  GraphIsomorphism/SoundnessRep.lean:344, with its protocol-specific 2^-n+sampling-error
  rate. It does not supply arbitrary s or this abstract padded verifier; no proof was copied.
- sound uses outV_eq, the supplied binary terminal equation, OneWay.uprob_congr,
  uprob_not, and Mathlib sub_le_sub_left directly. The nearest specialized complement
  conversion is GI.gi_rep_efficientProverProofErr at SoundnessRepGI.lean:438. Its
  protocol-specific conclusion cannot supply this generic reader. No probability
  complement or order fact was re-proved.

Promotion/readers: PaddedVerifierSpec and these abstract padded-phase readers belong in
this topic helper layer. General prerequisites already carry the earlier Interaction and
InteractiveProofs promotion requests. No frozen-file edit, scope extension, private host,
new Mathlib root, or new simp attribute was introduced.

Validation history and resource evidence:
- RepeatedVerifier01: syntax cascade from reserved capital Π; changed the bound protocol
  name to valid ρ. RepeatedVerifier02: explicit first-mover projection case split was
  needed for the index arithmetic; fixed through if_pos/if_neg on its equality. Both raw
  failures retained. RepeatedVerifier03 passed spec+phase_exec. RepeatedVerifier04 passed
  the complete phase_take extension with0errors/0warnings, actual runtime2.87s,
  maxRSS2,194,358,272. Its slot wait was10:04:53–10:15:32 UTC, normal host contention;
  not a stall or E-RES.
- RepeatedSoundness01 found one local-notation simplifier mismatch. Attempt02 fixed the
  outer block but exposed the inner occurrence's local c alias. Attempt03 normalized that
  local proposition explicitly and passed the full engine with0errors/0warnings, fresh
  olean, runtime2.41s, maxRSS2,172,452,864 bytes. All raw logs and structured results remain.
- The full engine uses explicitly typed probability intermediates and public product/
  equivalence readers; no pathological dependent calc or proof-debug interruption occurred.
- Each check used this sub-agent's own olean tree and shared wrapper/tag. Source files
  remain below1000lines and100characters. The lead owns the final merged sweep, axioms,
  seals, lint, commits and delivery.


### Statistical checkpoint additions: overlap and reuse

The per-declaration records below supplement the earlier complete overlap list. Raw searches
precede implementation, and no private proof was copied.

- StatisticalTransfer.statZK_of_padded_spec directly combines StatZK_iff (Defs.lean:187),
  phaseVerifier_efficient (WrappedVerifier.lean:154), exists_phaseSimulator
  (SimulatorMachine.lean:~305), PaddedProverSpec.statClose_prefix, StatClose.map,
  statClose_average, and statClose_view_endpoints. Nearest earlier complete construction is
  PerfectZKAbort.statZK (Defs.lean:433ff): it retries a fixed input until success, whereas
  this proof threads bounded normalized prefixes. Its machine is reused through the public
  exists_phaseSimulator, and no retry/loop/postprocessing proof is copied. This generic
  padded-prover transfer belongs in this topic helper layer; no frozen-file promotion needed.
- NormalizedStep.normalizePhaseMsgs_viewV publishes the real fixed point originally local
  to the same file's statistical theorem; that theorem now reuses it, with one proof retained.
  It directly uses PhaseView.normalizePhaseMsgs_of_encode and ExecutionBounds.exec_snd_bounded.
- Canonical phaseVerifier_eq/phasePrefix_eq and the endpoint _eq readers are home-definition
  equations, added for literal reader compliance; no foreign equation is re-derived.


## StatisticalRecursion checked continuation

StatisticalRecursion.lean introduces no definition or host. Its sole public theorem
statClose_recursion takes caller-supplied zero and snoc equations for arbitrary real/simulated
sampler families and updates. Shared-prefix averaging replaces the final update at cost
delta; the existing randomized test-set reader transports the induction hypothesis through
the same simulated final update. Public transitivity and Fin.snocEquiv close the successor.
No Nonempty assumption on either coin type is required, because empty coin tables have
explicit inhabitants in the base case.

Nearest relatives: OneWayLemmas.lean:276 statClose_pi handles independent copies of one fixed
sampler comparison; Statistical.lean:59 statClose_chain handles a supplied full-sampler chain.
Neither is a caller-supplied state-dependent snoc recursion theorem, and neither proof was
copied. Directly reused readers are Statistical.lean:44 statClose_average,
Sampling.lean:237 StatClose.abs_uprob_sub_le_prod, Sampling.lean:167 StatClose.trans,
Sampling.lean:179,185 seed-equivalence transports, and Mathlib Fin.snocEquiv/snoc_init_self.
Promotion beside generic StatClose support is requested at a shared-file window.

The first source triggered stack-diagnosed pathological implicit sampler unification and
was interrupted only by exact lead authorization, with the raw source, sample, resource
reading, process chain and authorization preserved. The explicitly typed rewrite passed
check02 with no diagnostics in2.45s, maxRSS2,121,269,248 bytes. It is139lines, maxwidth94,
SHA256 fe7d94d26ba375222245902da6ce0e71c9789d9ee98a9e68e4a063d5ada9591e.
Its precise rewrite patch and large lossless sample ZIP part001 are delivered.

## NormalizedStep pending compiler diagnosis

NormalizedStep is not yet claimed checked. Its stronger zero-verifier API was approved by
the lead and independently reviewed as mathematically/type-consistent by seq-zk-c. The exact
phase-wrapper reader-only instantiation recipe is normalized-step-instantiation.md.

compiler-diagnosis-summary.md and the numbered authorization/process/source/marker records
retain each targeted own-process proof-debugging interruption. All were authorized by the
lead under Seyoon's best-judgment exception, never elapsed-time timeouts or E-RES, and no other
job or slot was changed. Every created native stack sample is delivered losslessly in ZIP
parts with raw SHA256, entry lists and verified extraction. Current work is localizing the
scalar test comparison declaration with robust direct-file IO markers; no false proof claim
or statement weakening is made. All diagnostic IO/trace must be removed before a final clean
source check and intake.

## Checkpoint 2 closed-evidence boundary

compiler-diagnosis-summary.md is the authoritative corrected closed ledger through
NormalizedStep attempt07. It supersedes earlier tentative source-stage descriptions in this
historical report. Eight own exact-process interruptions are recorded: StatisticalRecursion01
and NormalizedStep01–07, all separately lead-authorized proof debugging rather than timeouts
or E-RES. No own Lean is active at this boundary. NormalizedStep remains unverified; the checked
StatisticalPostprocess dependency and completed fixed-point/pointwise markers do not imply
that its full concrete instantiation passed. The next opacity/instance correction awaits the
lead's three-slot cache completion. Complete prerequisite sources and lossless native-sample
ZIP parts are included so all closed raw evidence has its sources and verification tools.


## Final normalization and statistical-prefix extension

NormalizedStep is now clean-checked with no diagnostics. Its final source hash is
07c9fed43664eeaa47b712f02b72f09addbe0ceb8dc134917cd0b33f6754e689
(101lines,maxwidth96;nativecheck10=2.22s). The compiler ledger now explicitly records the
missing ZeroKnowledge.Defs import exposed by attempt08 and corrected before09. Prior
elaboration-stage diagnoses were incomplete because invalid simulate fields in the
signature remained buffered. The corrected exact-source check is retained in full.

StatisticalPrefix is clean-checked with no diagnostics. Its final source hash is
5275167b11df6074d08df53ae24486e94ccb1149eaf5d6541e88ad9fe1727d64
(151lines,maxwidth94;nativecheck02=2.31s). PaddedProverSpec.statClose_step specializes the
zero-verifier comparison at every index and prefix using an explicit coin-length equality,
coin equivalence and public ofFn reader. PaddedProverSpec.statClose_prefix instantiates the
public sampler-recursion bound using the public zero/snoc fold readers. It assumes only
a direct prover-message cap and raw phase closeness at every auxiliary input; S need not
be uniform. Neither proof uses a target theorem or creates a host.

Nearest overlap relatives: StatisticalRecursion's generic caller-supplied family bound,
NormalizedStep's generic zero-verifier bound, PrefixLaws zero/snoc readers,
PaddedProverSpec.original_count, public StatClose.comp_equiv_left/nonneg, and Mathlib
List.ofFn_congr. StatisticalPrefix is their concrete composition, not a duplicate generic
loop or statistical law. Exact searches are statistical-prefix-searches.log.

The lead authorized APFS clones of completed helper oleans into this isolated olean tree.
Eight completed immutable prerequisite source/olean pairs were copied with provenance in
prefix-prerequisite-seed.json. Their sources are reused unchanged; no other owner file was
edited. The lead will perform final source, axioms, seals and sweep checks.

## BoundedMetadata overlap plan

Nearest existing material is ColZKMachine's finite maximizing domain with a bounded
sigma-word, plus the public padFin/ofFn_padFin_of_length codec. The new metadata type
only assembles those standard finite representations into the five actual reduction
fields. It defines no selector, maximizing principle, interpreter or machine. c's Advice
selector will consume the resulting finite nonempty type. The exact packed-size formula
is b's public reductionData_length; it is reused directly, not re-proved.


## Complete checked helper handoff

seq-zk-a proved ten helper modules: Normalization, NormalizationMachine, PhaseView,
Statistical, ExecutionBounds, StatisticalRecursion, NormalizedStep, StatisticalPrefix,
BoundedMetadata and RealPrefixBounds. All final source bytes are in source-snapshots with
owner/status/hash rows. No target or frozen file was edited. The lead alone integrates,
commits, seals, sweeps and delivers the target declarations.

At lead request, NormalizedStep11 exposed normalizePhaseMsgs_viewV without any statistical
premise. The existing comparison calls it; no second normalization proof was added. The
new final source hash is76766e13e0eff35d107c98505f932dcec17cdf20f89c5f423f7e1d64217884b5
(126lines;clean native11=2.50s). This supersedes the earlier101line clean10 source.

BoundedMetadata final03 passed2.38s,0diagnostics. It defines finite nonempty five-field
PhaseMetadata, exact raw data/length readers and exact coverage. An initially redundant
direct Mathlib.Data.Fintype.Sigma import was removed before final03; the final source
imports only ComputationalReduction and requires no new Mathlib root. Source hash
f94e6c8ff89a1674aaed5047e479856ebe3e2a1623e2d2ccdeb46f4ae6f8959b.
Its raw01failure and exact source are retained (product RHS parenthesization and a proof
where simp had already changed reflexive equalities to True);02passed,03removed the
redundant import and added the direct packed-data cover corollary.

RealPrefixBounds final02 passed2.27s,0diagnostics. Its aggregate theorem gives exact j*k
message count, the uniform B cap, and encoding length at most(j*k)*(2*B+2) for every
real prefix j≤q. It reuses the public raw coin-table inverse/block reader and endpoint,
the specification's boundary/reply readers, and ExecutionBounds. No generic word-length
estimate is duplicated. Source hash
1a50f8656f00e280506a67947a16a0583cdcc5fb9242efa3e15a3fc160f390d8.
Its raw01failure is retained; split_ifs generated both first-mover cases as well as the
active/filler cases, so02applied the same bounded/empty branch argument to all four.

The retained FullOwnHelpersAxioms.lean probe checks42public declarations across all ten
owned modules. It passed5.09s with0diagnostics and only propext,Classical.choice,Quot.sound.
It also synthesizes Fintype and Nonempty of PhaseMetadata for arbitrary five natural
bounds. The smaller MetadataAndStatisticsAxioms.lean is a prepared but unused predecessor
probe retained for completeness; the full probe is the executed evidence.

All copied dependencies preserve their owner's exact checked bytes: c StatisticalPostprocess
and final EndpointSampling, b final ComputationalReduction, and lead-completed helper
sources/oleans cloned only after completion authorization. Provenance JSON files record
source hashes/check rows. seq-zk-a ran no lake command and touched no other worker process.
There were no new compiler interruptions after the historical eight own authorized events.


## Checkpoint3 closed-evidence boundary

The lead reports CP3 proof revision04c253e48d9c0ebb73943f39412365cd4d8e02db. The first eight
seq-zk-a helper sources are part of that proof revision. BoundedMetadata and RealPrefixBounds
are fully checked future support sources OUTSIDE CP3, as is b's ComputationalReduction
dependency; all three exact sources are retained under source-snapshots for replay of the
new checks and the full axioms/Fintype probe. Their outside-CP3 status is explicit in the
checkpoint3-closed-files.tsv source_status column. No own process is active at this boundary.
After producing that receipt, every named byte is frozen until the lead confirms copying.

The preceding agent report includes explicitly labeled future BoundedMetadata and
RealPrefixBounds, outside CP3. Its source_status receipt is authoritative for that boundary.
## Scope requests

One explicit request: add the nine-line StatZK_iff reader in frozen
TCSlib/Cryptography/ZeroKnowledge/Defs.lean. Seyoon answered **"Approve this reader addition"**.
The exact request, answer and diff are in evidence/scope-request/. No other frozen file changed.
Seyoon later authorized best judgment on exceptions and messaging workers for shared Mac
resources; that instruction is retained in evidence/coordination/. Shared-slot coordination
with derand, sc-garble and Ladner is recorded there. No other worker's tree or process was
edited, removed or interrupted.

## Promotion and reader requests

At a shared-file window, consider moving the Strategy/BinArith encoding bridge, encoded-prefix
reader and generic exec-prefix readers beside encodeMsgs/exec in Interaction.lean; decoded
canonicalization/lookup beside the BinaryArith word-list hosts; generic repetition-machine
closure facts into a shared encoded-interaction layer; and the arbitrary-rate adaptive bound
into the probability layer. These are promotion requests, not frozen-file edits in this payload.

## Payload and replay

patches/ contains the complete format-patch series at the issue base. COMMITS.tsv includes
all author/committer metadata and the signing column; commits use commit.gpgsign=false.
src/ contains every changed/new repository file. evidence/ includes input packs, tools,
probe/seal/control preparations, raw successful and failed logs, requests, source snapshots,
subagent records and manifests. Its SHA256SUMS covers every evidence file except itself.
The top-level SHA256SUMS covers every delivered file except itself; exact path equality and
hashes are verified before the exchange commit/push. Delivery touches only inbox/fills/seq-zk/.


## Endpoint helper overlap record (verbatim)

# EndpointSampling implementation record

Author: seq-zk-c. Assigned by lead after the checkpoint2 closed-evidence manifest was
sealed. This record and all endpoint-* files are future evidence, outside checkpoint
source e978a28274fdeb545e622ae28747221088352512. All72 files in the sealed manifest remain
byte-for-byte unchanged. The lead owns final integration, commits, frozen seals and delivery.

## Supplied interface and coordination

Read root PrefixFolds/PrefixLaws, b PaddedProverSpec/SimulatorMachine, and a
StatisticalRecursion. Coordinated the joint `(verifier tape, prefix)` domain with a and
b before coding. The lead approved generic tape block equivalences, real prefix
identification by the published padded-phase reader, and the optional joint statistical
endpoint convenience theorem. No sibling or main source was edited or checked in its
foreign tree. There is no target change or added cryptographic premise.

The stable new module is EndpointSampling.lean,269lines/max95columns, SHA256
76827a0f531b095aeccd1460ef56ad13bb13612a861f9e7af82bad9069c1c048.

It publishes:
- coinTableEquiv(hlen:m=q*c) and its block reader, for the real prover tape.
- coinBlocksEquiv(v,q,c,hlen:m=v+q*c) and its verifier-take/phase-block readers.
- statClose_reindex, for supplied endpoint equivalences and pointwise endpoint readers.
- PaddedProverSpec.realPrefix_eq_exec, for j<=q and supplied block equalities.
- PaddedProverSpec.realCoinsEquiv, with domain actual `(rho.withV V).ExecCoins` and codomain
  `V.Coins |x| x (Fin q -> pi.P.Coins |x|)`, plus tape/block readers.
- PaddedProverSpec.viewV_eq_realPrefix, the actual encoded real-view endpoint.
- simulate_eq_simPrefix, the typed simulator endpoint from the published raw split reader.
- statClose_view_endpoints, consuming joint real/simPrefix closeness and returning actual
  encoded repeated view versus SQ.simulate with exactly the same error. Its only extra
  readers are p=the original mover count, SQ coinLen=v+q*S.coinLen, and the supplied SQ
  split-tape endpoint; the lead derives them directly from existing readers.

## Search, overlap, reuse, and promotion

Raw exact searches are in endpoint-sampling-searches.log.

- coinTableEquiv is the canonical FunFamily.blocks composed with a finite-length cast.
  The nearest existing assemblies are RepeatedSoundness.accept_le (verifier blocks) and
  GI.gniTapes (graph-specific sampler blocks). Neither exports the required general
  length-cast table equivalence. The block proof directly reuses FunFamily.ofFn_blocks
  and List.ofFn_congr, rather than duplicating the GI.coinSlice_blocksEquiv entrywise proof.
  Promotion request: a named length-cast block equivalence/reader belongs in
  Asymptotic/Adversary.lean if accepted; it is frozen here.
- coinBlocksEquiv directly reuses splitCoins and ofFn_splitCoins_fst/snd from
  Asymptotic/CollectionsHelpers.lean:145ff, then FunFamily.blocks/ofFn_blocks. No sum split,
  take/drop proof, block equivalence, or entrywise window proof was reproduced.
  Its distinct combined codomain is one verifier tape and a finite table of phase tapes.
  Promotion request: combined uniform-tape layout reader in the shared sampling layer.
- statClose_reindex is only published comp_equiv_left/right followed by supplied pointwise
  function equalities. Searches found no combined endpoint-reader interface. It does not
  reproduce probability invariance or a statistical switch. Nearest public declarations
  are StatClose.comp_equiv_left/right (Sampling.lean:179/185). Promotion request to Sampling.
- realPrefix_eq_exec directly composes realPrefix_zero/succ and PaddedProverSpec.padded_phase.
  Its induction is on the number of phase updates, not a duplicated execution/phase proof.
  Nearest real endpoint is b's padded_phase; its single-phase conclusion does not identify
  the finite fold with all phases. The lemma belongs in this topic helper layer.
- realCoinsEquiv and its readers are the typed composition of coinTableEquiv,
  Protocol.withV_vCoinsEquiv/ofFn and product commutation. viewV_eq_realPrefix directly
  combines that interface with Protocol.viewV_withV and the real fold reader.
- simulate_eq_simPrefix directly reuses root simPrefix_eq_phasePrefix and the combined
  block readers; its raw endpoint is supplied by b's exists_phaseSimulator. It contains
  no second simulator recursion or reconstruction of the simulator machine.
- statClose_view_endpoints directly maps joint prefixes to canonical View encoding and
  reuses statClose_reindex plus both endpoint readers. It adds no per-phase statistical
  argument and preserves the error without a triangle/normalization loss.

No frozen source, new simp attribute, foreign-definition unfolding tactic, Lake command,
new iteration host, witness bound, target assumption, or new direct Mathlib root.
CollectionsHelpers was already inside the issued cached TCSlib closure.

## Isolated prerequisites and validation

The lead approved source-copying exact checkpoint helper sources plus b's final canonical
WrappedVerifier/SimulatorMachine public-reader additions, followed by native own checks.
endpoint-prerequisite-sources.json records all source provenance and SHA256s. Own helper
sources were retained. B's two final hashes were verified before copying. No sibling
oleans were copied.

The initial prerequisite Normalization check passed. NormalizationMachine then failed
because the initial209-module own bootstrap lacked ThreeColoring/Machines.olean. This
complete missing-import attempt is preserved, with no source edit to the prerequisite.
Using the lead's explicit existing authorization, APFS-cloned28 missing BASELINE oleans
from root's completed working tree; all source bytes were verified against both own/root
sources and exact checkpoint e978a28274fdeb545e622ae28747221088352512, all olean bytes hashed,
and no existing artifact overwritten. All SequentialZK modules were excluded from seeding.
endpoint-root-baseline-seed.json records each source/artifact hash and path.

Native own-tree checks then passed, one module at a time, in this order:
NormalizationMachine (retry02), PhaseView, WrappedVerifier, RealPhases, PaddedProverSpec,
PrefixFolds, SimulatorMachine, PrefixLaws. Each raw attempt and structured result is retained.

EndpointSampling check01 passed with0errors/0warnings, a fresh own olean,2.45s actual
runtime and maximum resident set size2,236,170,240bytes. The exact attempt source is saved.
Every Lean invocation used LEAN_SLOT_TAG=seq-zk-c, the shared lean-slot wrapper,
/usr/bin/time -l, scripts/lean_check_tree.sh and the separate seq-zk-c olean tree. There was
no interruption, timeout, sampling, or resource exception in this task.

The stable checked source/hash/API were sent to lead and a. No own Lean process remains.

Final reader-compliance amendment: at the lead's request, added full canonical
coinTableEquiv_eq, coinBlocksEquiv_eq, and realCoinsEquiv_eq, each rfl in its home module.
No existing body/reader changed. Check02 passed0diagnostics,2.66s actual runtime,
maxRSS2,237,087,744bytes. Final source/hash sent to lead and a; source remains stable.

## Uniform advice selector and opaque statistical post-processing

At the lead's request, inspected the published NUPPT closure/advice APIs and nearest
ThreeColoring finite-selector/hybrid proofs. The initial finite-kernel alternative is
unnecessary: maximizing the finitely many real suprema over arbitrary witnesses gives a
selector independent of the eventual negligible bound. The lead approved that route.
The complete design and remaining concrete obligations are recorded in
computational-advice-design.md; exact raw API searches are in advice-postprocess-searches.log.

Advice.lean introduces only exists_uniform_bound_selector: finite nonempty metadata,
arbitrary witness type, and a common nonnegative upper bound yield a metadata value whose
nonnegative uniform witness bounds also bound every metadata/witness pair. The proof
directly reuses Mathlib Finite.exists_max, le_csSup, and csSup_le. The nearest existing
ColZK.exists_hidingView_bound (ColZKMachine.lean:323) selects among finite colour/advice
triples and has a specialized commitment conclusion; it does not supply the arbitrary
witness-domain implication. No proof was copied. Promotion request: place this generic
bounded-family selector in a future shared order/probability helper. New precise imports
Mathlib.Data.Fintype.Lattice and Mathlib.Data.Real.Archimedean were approved by the lead;
both pinned olean files were already cached, and the lead owns required roots/pin/cache
updates. This agent ran no Lake command. Check01 passed with0errors/0warnings, 1.69s actual
runtime and maxRSS1,466,220,544 bytes. The slot wait from10:55:20 to10:57:10 UTC was normal
host contention, not an elapsed-time diagnosis, interruption, or resource shortage.

NormalizedStep's concrete elaboration remained slow inside the raw test bound despite
explicit public-reader arguments. The lead and a requested an opaque generic helper;
StatisticalPostprocess.lean introduces only statClose_map_fst. Its pair-indexed fixed-point
hypothesis matches a's existing proof directly. The ignored product factor is explicitly
Nonempty, necessary for the uniform-probability projection law (and automatically true
for verifier coin function spaces even with zero bits). It directly reuses StatClose.map,
statClose_iff, OneWay.uprob_congr and uprob_fst. Searches found no combined public map/fst
law. Nearest laws are those four imported public readers; no statistical switch, uniform
product, or event congruence proof was duplicated. Promotion request: this general law
belongs in Asymptotic/Sampling.lean if accepted; that file is frozen, so it stays in the
approved topic helper. Check01 passed with0errors/0warnings, 2.19s actual runtime and
maxRSS2,110,701,568 bytes. Source/API/hash sent to a and lead for independent copying and
checking. No concrete protocol or NUPPT appears in the helper, and no NormalizedStep edit,
check, sample, or interruption was performed by this agent.

Both new source files are stable. Every own Lean-running command used the shared wrapper,
seq-zk-c tag, one module, and own olean tree. Full raw checks, source hashes, searches,
structured attempt results, and refreshed source/diagnostic audits accompany this record.
No new simp attribute, frozen-file edit, scope extension, admission, or target change.

The computational suffix/hybrid sections above are labeled future evidence; they are not
part of checkpoint3src at the stated proof revision.

## Comment-final delivery boundary

The delivered proof tip is5a80d36a5a4da1c2906b747dab59251fdd03836a. The fourth commit adds
only16stage-comment lines across the owned file, SimulatorMachine and StatisticalPrefix.
A token roundtrip removes those lines and exactly restores the prior sources; statements
and proof tactics are unchanged. The prior source audit found seven long new proofs whose
sketches were present but internal comments missing; all seven were corrected before delivery.
Lead native rechecks passed for both changed helpers, StatisticalTransfer and the owned file.
The exact comment-final axiom census, style diff, width check, canonical seal and four-commit
independent replay are under checkpoint3-doc paths; earlier checkpoint3 logs remain historical.

Subagent checkpoint3receipts use04c253... as their original source boundary. The later
post-cp3-audit and simulator-doc-comments receipts supply the exact checked comment overlays.
Every receipt remains byte-identical. Additional closed computational-phase-bound and
withV-reader-fix receipts and snapshots postdate that boundary and are explicitly future
support, outside this checkpoint's30src files. ComputationalTransfer.lean under drafts is
uncompiled future final assembly, reviewed read-only with exact source hashes; it is not a
proved source in this checkpoint.

## Historical receipt resolution

Closed receipt files are kept immutable. Nine referenced metadata paths later acquired newer
versions after copy acknowledgment. Their original exact bytes are also delivered: five a
metadata files recovered from our published CP2Git payload, two c append-only result prefixes
verified by original hashes, and two c audit files deterministically regenerated by the
unchanged original script from15authenticated source snapshots and exactly48historical logs.
Both regenerated files match their original receipt SHA256exactly. The current171-file c
receipt stayed unchanged throughout. All commands/input hashes/stdout/provenance are retained.
receipt-resolution.tsv resolves every historical row to exact current or archived bytes;
no old metadata or raw diagnostic has been dropped. Primary SHA256SUMS manifests cover all
versions and the resolution map.


### Preserved implementation record: subagents/seq-zk-a/report.md

# seq-zk-a final helper report

Agent `/root/zk_route`, tag `seq-zk-a`, branch `fill/seq-zk-a`, issue base
107f1e8c218733eac12d6b9bee6fece441271317. Worktree:
`/Users/seyoonr/.codex/worktrees/seq-zk-a/tcslib-exchange`.
Own olean tree: `.lake/seq-zk-a-oleans`, seeded by the lead from completed base modules.
`.lake/packages` is a symlink to the lead's exact-pin packages and read-only to this agent.
No commits, Lake commands, frozen edits, or SequentialZK.lean edits were made by this agent.

## Checked source

- Normalization.lean: 98 lines, maximum width 94; encoding bridge, bounded slot normalizer,
  exact count, per-message length bound, canonical bounded-list fixed point, encoded-size bound.
- NormalizationMachine.lean: 97 lines, maximum width 95; polynomial-time canonical reencoding,
  total decoded lookup, and encoded bounded-slot normalization for arbitrary polynomial-time
  raw input and unary-computable slot count and bit cap.
- PhaseView.lean: 168 lines, maximum width 95; canonical view metadata/tape/encoding validator,
  fixed-point and malformed-view fallback, bounded normalized messages and polynomial-time
  validator/encoded-normalizer theorems.

All three compile without final diagnostics or admissions, and add no simp attributes.
Source hashes are recorded in final-width-and-hashes.log. The first two source files were
held byte-stable after checking so seq-zk-b could reuse them with recorded provenance.

## Overlap and reuse

### Normalization.lean

- encodeMsgs_eq_encWords exactly matches the local `have henc` inside
  SecureComputation/Yao.lean:352. That provider is outside the supplied closure; this helper
  derives the general statement from public nil/cons readers of both encodings. The same
  representation occurs in ThreeColoring/Machines.lean:912 encodeMsgs_eq_flatMap.
  Promotion request: a general Strategy/BinArith encoding bridge belongs beside
  Strategy.encodeMsgs in ZeroKnowledge/Interaction.lean during a shared-file window.
- normalizeMsgs and normalizeMsgs_eq publish a new bounded-slot operation. No existing
  normalization with this shape was found in TCSlib or Mathlib searches.
- length_normalizeMsgs specializes List.length_map and List.length_range, directly reused.
- length_le_of_mem_normalizeMsgs uses List.length_take and Nat.min_le_left; this is the same
  arithmetic as List.length_take_le, specialized to the new operation.
- normalizeMsgs_encodeMsgs reuses BinArith.decWords_encWords (Words.lean:116) and
  List.take_of_length_le. No decoder or list host is copied.
- length_encodeMsgs_normalizeMsgs_le directly specializes public Words.lean:81
  length_encWords_le to the new invariants. CommitmentLemmas.lean:241 length_encodeMsgs_le
  offers the same generic encoded-size bound but introduces larger cryptographic imports.

### NormalizationMachine.lean

- polyTimeComputable_encWords_decWords specializes Words.lean:221 polyTimeComputable_mapW
  to the identity payload and uses mapW_pairEncode at line 208. No host is copied.
- polyTimeComputable_decWords_getD composes canonicalization with Loops.lean:391
  polyTimeComputable_getW and its reader getW_pairEncode at line 375.
- polyTimeComputable_encode_normalizeMsgs uses these lookups, EncodingMachines.lean:459
  truncate_poly, and ThreeColoring/Machines.lean:159 polyTimeComputable_flatMap_range. The
  published counted-emission argument is reused. Its import is within the supplied closure
  and was confirmed with the lead. No extra size premise or new private host is introduced.
- Promotion request: the generic canonicalization and total decoded-lookup lemmas belong
  beside the BinaryArith word-list hosts at a future shared-file window.

### PhaseView.lean

- phaseViewPayload and its eq reader are a new canonical-view validator; no matching
  validator was found. normalizePhaseMsgs and its eq reader compose it with normalizeMsgs.
- phaseViewPayload_of_encode specializes Interaction.lean:302 View.encode_mk, public pair
  projection equations, and Words.lean:116 decWords_encWords. All are directly reused.
- phaseViewPayload_of_ne is the new validator's failed-branch equation, proved by if_neg.
- normalizePhaseMsgs_of_encode directly reuses Normalization.lean:76
  normalizeMsgs_encodeMsgs after the canonical payload reader.
- length_normalizePhaseMsgs, length_le_of_mem_normalizePhaseMsgs, and
  length_encodeMsgs_normalizePhaseMsgs_le directly reuse Normalization.lean:60,66,89 after
  the new definition reader. They are its three phase-view specializations.
- normalizePhaseMsgs_of_ne specializes the normalized-empty-payload formula; its list
  calculation directly reuses core getD/getElem?/take/map-constant/range equations.
- polyTimeComputable_phaseViewPayload composes the existing canonical reencoder with
  Loops.lean:426 polyTimeComputable_eqW and PolyTimePairing.lean:290
  polyTimeComputable_ite. It introduces no host or machine construction.
- polyTimeComputable_encode_normalizePhaseMsgs directly reuses
  NormalizationMachine.lean:72 after validation. No additional promotion is requested for
  these phase-specific operations.

Searches and closest relatives are recorded in searches.md, searches.log,
normalization-machine-searches.log, map-identity-search.log, phase-view-searches.log and
phase-view-ite-search.log. Searches consulted the lead's Mathlib source read-only.

## Scope and mathematical assessment

The agent discovered the missing StatZK reader and supplied scope-StatZK-iff.patch without
applying it. The lead reports Seyoon approved the addition and the lead applied it. This
agent changed no frozen file. route-assessment.md records the independent mathematical
review of the ZK/StatZK route, auxiliary bounds and edge cases. No mathematical counterexample
was found; that assessment itself is not a checked composition proof.

## Checks and evidence

Every check used LEAN_SLOT_TAG=seq-zk-a, the assigned TCSLIB_OLEANS, the issued host wrapper,
/usr/bin/time -l, and scripts/lean_check_tree.sh for one module. All raw attempts are retained.

- Normalization passed attempt 01: 0 errors, 0 warnings; RSS 1,564,000,256 bytes.
- NormalizationMachine attempt 01 had one map-identity proof error and two unused simp
  arguments. Core List.map_id' fixed the lambda identity; attempt 02 passed with 0 errors,
  0 warnings; RSS 2,213,593,088 bytes.
- PhaseView attempt 01 had one missing true-conditional simplification and one unused simp
  argument. Public if_true completed the payload proof; attempt 02 passed with 0 errors,
  0 warnings; RSS 2,224,095,232 bytes.

check-summary.json counts both error: and error(...) diagnostic forms. slots.log records
all this tag's acquisitions/releases and their timestamps; it supplies the module start/end
for the first normalization raw log, which contains only the timing report. Later raw logs
include START/END timestamps, including any normal slot wait. Axiom/seal/campaign-lint checks
are the lead's final merged-branch responsibility. No probe/check logs have been omitted.

## Statistical helper continuation

Statistical.lean adds the sole missing sampler-level shared-prefix averaging lemma
`statClose_average`. It directly reuses statClose_iff (Asymptotic/Sampling.lean:133),
StatClose.abs_uprob_sub_le (Sampling.lean:138), abs_uexp_sub_le (Sampling.lean:210), and
uprob_prod (Foundations/Probability.lean:153). This is a new packaging of those published
interfaces, not a copied averaging proof. Promotion beside StatClose in Sampling.lean is
requested at a future shared-file window.

The lead approved an explicit nonnegative error premise to cover an empty shared seed space.
statistical-api.md records the exact counterexample to the draft interface without that
premise, and explains why it is not a frozen-target flaw. Actual phase coin spaces are
nonempty and one-phase closeness also supplies nonnegativity for witnessed inputs.

No randomized postprocessing wrapper was added: StatClose.abs_uprob_sub_le_prod already
provides the exact test-set bound, and statistical-api.md gives its two-line consumer.
The new file imports only Asymptotic.Sampling, within the supplied closure; no new host,
cache root, frozen edit or simp attribute is introduced.

Statistical.lean passed wrapped check 01 with no diagnostics; peak RSS 2,110,177,280 bytes,
3.22 seconds compiler wall time, after a normal shared-slot wait. The raw log includes
START/END timestamps. statistical-searches.log retains the searches before implementation.
The final source width/hash ledger, check summary, and own-tag slot log are updated.

## Finite-chain and actual-kernel outline continuation

After fresh public TCSlib and Mathlib searches, Statistical.lean now also publishes
statClose_chain for an arbitrary same-seed family f : Nat -> Omega -> O. The proof only
uses public StatClose.refl (Sampling.lean:153) and StatClose.trans (Sampling.lean:167), with
natural-cast arithmetic. It has no sign premise on delta, including q=0. Nearest relatives
are Probability.lean:218 abs_sub_le_sum_hybrids (a scalar probability-gap theorem) and
OneWayLemmas.lean:276 statClose_pi (independent products of a fixed sampler comparison).
Neither is an arbitrary-family StatClose chain; neither argument is copied. Promotion of
this generic chain lemma beside StatClose is requested at a shared-file window.

Statistical check02 passes with no diagnostics; RSS 2,114,224,128 bytes and 3.67 seconds
compiler wall time. All check summaries, own slot records, and final source hashes are
updated. The earlier Statistical hash is superseded by final-width-and-hashes.log.

hybrid-outline.md gives a precise semantic proof plan for the actual one-phase kernels,
using b's approved phaseAux/phaseVerifier and phasePrefix simulator-fold readers. It includes
normalization's real fixed point, common paired real/simulator coin tables, shared-prefix
averaging, existing randomized suffix data processing, full chain, and endpoint coin-law
transports. It explicitly records remaining execution-reader obligations rather than
assuming them. The outline has been coordinated with seq-zk-b; it proposes no private host
or frozen edit and weakens no target. Raw extra API searches are retained in
statistical-chain-searches.log and hybrid-execution-searches.log.

## ExecutionBounds continuation

ExecutionBounds.lean is 88 lines, maximum width 94, with no admissions or simp attributes.
It imports only stable Normalization.lean; the previous four source hashes were asserted
unchanged when this report was finalized. Public searches found no existing generic message
length bound for Cryptography.exec.

New declarations and overlap:

- exec_snd_bounded derives a bound on every verifier-received message from a fixed prover
  tape's uniform next-message bound. It uses only Interaction.lean's exec_zero and exec_succ
  readers (lines 262 and 266 in the base). Related
  Games/Protocols.lean:316 execT_trace bounds concern a different oracle protocol and only message
  counts; they do not provide this statement. No private argument was copied.
- exec_snd_slice_bounded directly specializes exec_snd_bounded through the public core
  List.mem_of_mem_take and List.mem_of_mem_drop readers. It adds no list-membership lemma.
- length_encodeMsgs_exec_snd_le applies Words.lean:81 length_encWords_le through the checked
  encodeMsgs_eq_encWords bridge and exec_snd_bounded. It is execution-specific. No duplicate
  generic encoded-history bound was added; the nearest existing generic
  CommitmentLemmas.lean:241 length_encodeMsgs_le is subsumed by the Words theorem reused.

Promotion request: generic execution-message bounds belong beside the execution readers in
Interaction.lean at a future shared-file window. No frozen-file edit was made or needed.

ExecutionBounds check01 passed with one unused simp argument; the argument was removed in
its single proof block. Check02 passes with no diagnostics, RSS 1,560,723,456 bytes and
1.77 seconds compiler wall time. Both raw attempts, preimplementation searches, width/hash
ledger, diagnostic summary and own-tag slots are retained. No Lake command ran. The hybrid
outline now marks the execution-message-bound obligation resolved by this checked helper;
the separate cheating-verifier padded-phase endpoint reader remains a lead obligation.

## StatisticalRecursion checked continuation

StatisticalRecursion.lean introduces no definition or host. Its sole public theorem
statClose_recursion takes caller-supplied zero and snoc equations for arbitrary real/simulated
sampler families and updates. Shared-prefix averaging replaces the final update at cost
delta; the existing randomized test-set reader transports the induction hypothesis through
the same simulated final update. Public transitivity and Fin.snocEquiv close the successor.
No Nonempty assumption on either coin type is required, because empty coin tables have
explicit inhabitants in the base case.

Nearest relatives: OneWayLemmas.lean:276 statClose_pi handles independent copies of one fixed
sampler comparison; Statistical.lean:59 statClose_chain handles a supplied full-sampler chain.
Neither is a caller-supplied state-dependent snoc recursion theorem, and neither proof was
copied. Directly reused readers are Statistical.lean:44 statClose_average,
Sampling.lean:237 StatClose.abs_uprob_sub_le_prod, Sampling.lean:167 StatClose.trans,
Sampling.lean:179,185 seed-equivalence transports, and Mathlib Fin.snocEquiv/snoc_init_self.
Promotion beside generic StatClose support is requested at a shared-file window.

The first source triggered stack-diagnosed pathological implicit sampler unification and
was interrupted only by exact lead authorization, with the raw source, sample, resource
reading, process chain and authorization preserved. The explicitly typed rewrite passed
check02 with no diagnostics in2.45s, maxRSS2,121,269,248 bytes. It is139lines, maxwidth94,
SHA256 fe7d94d26ba375222245902da6ce0e71c9789d9ee98a9e68e4a063d5ada9591e.
Its precise rewrite patch and large lossless sample ZIP part001 are delivered.

## NormalizedStep pending compiler diagnosis

NormalizedStep is not yet claimed checked. Its stronger zero-verifier API was approved by
the lead and independently reviewed as mathematically/type-consistent by seq-zk-c. The exact
phase-wrapper reader-only instantiation recipe is normalized-step-instantiation.md.

compiler-diagnosis-summary.md and the numbered authorization/process/source/marker records
retain each targeted own-process proof-debugging interruption. All were authorized by the
lead under Seyoon's best-judgment exception, never elapsed-time timeouts or E-RES, and no other
job or slot was changed. Every created native stack sample is delivered losslessly in ZIP
parts with raw SHA256, entry lists and verified extraction. Current work is localizing the
scalar test comparison declaration with robust direct-file IO markers; no false proof claim
or statement weakening is made. All diagnostic IO/trace must be removed before a final clean
source check and intake.

## Checkpoint 2 closed-evidence boundary

compiler-diagnosis-summary.md is the authoritative corrected closed ledger through
NormalizedStep attempt07. It supersedes earlier tentative source-stage descriptions in this
historical report. Eight own exact-process interruptions are recorded: StatisticalRecursion01
and NormalizedStep01–07, all separately lead-authorized proof debugging rather than timeouts
or E-RES. No own Lean is active at this boundary. NormalizedStep remains unverified; the checked
StatisticalPostprocess dependency and completed fixed-point/pointwise markers do not imply
that its full concrete instantiation passed. The next opacity/instance correction awaits the
lead's three-slot cache completion. Complete prerequisite sources and lossless native-sample
ZIP parts are included so all closed raw evidence has its sources and verification tools.


## Final normalization and statistical-prefix extension

NormalizedStep is now clean-checked with no diagnostics. Its final source hash is
07c9fed43664eeaa47b712f02b72f09addbe0ceb8dc134917cd0b33f6754e689
(101lines,maxwidth96;nativecheck10=2.22s). The compiler ledger now explicitly records the
missing ZeroKnowledge.Defs import exposed by attempt08 and corrected before09. Prior
elaboration-stage diagnoses were incomplete because invalid simulate fields in the
signature remained buffered. The corrected exact-source check is retained in full.

StatisticalPrefix is clean-checked with no diagnostics. Its final source hash is
5275167b11df6074d08df53ae24486e94ccb1149eaf5d6541e88ad9fe1727d64
(151lines,maxwidth94;nativecheck02=2.31s). PaddedProverSpec.statClose_step specializes the
zero-verifier comparison at every index and prefix using an explicit coin-length equality,
coin equivalence and public ofFn reader. PaddedProverSpec.statClose_prefix instantiates the
public sampler-recursion bound using the public zero/snoc fold readers. It assumes only
a direct prover-message cap and raw phase closeness at every auxiliary input; S need not
be uniform. Neither proof uses a target theorem or creates a host.

Nearest overlap relatives: StatisticalRecursion's generic caller-supplied family bound,
NormalizedStep's generic zero-verifier bound, PrefixLaws zero/snoc readers,
PaddedProverSpec.original_count, public StatClose.comp_equiv_left/nonneg, and Mathlib
List.ofFn_congr. StatisticalPrefix is their concrete composition, not a duplicate generic
loop or statistical law. Exact searches are statistical-prefix-searches.log.

The lead authorized APFS clones of completed helper oleans into this isolated olean tree.
Eight completed immutable prerequisite source/olean pairs were copied with provenance in
prefix-prerequisite-seed.json. Their sources are reused unchanged; no other owner file was
edited. The lead will perform final source, axioms, seals and sweep checks.

## BoundedMetadata overlap plan

Nearest existing material is ColZKMachine's finite maximizing domain with a bounded
sigma-word, plus the public padFin/ofFn_padFin_of_length codec. The new metadata type
only assembles those standard finite representations into the five actual reduction
fields. It defines no selector, maximizing principle, interpreter or machine. c's Advice
selector will consume the resulting finite nonempty type. The exact packed-size formula
is b's public reductionData_length; it is reused directly, not re-proved.


## Complete checked helper handoff

seq-zk-a proved ten helper modules: Normalization, NormalizationMachine, PhaseView,
Statistical, ExecutionBounds, StatisticalRecursion, NormalizedStep, StatisticalPrefix,
BoundedMetadata and RealPrefixBounds. All final source bytes are in source-snapshots with
owner/status/hash rows. No target or frozen file was edited. The lead alone integrates,
commits, seals, sweeps and delivers the target declarations.

At lead request, NormalizedStep11 exposed normalizePhaseMsgs_viewV without any statistical
premise. The existing comparison calls it; no second normalization proof was added. The
new final source hash is76766e13e0eff35d107c98505f932dcec17cdf20f89c5f423f7e1d64217884b5
(126lines;clean native11=2.50s). This supersedes the earlier101line clean10 source.

BoundedMetadata final03 passed2.38s,0diagnostics. It defines finite nonempty five-field
PhaseMetadata, exact raw data/length readers and exact coverage. An initially redundant
direct Mathlib.Data.Fintype.Sigma import was removed before final03; the final source
imports only ComputationalReduction and requires no new Mathlib root. Source hash
f94e6c8ff89a1674aaed5047e479856ebe3e2a1623e2d2ccdeb46f4ae6f8959b.
Its raw01failure and exact source are retained (product RHS parenthesization and a proof
where simp had already changed reflexive equalities to True);02passed,03removed the
redundant import and added the direct packed-data cover corollary.

RealPrefixBounds final02 passed2.27s,0diagnostics. Its aggregate theorem gives exact j*k
message count, the uniform B cap, and encoding length at most(j*k)*(2*B+2) for every
real prefix j≤q. It reuses the public raw coin-table inverse/block reader and endpoint,
the specification's boundary/reply readers, and ExecutionBounds. No generic word-length
estimate is duplicated. Source hash
1a50f8656f00e280506a67947a16a0583cdcc5fb9242efa3e15a3fc160f390d8.
Its raw01failure is retained; split_ifs generated both first-mover cases as well as the
active/filler cases, so02applied the same bounded/empty branch argument to all four.

The retained FullOwnHelpersAxioms.lean probe checks42public declarations across all ten
owned modules. It passed5.09s with0diagnostics and only propext,Classical.choice,Quot.sound.
It also synthesizes Fintype and Nonempty of PhaseMetadata for arbitrary five natural
bounds. The smaller MetadataAndStatisticsAxioms.lean is a prepared but unused predecessor
probe retained for completeness; the full probe is the executed evidence.

All copied dependencies preserve their owner's exact checked bytes: c StatisticalPostprocess
and final EndpointSampling, b final ComputationalReduction, and lead-completed helper
sources/oleans cloned only after completion authorization. Provenance JSON files record
source hashes/check rows. seq-zk-a ran no lake command and touched no other worker process.
There were no new compiler interruptions after the historical eight own authorized events.


## Checkpoint3 closed-evidence boundary

The lead reports CP3 proof revision04c253e48d9c0ebb73943f39412365cd4d8e02db. The first eight
seq-zk-a helper sources are part of that proof revision. BoundedMetadata and RealPrefixBounds
are fully checked future support sources OUTSIDE CP3, as is b's ComputationalReduction
dependency; all three exact sources are retained under source-snapshots for replay of the
new checks and the full axioms/Fintype probe. Their outside-CP3 status is explicit in the
checkpoint3-closed-files.tsv source_status column. No own process is active at this boundary.
After producing that receipt, every named byte is frozen until the lead confirms copying.


### Preserved implementation record: subagents/seq-zk-c/computational-hybrid-record.md

# Computational helper record (future work after checkpoint3)

Author: seq-zk-c. The lead owns main, frozen files, final merge/checks/axioms/seals,
commits and delivery. This record concerns only c-owned helper modules and isolated native
checks. Checkpoint3 source is04c253e48d9c0ebb73943f39412365cd4d8e02db. The first10 c helpers
match that source exactly; the five helpers below are future checked source outside it.
checked-source-snapshots.json and its exact15 snapshots record this distinction.

## Checked contributions and architecture

HybridRecursion.lean:90lines, SHA5277132bb0013c9e290f17272947624e6fd33f17fb9029608d9821affe1e92da.
The public hybrid_recursion_gap_le uses arbitrary state and continuation potential, only
finite nonempty real coin type A, supplied initial/snoc family readers, and conditional
potential drift<=epsilon at every actual prefix. It concludes end-to-end difference
<=q*epsilon. It directly reuses the existing telescope, snoc equivalence, product averaging,
and abs_uexp_sub_le. No finite state/witness bound, new iteration host or new telescope.

SuffixLaws.lean:122lines, SHA4415c221a7d3273f02c22572a20f7033071a504364cb0b5dc855c35e281f3971.
phaseStep_eq_simStep reads a supplied typed block; phaseSuffix_front separates the first
update of b's existing suffix; phaseSuffix_congr_blocks depends only on its own range;
phaseSuffix_update_before ignores an overwritten earlier table coordinate. There is no
new suffix machine or duplicate execution-phase induction. This module owns no definitions.

ComputationalAdvice.lean:74lines, SHAf7a61a8277300e179d2df45c2be4261c90429d8ad7142583ef75e967ad26cffc.
exists_uniform_negligible_bound takes finite nonempty A(n), arbitrary witnesses W,
gap<=1, a validity predicate, and one negligible bound for every selected metadata function.
It chooses metadata before epsilon by the checked Advice selector and concludes one
negligible epsilon uniformly bounds every valid gap by abs(epsilon(n)). Invalid gaps are
zero only inside the proof. No machine decides validity or witness membership. No
nonnegative-gap premise, witness encoding, witness maximum attainment, or bound on W.
Old Advice source is unchanged.

ContinuationProbability.lean:320lines, SHAa5922afe075adffb6349ba1801857125ac76ec158d4bca3faa8fc5289ee03d32.
- acceptProb_prod, acceptProb_update_tuple, acceptProb_postprocess_fst expose exact opaque
  product/update/unused-factor acceptance laws from published probability readers.
- continuationProb(+_eq) is the existing suffix acceptance potential, sampling a full
  typed table of independent S tapes and using only the suffix range.
- continuationProb_bellman uses the published acceptProb_update to reseed the current
  table entry, the front-step reader to consume it, and update_before to remove it from
  all later phases. It is exactly a fresh current simulator coin and independent suffix.
- continuationProb_real directly uses a's normalizePhaseMsgs_viewV fixed point with the
  supplied padded-prover original message count and caller's uniform prover bound. It
  removes the wrapper's zero verifier tape by opaque public averaging/projection laws.
- continuationProb_sim is the matching raw S call identity from the Bellman law.
- phaseGap(+_eq) is the SINGLE shared local raw original-view/S gap through b's
  phaseContinuation, with coin product (Fin Q -> S.Coins) x Dcoins. b's
  ComputationalPhaseBound consumes this public definition/reader; no duplicate gap.
- phaseGap_eq_drift states its exact absolute potential drift under the real next phase.
Final source has the required sim proof sketch and major-step comments. Only docs changed
between passing03 and passing04; no statements, definitions or tactics changed.

ComputationalHybrid.lean:197lines, SHA07e9f3beeaca0c2d2c4d5aa4e166cda4833412ad6b9bf5b5aba62aa888fa9bb1.
prefix_distAdv_le assumes the shared phaseGap bound for each ACTUAL realPrefix before q,
plus d, numeric p count, nonnegative epsilon and honest-message bound. It concludes the
canonical real/simulated prefix view advantage<=Q(|x|)*epsilon at fixed verifier tape.
The real/sim endpoint identities and generic potential theorem do all the work.
prefix_distAdv_joint_le averages verifier tapes. distAdv_reindex directly uses public
acceptProb_comp_equiv and supplied readers. distAdv_view_endpoints equates actual encoded
repeated-view/SQ advantage with the joint typed prefix advantage, reusing stable Endpoint.
No metadata validity, finite witnesses, weakened target or extra cryptographic assumption.
The q=0 case is included by the generic telescope; no Fin0 index is fabricated.

## Coordination and source provenance

The lead approved every new helper/API before coding. c alone edited these files. a owns
NormalizedStep and RealPrefixBounds; b owns SuffixMachine, ComputationalReduction,
ReductionAdvantage and ComputationalPhaseBound; root owns main and transfers. No helper
ownership overlap or foreign-tree edit/check occurred. In particular, a supplies ALL real
normalization and prefix-size proofs, b supplies ALL machine/advice construction and
NUPPT reduction-coin transport, and c does not duplicate them.

Only stable checked source bytes were copied from b/a, then compiled in c's own tree.
Hybrid prerequisite source manifests record exact hashes. A source-copy assertion caught
b's comment-only update from0095... to32d8... before copying; c waited for b's successful
final native check, then copied32d8... unchanged. This was provenance checking, not a proof
failure. SuffixMachine, ComputationalReduction, ExecutionBounds and a's corrected
NormalizedStep all passed native own-tree prerequisite checks. No sibling olean was used.

## Search, overlap, reuse, and promotion

Raw searches are in hybrid-searches.log; earlier advice/endpoint searches remain complete.

Nearest generic hybrid: Foundations/Probability.abs_sub_le_sum_hybrids. HybridRecursion
USES it directly; only conditional-prefix averaging and the snoc reader are new. Nearest
specialized hybrid is ColSimLemmas.exists_hybRed_ge (ThreeColoring/SimulatorLemmas), whose
protocol-specific coordinate/prefix proof does not supply the conditional state-potential
contract. Promotion request: generic conditional-family hybrid in shared probability if
accepted; frozen modules were not edited.

Suffix front/block readers are consequences of b's published phaseSuffix_succ/zero and
phaseStep_eq. None existed in the searched closure. The finite-table update proof uses
canonical FunFamily.ofFn_blocks plus Equiv.apply_symm_apply, not an entrywise copy of
GI.coinSlice_blocksEquiv. This same canonical specialization also appears as a local
reader in RepeatedSoundness; it is disclosed and directly reuses the public window law.
No independent block/window arithmetic is re-proved.

ComputationalAdvice directly reuses Advice.exists_uniform_bound_selector. Nearest existing
finite selector is ColZK.exists_hidingView_bound, which cannot cover an arbitrary witness
domain. Its finite maximum proof was not copied. Promotion request: the length-indexed
logical lifting belongs with a future shared advice/reduction helper.

acceptProb_prod's nearest relative is the local hX product computation in ColZK.exists_fixSeed;
no exact public sampler-factor averaging reader was found. It directly reuses acceptProb_def,
uprob_comp_equiv and uprob_prod. acceptProb_update_tuple SPECIALIZES the existing public
acceptProb_update (Indistinguishability.lean:103), dropping Unit via acceptProb_fst; it does
not construct/re-prove a uniform update bijection. postprocess_fst uses acceptProb_bind,
the product reader and HardcoreBit.uexp_fst. Promotion requests: these generic acceptance
readers belong in shared Experiments/Indistinguishability, which are frozen here.

continuationProb/phaseGap are topic-specific semantic leaves, with canonical_eq readers.
Bellman uses published acceptProb_update and owned suffix readers; real identity uses a's
published fixed point; sim identity uses b's phaseContinuation_eq. These helpers introduce
no probability distribution host, simulator loop, or normalization proof.

The actual q*epsilon theorem directly reuses HybridRecursion, PrefixLaws, phaseGap_eq_drift,
and both suffix endpoints. Nearest specialized bounds are the ThreeColoring hybrid and
coordinatewise pair-hybrid theorems in Commitment; they do not supply this adaptive real
prefix/simulated suffix contract. No specialized proof was copied. distAdv_reindex is only
acceptProb_comp_equiv plus supplied function equalities; promotion to shared sampling is
requested. Endpoint transfer reuses stable EndpointSampling, not a second coin induction.

## Native validation and corrections

All attempts use LEAN_SLOT_TAG=seq-zk-c, the shared lean-slot.sh wrapper, /usr/bin/time -l,
scripts/lean_check_tree.sh ONE module, and c's private seq-zk-c olean tree. All Python uses
python3 -I. Every raw output, source-attempt snapshot and structured result is retained.
No interruption, timeout, sampling, resource exception or Lake command in this task.

- HybridRecursion01: rewrite could not infer a product integrand through projections.
  Supplied it explicitly to the public expectation-equivalence reader. Attempt02 passed,
  0diagnostics,2.23s,maxRSS2,116,681,728.
- SuffixLaws01: omega saw an opaque Fin.mk.val term. Exposed its concrete value by change.
  Attempt02 passed,0diagnostics,2.53s,maxRSS2,227,847,168.
- ComputationalAdvice01 passed,0diagnostics,2.17s,maxRSS2,006,581,248.
- ContinuationProbability01: implicit product/fst reader matches and update_self name;
  fixed through explicit functions and the published correct reader. Attempt02: explicit
  Fin value and bind postprocessor needed. Attempt03 passed the complete shared gap/drift
  module. Attempt04, doc-final only, passed0diagnostics,2.35s,maxRSS2,243,788,800.
- ComputationalHybrid01: after suffix_zero, an own local realView alias goal remained;
  closed it by rfl. Attempt02 passed all four complete declarations,0diagnostics,2.33s,
  maxRSS2,231,697,408. No target or premise change.

Endpoint's separate record includes its final canonical-reader check02. The old read-only
NormalizedStep diagnostic suggestions are corrected by normalized-step-diagnosis-correction.md:
the actual cause was a missing direct Defs import, found by a/root with with_reducible.
The initial closed evidence remains byte-identical, preserving the full chronological record.


### Preserved implementation record: subagents/seq-zk-b/computational-reduction-overlap.md

# Computational reduction search and overlap disclosure

Worker: seq-zk-b. Source SHA256: 32d8ef575f769772b7e8b4b309ddf55d3e52c605c0f09c7fdc98cdbec11e6bb3.

Searches are retained verbatim in computational-reduction-searches.log. No existing generic
metadata-driven normalized one-phase/simulated-suffix reduction was found. The nearest
concrete reductions are ThreeColoring/ColZKMachine.lean exists_colHidingRed (commitment
hiding with advice) and SimulatorLemmas.lean exists_hybRed_ge (commitment-coordinate hybrid).
They do not implement this sequential-protocol continuation; no proof body was copied.

Direct reuse: Complexity/Randomized/Closure.lean exists_comp, exists_seq, exists_withAdvice;
public NUPPT uniform constructor, input/layout and activation readers; WrappedVerifier
phaseAux_eq/phaseAux_poly; PhaseView normalization PT reader; SuffixMachine phaseSuffix_poly;
EncodingMachines unary arithmetic; public pair/encoded-message readers. No new host or
hand-built control machine was introduced. Raw prefix advice decodes totally, including
malformed words, without testing witness or reachability.

phaseContinuation repeats the normalized-candidate append expression of phaseStep and the
local phasePrefix_poly assembly. Its candidate is supplied externally, while phaseStep
computes it by activating S, so phaseStep_poly cannot directly instantiate this function.
The PT leaf is re-derived from the published normalization/pair/append readers, then the
published arbitrary-start/prefix suffix theorem is applied. A later extraction could share
that candidate-append PT leaf. This overlap and reuse were explicitly approved by the lead.

The uniform continuation sampler is nearest exists_phaseSimulator, but it reads arbitrary
advised metadata/current raw candidate rather than constructing a whole repetition from an
empty prefix. Both use the same published uniform constructor, not duplicated hosts.
All additions stay within the approved helper scope; no frozen source or Mathlib root changed.


### Preserved implementation record: subagents/seq-zk-b/reduction-advantage-overlap.md

# Typed reduction advantage overlap disclosure

Worker: seq-zk-b. ReductionAdvantage.lean introduces no definitions or hosts. Searches are
retained in reduction-advantage-searches.log. Nearest generic readers are
EnsembleLemmas.acceptProb_coins_equiv and coinsEquiv/take_ofFn_coinsEquiv/
drop_ofFn_coinsEquiv (Asymptotic/EnsemblesLemmas.lean:85,141,151,156). They are directly reused,
not copied. This improves the initially proposed local splitCoins/cast equivalence by using
the already published exact split/cast constructor and its two tape readers.

CommitmentLemmas.acceptProb_distinguisherL_of_runAtL handles one deterministic preprocessor
with an equal coin polynomial. ThreeColoring/ColZKMachine.distAdv_distinguisherL_reparam
handles deterministic preprocessing with a changed security parameter. Neither handles the
random continuation suffix and independent final-distinguisher tape required here. Their
standard public-reader/reindexing pattern is reused, but no proof body was copied and no
new general probability transport theorem is introduced. The new theorem applies the
existing acceptance reindexer twice and the public distAdv_def.

Canonical FunFamily.blocks.symm only regroups the simulator coin table; its implementation
is not unfolded. The raw run equation is a hypothesis supplied by exists_phaseReduction,
so the proof does not unfold any foreign reduction or machine. Only the local equivalence
e is expanded. NUPPT.distinguisherL_eq/runAt_eq/coinLen_eq and PolyExpr evaluation readers
supply all foreign computations. No validity, reachability, witness or nonemptiness premise
was added. Parent approved this exact statement and source-only integration.


### Preserved implementation record: subagents/seq-zk-b/computational-phase-bound-overlap.md

# Common phase-bound overlap and reuse disclosure

Worker: seq-zk-b. Parent approved this exact helper/API after receiving a concrete proposal.
No existing theorem was found assembling the fixed original wrapped-ZK comparison into the
common finite-metadata phase bound. Searches are in computational-phase-bound-searches.log.
Nearest relatives are c's exists_uniform_negligible_bound/exists_uniform_bound_selector,
a's PhaseMetadata bounds/cover, our advised phase reduction and typed advantage bridge,
and c's shared phaseGap reader. They are all reused directly; no selector, cover, reduction,
coin transport or probability host is copied. No public definitions or hosts are added.

The bounded-gap leaf directly reuses ColZK.distAdv_le_one from the already cached pinned
ThreeColoring/ColZKLemmas module; no duplicate generic probability lemma or new Mathlib root
is added. Local syntactic polynomials set H=Q*k*(2B+2) and
b=2*var+2*Lz+2*V.coins+2*Q+H+8. The selected metadata word has length at most b by the public
PhaseMetadata.toData_length_le/toData_eq readers. On canonical raw-prefix validity,
reductionData_encodeMsgs identifies this word with pairEncode x aux. The existing public
length_pairSndD_le reader bounds aux; no pair arithmetic is reproved.

Validity is a local proof-only predicate R x y plus canonical-prefix and j<Q facts.
The arbitrary witness y is outside the finite metadata and is neither stored nor tested.
The existing selector is applied before requesting the original negligible error. The
machine remains the already checked total advised phase reduction. The final exact cover
handles arbitrary typed bounded prefixes, without a reachability or prover-bound premise.

The first two failures concerned only local argument/name/equality elaboration. Native01
exposed implicit List.length_ofFn use, a missing Turing namespace, and dependent coin casts
from rewriting a parameter inside the distinguisher. Native02 exposed a rewrite touching
both sides of a canonical-prefix equation and the final analogous dependent distinguisher
transport. Keeping local experiments at actual decoded x.length, transporting the whole
real-valued phaseGap by congrArg, and applying the public packed-prefix reader resolves them.
No theorem statement, hclose premise, or machine construction was weakened. Exact source
snapshots and all raw failure logs are retained. Native03 passed; native04 seals a single
line wrap only, with an exact inverse-transform hash check retaining attempt03.

All foreign definitions are used through published equations/bounds. Only local aliases
are unfolded. Sibling helper sources are copied unchanged with SHA256 provenance and checked
independently in seq-zk-b's private olean tree. No sibling oleans, frozen files, main edits,
new Mathlib roots, Lake calls or Git commits are involved.


### Preserved implementation record: subagents/seq-zk-c/final-acceptprob-reader/README.md

# Final explicit acceptance-reader correction

Lead-owned canonical C_A found one foreign-definition access in
ContinuationProbability.acceptProb_prod: its initial acceptProb_def rewrite affected the
outer occurrence, while the RHS occurrence inside uexp was left for the final rfl to
unfold. The full old seal failure is preserved by the lead at
evidence/logs/final-seals-stream-2/final-coe-SealA_Cryptography_Composability_SequentialZK_ContinuationProbability.log,
reported line155. This was a reader-discipline failure, not a false theorem.

At the lead's request, c changed ONLY that short proof's last line. The final source uses
`simp only [acceptProb_def, Equiv.prodAssoc_symm_apply]`, reading both the RHS acceptance
formula and the product-association equation explicitly. No public statement, import,
other proof byte, frozen file or scope changed. The withV seed-reader correction remains
exactly as checked before. No seal/probe was run by c; lead reruns the affected20 cells.

Old source SHA4b7b7ad15dcd6ead93532c83dfe9e2b1f9750e2d5933ae359949bd7b4475db9a.
First reader-only trial SHA8d631348a0f8e346dcf6df132fa70df0572830978ee140ceb0e48f8a208f7e84
exposed one remaining ordinary native goal: product-association evaluation. Its complete
source/patch/roundtrip and raw native failure remain,2.69s actual runtime,
maxRSS2,238,791,680bytes. No interruption, timeout or resource exception.

Final source SHA91355ac3dff34e7b06e8684bf36b1c5fb363c7688a737f8f4efcf4f18246011d,
354lines/max94columns. Adding the published product-association reader closes the same
proof. Native retry02 passed0errors/0warnings,2.42s actual runtime,
maxRSS2,246,049,792bytes. All output/source/result evidence is preserved; final patch and
roundtrip-final.json verify exact forward/reverse git-apply bytes and that replacing only
that final line by the old rfl restores every old source byte, including all statements.

Both native attempts used seq-zk-c, the shared Lean slot wrapper, the private c olean tree,
/usr/bin/time -l and scripts/lean_check_tree.sh for this module alone. No Lake, dependent
sweep, seal, axiom probe, new definition, theorem or Mathlib root. All171 prior current
receipt files were verified unchanged. Source and this new evidence are closed for exact
copying into the lead's final revision6 matrix/payload.


### Preserved implementation record: subagents/seq-zk-a/final-review-12/REPORT.md

# Final explicit-reader scan: unresolved-name review

Reviewer: seq-zk-a. Final proof revision d842dc8f681f6b89499129f5b64a50d0e4587935.
Read-only review of scan1.py, scan2.py, review_explicit.py, and the final-repair/explicit
inputs/results. All41scanned source files independently match the committed revision byte
for byte (source-revision-verification.json). No Lean/lake command or source edit was made
by this reviewer. Python scripts write only this final-review-12 evidence directory.

## Completed outcome

The raw scan contains1245items:868native-resolved theorem uses,6same-module definition
uses,and371LOCAL_OR_UNRESOLVED items. Its zero-foreign count alone was incomplete evidence
until those371items were reviewed. Every one is now classified source-locally and the
nonlocal aliases are checked by the lead's completed secondary native probe:

| Supplement category | Items |
|---|---:|
|Named local hypothesis, case, lambda, obtained value, or let|322|
|Anonymous local have proof named this|2|
|Inline typed show equality proof term|15|
|Local equality combined by Eq.trans|1|
|Public theorem/equality/iff/contract readers through aliases|29|
|Additional same-module inherited AbortRetry definitions|2|
|Still unexplained|0|

Thus the merged interpretation is897public theorem/reader items,8same-module definition
items,and340local/inline proof items. No foreign definition-body unfolding was found. All
eight same-module definition occurrences are in declarations marked UNCHANGED by the
base/final touched map. No newly added/changed declaration unfolds a foreign definition
explicitly in this scan. The raw scan2 output is retained unchanged; this is a separately
reported supplement, not a silent rewrite of its results.

## Native alias confirmation

The lead ran `.lake/seq-zk-rule10/final-repair/explicit/ExplicitAliases`; the retained log
`evidence/logs/final-explicit/final-explicit-aliases.log` contains all24requested canonical
names,EXPLICIT_ALIAS_DONE24,and EXIT0,with zero error: or error( diagnostics.22names have
native kind theorem and type_is_Prop=true; the only two definitions are AbortRetry.attempt
and AbortRetry.retry,with the same Defs module home as their explicit uses.

The initial conservative warning that proof-valued class/spec fields might have definition
kind was a probe-design precaution, not an observed issue. The pinned native result
actually classifies every queried proof field as theorem-kind. native-supplement-validation
records these exact results and probe/log hashes.

## Why the scanner left valid names unresolved

1. Export aliases are absent from the probe's raw env.constants string map. `mul_zero` and
   `zero_mul` are exported from MulZeroClass at Mathlib/Algebra/GroupWithZero/Defs.lean:77
   (field declarations35,37). Their canonical names MulZeroClass.mul_zero and zero_mul are
   theorem-kind public equality readers in the native result. `not_not` is exported from
   Classical at Mathlib/Logic/Basic.lean:188; Init/Classical.lean:141 declares the theorem.
2. Receiver notation needs the local receiver type. hA.advice_eq/hS.advice_eq resolve to
   Complexity.NUPPT.Uniform.advice_eq (Randomized/PPT.lean:300). The specification methods
   h.realCoinsEquiv_fst_ofFn,d.phase_take,and d.outV_eq resolve to their published
   PaddedProverSpec/PaddedVerifierSpec theorems. The13spec-field uses are public equality
   proof projections (first,rounds_eval,next,boundary; rounds_eq,first_eq,next_eq,terminal_eq,
   period,local_length), not attempts to unfold those projections' definitions. All are
   native theorem-kind/type-is-Prop=true.
3. List.mem_singleton.mp and List.prefix_iff_eq_append.mp apply the mp direction of public
   iff theorems to local membership/prefix proofs. Canonical List lemmas and Iff.mp were
   verified natively. hpV.trans hp combines two local equality proofs using Eq.trans;
   hpV is explicitly bound by congrArg at SequentialZK.lean:669.
4. `open AbortRetry in` appears at Defs.lean:588 before the following theorem's docstring.
   scan1.py only searches tactic-local opens inside the owning declaration span, so it
   misses this legal preceding local open. At636,648,the inherited simp arguments attempt
   and retry are owned AbortRetry.attempt/retry (defined at328,346 in that same file). At642,
   firstHit_map_getD_eq is the public AbortRetry theorem declared at460. These are not
   private copies and are not foreign-definition uses.
5. The inline keyword show is not a declaration name. The15full items are13arithmetic
   equality terms proved by ring/omega and two local funext h equalities. No foreign body
   is hidden in those terms. The two local this entries come from anonymous have:= at
   Defs.lean:472 and494 before their rw uses at474 and496.

## Source-local handling of ordinary local names

For322entries the review retains the enclosing compiled declaration and direct binding
evidence (have,let,set,by_cases,intro,obtained pattern,case/lambda binder,or typed premise)
strictly before the scanned use. No blanket “starts with h” rule was used. All322had a
direct binder match under a second stricter pass. The two anonymous-have cases were
reviewed manually and explicitly overridden. The exact occurrence, full rewrite item,
source context,and local binding lines are in native-validated-review.json. The original
proposed/unlocated intermediate files remain for provenance; resolved-review and native-
validated-review explicitly resolve both initial missing binder locations.

## Tool review and requirements

scan2.py correctly keeps LOCAL_OR_UNRESOLVED separate at32–33 and reports raw foreign
items only among resolved names at37–46. It cannot itself certify zero foreign unfolding
while unknown names remain. Its equation-target handling covers generated eq_N,eq_def,
eq_unfold heads; the original explicit-items inventory remains authoritative for those
lexer records. Any native-kind continuation must preserve both diagnostic forms error:
and error( and must require successful completion/exit, as done in the root logs here.

review_explicit.py is not generic for this fill: it hard-codes hash-sign SignatureScheme
aliases,an unrelated local-head whitelist,and writes .lake/hash-sign-rule10 paths. It should
not be executed unchanged or treated as resolving the371seq-zk unknowns. The present
supplement performs the corresponding source-specific review and canonical native check,
while leaving that archived tool untouched.

This explicit scan is one part of Rule10 evidence; it does not replace strict/coe A/B
irreducibility seals or their attribution. The lead's separate native sweeps/axioms/seals
remain the authority for implicit elaboration. No source correction is requested by this
review. All files produced here are indexed by receipt.tsv and lie outside the historical
frozen CP3 and post-CP3 audit receipts.

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

## ===== briefs/pass-shelat-ch5-8/fills/seq-zk/issued-r1/brief.md =====

# Claude fill · sequential repetition preserves zero-knowledge and interactive proofs (the five `seqRep` theorems, Theorem 175.1)

**Issue base** `107f1e8c218733eac12d6b9bee6fece441271317` on `cryptography/pass-shelat-ch2-4` (the records tip after #303, #305, #306,
#308 and #309; records-only commits since `58a061c9`). **Unit** `seq-zk`. **Worker** Claude (standing ruling, 2026-11-11). **Lean** 4.25.0 and the
Mathlib revision in that commit's `lake-manifest.json`.

Prove the admitted theorems `ZK.seqRep`, `StatZK.seqRep`, `InteractiveProof.seqRep`, `InteractiveProofErr.seqRep` and `EfficientProverProofErr.seqRep` of [PS10, §7.2.1, Theorem 175.1] and [Gol01, §4.3.4] in
`TCSlib/Cryptography/Composability/SequentialZK.lean`. The statements passed the prong C statement phase, Gate 03 (rulings G3-3, G3-4, G3-7d) and Gate 06,
and are frozen. Each docstring holds the maintainer's proof sketch.

## Feasibility (maintainer's assessment)

Feasible: the statements passed their gates, the sketches are explicit, and the iterate hosts and hybrid lemmas exist. No dependency on an admitted target. The risk is size: the checkpoints are ordered so that each delivers whole declarations, and a final that proves only some of the five is allowed (see *Partial delivery*).

**Estimated size:** 5,000–10,000 lines in roughly 10–15 helper modules, the largest unit of this batch. For calibration, one theorem (cca2-ett) landed 5,364 lines.

## Checkout and delivery

- Fetch `cryptography/pass-shelat-ch2-4`. Start a local branch `fill/seq-zk` at the exact issue base, and
  record the base in `REPORT.md`. Keep the proof branch local.
- Read `policy.md`, the attached environment addendum and `README.md`.
- Deliver every checkpoint and the final payload under `inbox/fills/seq-zk/` on `exchange/pass-shelat-ch5-8`:
  - `REPORT.md`;
  - `patches/`: the whole `git format-patch` series from the issue base;
  - `patches/COMMITS.tsv`: one row per commit, giving its hash, the author's name, email and date, and the
    committer's name, email and date, so that `git am` at the base reproduces every hash. Before you push,
    check the reproduction in a scratch clone and say so in `REPORT.md`. The last batch's worker hashes
    could not be reproduced, because no committer metadata was delivered;
  - `src/`: the changed and new files;
  - `evidence/`, with an `evidence/SHA256SUMS` manifest (see *Evidence completeness*);
  - a top-level `SHA256SUMS` listing every delivered file under `inbox/fills/seq-zk/` except itself. The
    delivered paths must equal the manifest's paths exactly, with nothing missing and nothing extra.
    Check this before each push.
- Commit as `fill seq-zk: checkpoint N` and `fill seq-zk: final`.
- Pull with rebase before pushing, push only your delivery path, and never force-push. Campaign changes land
  by a maintainer PR for Seyoon's approval.

## Base and parallel work

- **#307 (dl-crh) is not merged.** It changes `Candidates/DiscreteLog.lean`, the `Hashing.lean` facade and `Hashing/FromDiscreteLog*`. This unit edits none of them, and its closure contains none of them.
- The other fills of this batch (`prf-mac`, `learning`, `derand`, `canonizer`, `sc-ot`, `sc-compose`) start from the same base.
  Each edits only its own owned file and helper directory.

## Targets (frozen; quoted from the issue base)

```lean
theorem ZK.seqRep {B : PolyExpr} (h : ZK π R) (hB : π.ProverBounded R B) (Q : PolyExpr) :
    ZK (π.seqRep Q) R := by
  sorry
```

```lean
theorem StatZK.seqRep {B : PolyExpr} {δ : ℕ → ℝ} (h : StatZK π R δ)
    (hB : π.ProverBounded R B) (Q : PolyExpr) :
    StatZK (π.seqRep Q) R (fun n => Q.eval n * δ n) := by
  sorry
```

```lean
theorem InteractiveProof.seqRep {L : Language Bool} (h : InteractiveProof π L) (Q : PolyExpr)
    (hQ : ∀ n, 1 ≤ Q.eval n) : InteractiveProof (π.seqRep Q) L := by
  sorry
```

```lean
theorem InteractiveProofErr.seqRep {L : Language Bool} {s : ℕ → ℝ} (h : InteractiveProofErr π L s)
    (Q : PolyExpr) (hQ : ∀ n, 1 ≤ Q.eval n) :
    InteractiveProofErr (π.seqRep Q) L (fun n => s n ^ Q.eval n) := by
  sorry
```

```lean
theorem EfficientProverProofErr.seqRep {L : Language Bool} {s : ℕ → ℝ}
    (h : EfficientProverProofErr π L R s) (Q : PolyExpr) (hQ : ∀ n, 1 ≤ Q.eval n) :
    EfficientProverProofErr (π.seqRep Q) L R (fun n => s n ^ Q.eval n) := by
  sorry
```

They live in namespace `TCSlib.Cryptography`. The section variables are `{π : Protocol} {R : List Bool → List Bool → Prop}`.

**The construction** (owned, proved readers): `Protocol.seqProver`, `seqVerifier`, `seqRep`, with
`moverIsV_two_mul_add`, `countP_moverIsV`, `countP_not_moverIsV`, `exec_fst_length`, `exec_snd_length`,
`proverMoveIndex_exec`, `verifierMoveIndex_exec` and `Protocol.seqRep_exec_phase` (phase `j` of an honest run is a
run of `π` on coin slice `j`). Read the module docstring's deviations: filler moves, strict-PPT simulators
(G02-#4, D8), bounded prover messages (`ProverBounded`, G3-3), and at least one phase for soundness.

**Proved consumers:** `PerfectZK.seqRep` and `PerfectZKAbort.seqRep` (from `StatZK.seqRep`) in the owned file;
`Composability/ThreeColoring.lean` uses `ZK.seqRep` and `EfficientProverProofErr.seqRep` (Theorem 124.1). Their
axioms become standard with yours.

## Published interfaces

| Interface | Provider |
|---|---|
| the construction readers listed above, `seqRep_exec_phase` | owned file |
| `ZK_iff`, `StatZK`, `perfectZK_iff`, `PerfectZKAbort.statZK`, `StatZK.zk`, `NUPPT.simulate_eq`, `attempt`/`retry` readers | `ZeroKnowledge/Defs.lean` |
| `Strategy`, `efficient_iff`, `ofNUPPT_efficient`, `exec` and its readers, `viewV`, `outV`, `View.encode`, `encodeMsgs`, `ProverBounded`, `withV` and `withV_vCoinsEquiv` | `ZeroKnowledge/Interaction.lean` |
| `InteractiveProof`, `InteractiveProofErr`, `EfficientProverProof(Err)` fields | `ZeroKnowledge/InteractiveProofs.lean` |
| `exists_hybrid_gap`; `StatClose`, `distAdv_le_of_statClose` | `Foundations/Probability.lean`, `Asymptotic/Sampling.lean` |
| `coinBlock`, `FunFamily.blocks`, `distinguisherL` | `Asymptotic/Adversary.lean` |
| `polyTimeComputable_iterate`, `polyTimeComputable_iterateFind`, `polyTimeComputable_iterateEmit`; `BinArith.polyTimeComputable_iterate` | `Complexity/Randomized/Repetition.lean`, `Complexity/ClassP/BinaryArith/Iterate.lean` |
| `NUPPT.exists_comp`, `exists_withAdvice(On)` (the non-uniform hybrid reduction), `ofPolyTimeUniform`; `Negligible.mul_pow`, `const_mul`, `mono` | `Complexity/Randomized/Closure.lean`, `Foundations/Negligible.lean` |
| `simulate` and `OracleComp` laws, `buildComp_*`, `CostBoundedBy`, `bitCodec_*`, `ProbComp.expect_*`, `advantage_eq`, `accept_eq` | `Games/*` |

## Proof route and checkpoints

1. **Checkpoint 1 · `InteractiveProof.seqRep`.** Efficiency of `V_Q` (a uniform machine with coins `Q · coins`, built from the iterate hosts over the phases and `coinBlock` slices), completeness from `seqRep_exec_phase`, and soundness from phase 0 (sketch steps 1–3). Send this checkpoint.
2. **Checkpoint 2 · `InteractiveProofErr.seqRep` and `EfficientProverProofErr.seqRep`.** Soundness error `s^Q` by conditioning on the prefix and induction on the phases, with the prover strategy that hard-wires the prefix; efficiency and completeness of `P_Q`. Send this checkpoint.
3. **Checkpoint 3 · `StatZK.seqRep`.** The normalized simulator `S_Q` as a uniform strict PPT (one verifier tape, `Q(n)` calls of `S` on fresh coin blocks, the canonical normalization and fallback), the empty-history case, and the triangle inequality over the `Q(|x|)` hybrids, giving exactly `Q(|x|) · δ(|x|)`. Send this checkpoint.
4. **Final · `ZK.seqRep`.** The wrapped verifier `V*` and its efficiency, the simulator of `ZK π R` at the enlarged bound `Lz'`, the non-uniform phase reduction with advice, and the sum of the `Q(n)` gaps, `Q(n) · ε(n)`, negligible.

Check the edge cases: `k = 0` rounds; `Q(n) = 0` for the ZK statements (empty history; the proof-system statements assume `1 ≤ Q(n)`); odd `k` (three-message protocols); `verifierFirst` true and false; a cheating verifier's filler replies; malformed or non-canonical simulator outputs; the auxiliary-input bounds `Lz` and `Lz'`; the honest prover's `[]` fillers.

If the sketch is wrong, or a target is false as stated, stop and escalate with the exact obligation: a
checkpoint with the counterexample or the missing fact. Do not weaken any statement.

**Partial delivery.** If you cannot finish every target, your final payload may prove a subset. Each proved
declaration must use only the standard axioms. The others keep their `sorry` and their statements,
and `REPORT.md` says which are proved and what remains for each of the others.

## Scope and proof discipline

- **Owned file.** You own `TCSlib/Cryptography/Composability/SequentialZK.lean` (509 lines at the issue base):
  - replace the targets' proof bodies and edit their sketches to describe the delivered proof;
  - update the module title (drop "(statement phase)" where present) and the `## Main results` status.
- **Helper modules.**
  - They are permitted under `TCSlib/Cryptography/Composability/SequentialZK/`. The owned file imports them precisely and gets a
    `## Contents` list.
  - **Facades.** After the facade-lint fix (#305), a new helper under `X/` is covered as long as `X.lean`
    imports it, so no parent facade needs an edit.
  - Helpers may import modules already in the closure (the ZK layer, `Games/*`, `Complexity/*`).
- **Size and width.** Every line has at most 100 characters (Python `len`), and every file at most 1000 lines.
  Check both with a short `python3 -I` script before each push and include its output in `evidence/`.
- **Frozen files.** Do not edit any other file.
  - `Games/Efficiency.lean` is at 982 lines. Do not add to it.
  - **Scope requests.** If the route needs a change to a frozen file (a reader beside a foreign definition, an
    import, a promotion), stop that line of work. Ask Seyoon in your session, giving the exact file, the diff
    and the reason, and go ahead only on his approval. Record the request and his answer verbatim under
    `evidence/scope-request/` and in `REPORT.md` § *Scope requests*. The Codex fills obtained their facade
    imports, and dl-crh its two `DiscreteLog` readers, this way. Seyoon prefers a route with no frozen-file edit
    where one exists.
  - A lemma that belongs in an existing file goes in your helper module, with a promotion request.
- **Parallel fills.** The seven fills `prf-mac`, `learning`, `derand`, `seq-zk`, `canonizer`, `sc-ot` and
  `sc-compose` are issued from the same base. Edit only your owned file and helper directory.
- **Duplication (binding).**
  - **Search first.** Before writing any lemma, search `TCSlib/` and Mathlib for its statement shape and key
    names. Reuse published lemmas by importing them.
  - **Private lemmas.** Never copy a private lemma silently. If you need one, re-derive it from published
    readers, keep its statement general, and disclose it.
  - **Disclose every overlap.** `REPORT.md` has a section **`## Overlap and reuse`**. For every new declaration
    that restates, specializes or re-proves existing material (public or private, TCSlib or Mathlib), give its
    nearest relative (`path:line`), the relation, and why it is not reused. List the searches you ran.
  - **Why.** Undisclosed duplication is a freeze violation, not debt. The majors that held Gates 23 and 24
    were undisclosed duplicates: G23-01, a private copy of `length_le_length_encodeLog`; G24-01,
    `inputWord_take`, which re-proves the public `take_ofFn_castLE`.
  - **Nearest relatives here:** `PerfectZKAbort.statZK` and its retry machine (`ZeroKnowledge/Defs.lean`), the hybrid arguments of the 3-colouring and graph-isomorphism proofs (`ZeroKnowledge/ThreeColoring/*`, `ZeroKnowledge/GraphIsomorphismZK/*`), `exists_hybrid_gap`, and the repetition hosts of `Randomized/Repetition.lean`.
- **Statements.** Preserve the target statements, every other declaration, the statement prose and the global
  simp attributes.
- **Docstrings and sketches.** The last batch's landing edits were mostly LE-doc (cca2-ett: 94 formulas and
  15 sketches; dl-crh: 59 formulas; lamport: 188 formulas and 7 sketches) and LE-width. Do these yourself:
  - every new public declaration has a docstring that states its formula: the equation or inequality, with its
    arguments in the Lean order, and a `[PS10, …]` tag where it comes from the source;
  - every proof of 15 lines or more carries a `**Proof sketch.**` paragraph, and long proofs get step comments
    (policy §3);
  - a new public `def` lands with its `_eq`, `_iff` or `simps` readers (lint check 8), and a new public
    `abbrev` with an `_eq` or `_iff` lemma;
  - add no `@[simp]`.
- **Rule 10.**
  - Use only published readers for other files' definitions, including generated matchers and projections.
  - Your helper modules count as foreign to each other and to the owned file. The owned file's definitions
    are foreign to your helpers.
  - **Notation, never sealed:**
    - `PolyExpr.eval` (Q1);
    - reducible abbreviations (2026-10-26; for example `QueryImpl`, `OracleSpec.add`, `glNeed`);
    - **projection coercions:** a `CoeFun`/`Coe` instance whose body is a structure projection, such as
      `FinDist`'s `⟨FinDist.prob⟩` (Seyoon's ruling, 2026-11-14).

    The coe-variant seals are canonical. Run the strict variant as well, and attribute each difference.

## Checks and report

- **Bootstrap.**
  - Bootstrap from `order.txt` (237 modules) and the narrow `roots.txt` (76), following the addendum.
  - Check one module per `scripts/lean_check_tree.sh` call, with one Lean process per olean tree.
  - Never run `lake build` or an unfiltered cache get. Run Python as `python3 -I`.
  - Insert helper modules before their consumers.
- **Sweep.**
  - Recheck the owned module, then sweep the supplied order with 0 errors.
  - Compare the `sorry` warnings with `base-sorries.txt` (23 declarations in 9 modules). The only change
    must be the removal of `ZK.seqRep`, `StatZK.seqRep`, `InteractiveProof.seqRep`, `InteractiveProofErr.seqRep` and `EfficientProverProofErr.seqRep`.
- **Axioms.**
  - Print the axioms of `ZK.seqRep`, `StatZK.seqRep`, `InteractiveProof.seqRep`, `InteractiveProofErr.seqRep` and `EfficientProverProofErr.seqRep`. Expect only `propext`, `Classical.choice` and `Quot.sound`.
  - Print them for every stored constant of the changed and new files, and of `PerfectZK.seqRep`, `PerfectZKAbort.seqRep` and the `Composability/ThreeColoring` consumers.
- **Rule 10 evidence.**
  - Run whole-file seals A and B of every changed or new file over its full TCSlib import closure, at base and
    final.
  - Run both the **strict** and the **coe** variant (projection coercions sealed, or treated as notation).
    Report every failing declaration in each.
  - Add paired controls that pass unsealed and fail sealed, each sealed negative failing exactly once.
  - Run the explicit-unfold scan.
  - Report the seals with `PolyExpr.eval` both excluded as notation and sealed.
  - **Error counts (G26-N1).** Your runner must count both diagnostic forms, `error:` and `error(…)`, for
    example with `^\S+\.lean:\d+:\d+: error[:(]`. Keep every raw log.
- **Lint.**
  - Run `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography --check8b` at base and at final.
  - The baseline at the issue base is **92 FAIL / 101 WARN** (after #305).
  - Diff the line sets, not only the counts. There must be no new FAIL line, and no new WARN line except one you
    disclose and justify.
- **Report.** `REPORT.md` gives:
  - the base and the status of each target;
  - the changed files and the sketch edits;
  - the new declarations;
  - **Overlap and reuse**;
  - **Scope requests** (none, or each with Seyoon's answer);
  - the promotion and reader requests;
  - the evidence, with its manifest.

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
| DL-44 | prf-mac fill (delivery review 2026-11-15): F-01 local `hadv` in `MAC/FromPRF/Bound.lean` re-proves public `ETTGame.prfAdv_eq_expect` (**ruling Seyoon 2026-11-15: promote now** to the PRF layer beside `prfAdv`, re-derive the ETT copy proof-only, re-point prf-mac); F-02 `decide_fnForge`'s `hw`/`htake`/`hdrop` restate list readings of `splitBits` (`take_ofFn_castLE`, `CollectionsHelpers.ofFn_drop_take`, `FromDiscreteLog.ofFn_splitBits_fst/_snd`); F-03 `PRFMAC.blocks`/`macState`/`hits_nil_iff` near `GGMRed.tblEnc`/`lookup` (cca2-ett `tblW`). The private `prfAdv_prfReduction` (`OracleFromPRF.lean`) is the same identity specialised (DL-40). | `TCSlib.Cryptography.prfAdv_eq_expect` (published in #314, merge `59c2c1fb`); the list readers above; `GGMRed.tblEnc` | Open (F-01 paid) | F-01 **paid**: promoted in #314 (ETT re-derived, LE-gate30), prf-mac re-pointed by LE-reuse `590d1a56` (#317, Gate 33). F-02/F-03 and the private `prfAdv_prfReduction` in the deferred cleanup. |
| DL-45 | learning fill (delivery review 2026-11-15): undisclosed `LearnPRF.uprob_eq_point` = `OneWay.uprob_eq_one_div_card` (reversed); inline re-proof of `MultiMsg.abs_uexp_sub_le_uprob` in `abs_gameProb_random_sub_half_le` (both re-pointed by maintainer LE-reuse `8befc589`, #313); private `length_blk` re-proves `MultiMsg.length_histBlock` for the disclosed private copy `blk` of `histBlock`; `flip0`/`flip0_flip0` = `flipBit`/`flipBit_flipBit` (BooleanAnalysis) and `flipAt` (DeterministicCC); `foldr_pairEncode_nil` reads `Strategy.encodeMsgs`; short-name clashes `relabel`/`relabel_eq` (DL-36 family) and `flipAt`. | `OneWay.uprob_eq_one_div_card`; `MultiMsg.abs_uexp_sub_le_uprob`, `length_histBlock`; `BooleanAnalysis.flipBit` | Open | Items 1–2 by LE-reuse at landing; the rest in the deferred cleanup. |
| DL-46 | prf-long fill (delivery review 2026-11-15, disclosed): `MultiMsg.encodeList_eq_flatMap` (`FromPRF/MultiMsgOut.lean`) is a third copy of public `encodeList_eq_flatMap` (`Asymptotic/BlockEncryptor.lean`) beside the frozen private copy in `FromPRF.lean` (now unused); reuse blocked by a private/public name clash. `histBlockLen` kept beside `histBlockLenOut` (different `PolyExpr` terms); `adviceBound` now unused. Near relatives: GGM `encodeHist_eq_histEnc`/`histEnc_append_single`/`length_histEnc`, `UniformTableauEmitter.encodeList_eq_flatMap`. | `encodeList_eq_flatMap` (to move to `EnsembleSecurity`, worker's promotion request) | Open (deferred) | Promote and delete the copies; remove the unused frozen items under a frozen-file exception in the cleanup. |
| DL-47 | Gate 32 staging (2026-11-15), pre-existing: copies of `((List.ofFn f).drop i).headD d = f i` and of its getD form `(List.ofFn f).getD i d = f i`, at the tip `e9998722`. Inline chain: `Pseudorandom/NextBit.lean:454` (`headD_drop, List.getD_eq_getElem?_getD, List.getElem?_ofFn`, the remnant of NextBit's private `headD_drop_ofFn` that dl-consolidation L1 deleted). Index-0 cases: `headD_ofFn_one` (`Foundations/BitLists.lean:75`), `GIZK.headD_ofFn_block` (`ZeroKnowledge/GraphIsomorphismZK/Closeness.lean:280`), private `eq_const_headD` (`Encryption/PublicKey/NonMalleability/Simulation/SimIND.lean:88`). getD forms: `GI.getD_ofFn_lt'` (`ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean:61`), `GI.getD_ofFn_lt` (`ZeroKnowledge/GraphIsomorphism/Proofs.lean:818`), `GIZK.getD_ofFn_lt` (`ZeroKnowledge/GraphIsomorphismZK/Closeness.lean:110`), `ColProofs.ofFn_getD_lt` (`ZeroKnowledge/ThreeColoring/ProtocolProofs.lean:391`), Yao's private `getD_ofFn'` (`SecureComputation/Yao.lean:611`). Inline getD chains (`List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos …`): `ZeroKnowledge/ThreeColoring/Simulator.lean:861`, `ZeroKnowledge/ThreeColoring/Language.lean:429` (in private `ofFn_getD_tape`), `ZeroKnowledge/Encoding.lean:359`; the same getD chain also inline outside the cryptography files, in `TCSlib/Complexity/ClassNP/SAT.lean:149`, `TCSlib/Complexity/ClassNP/Tautology.lean:142` and `TCSlib/Complexity/SpaceComplexity/Codec/Word.lean:135` (`getD_encChunk`). **Extended by Gate 32 G32-01 (ruling Seyoon 2026-11-15: extend DL-47 and close), at the #316 head `c18afbe6`:** exact copy of the promoted statement: GGM `Pseudorandom/Functions/Asymptotic/GGM/Run.lean:449–450` (`step_eq`, local `hbit`, replacement `TCSlib.Cryptography.headD_drop_ofFn x ⟨d.i, hi⟩ false`); headD chain `Asymptotic/HardCoreLoops.lean:278–280` (`orbit_eq`); getD/ofFn computations: `SecureComputation/Garbling.lean:193–198` (private `map_range_getD_ofFn`) and `:375–380` (`garbledValues_getD`), `SecureComputation/Yao.lean:626–627` (`yaoBobTables_yaoMsg`), `Encryption/PublicKey/BitwiseCPA.lean:107–113` (private `ofFn_half`), `Encryption/PublicKey/OracleSecurity/PaddedCPA.lean:72–78` (private `ofFn_splitHalf_bit`), `Complexity/CircuitComplexity/CircuitEvalNP.lean:68–69` (`dagCktSatLang_mem_NP`), `PSubsetPPolyGadget.lean:188–190` (`runWith_embedGates_getD`), `PSubsetPPolyProgram.lean:383–387` (`progGates_values`), `PSubsetPPolyTableau.lean:127–132` (`snapEncode_injective`), `UniformTableauCircuit.lean:427–431` (private `tabSrc_eval`), `Complexity/Randomized/RandomWalk.lean:256–259` (`decodeIdx_succ_append`), `Complexity/ClassPSPACE/TQBF.lean:857–859` (private `codecRow_realize`), optional-access form `Cryptography/Encoding/BooleanVector.lean:168–171` (`expandPoly_encode`) and `Hashing/SIS/CollisionOutput.lean:237–243` (`collisionOutputPoly_pairEncode`). **sc-garble SG-F04 (ruling Seyoon 2026-11-15, ledger):** new inline getD/`List.ofFn` chain in `SecureComputation/Garbling/CoinBlocks.lean:73–74` (`getD_eq_getElem`, `getElem_ofFn`), same as Yao's private `getD_ofFn'`. | `TCSlib.Cryptography.headD_drop_ofFn` (#316) | Open (deferred) | Ruling Seyoon 2026-11-15: pre-existing (merged before the promotion), recorded as debt and not re-pointed in #316. Re-point NextBit:454 and the index-0 cases onto `headD_drop_ofFn`, and the getD forms onto one shared getD reader, in the deferred cleanup. Yao's `getD_ofFn'` waits for sc-garble and sc-yao to land (`Yao.lean` is shared). **Cleanup plan (G32-01):** add one generic reader `(List.ofFn f).getD i d = f ⟨i, h⟩` (any type) derived from `headD_drop_ofFn` and `List.headD_drop`, then re-point every DL-47 copy onto it or onto `headD_drop_ofFn`, proof only, headers preserved, starting with the exact GGM copy; the `Garbling.lean`/`Yao.lean` copies wait for sc-garble and sc-yao to land. |
| DL-48 | sc-ot fill (delivery review 2026-11-15): F-02 `OT.splitLen` / `splitLen_symm_ofFn` (`SecureComputation/ObliviousTransfer/Simulators.lean`) restate public `coinsEquiv` (inverted) and `ofFn_coinsEquiv` (`Asymptotic/EnsemblesLemmas.lean:141,145`), body as private ElGamal `dlc_splitEquiv`; F-04 `OT.uprob_signedPredictor_false/_true` adapt `exists_pkPredictor` (`pkPredictor` has no public reader); F-07 near-relatives `GI.pairSndD_encodeMsgs` (for `getD_one_eq`), `predict_eq`, and promotion requests `negligible_finset_sum`, `statClose_prod_of_forall`, `exec_five`, `length_runAtL_le`. **Gate 34 G34-02 (ruling Seyoon 2026-11-15, ledger):** `OT.length_ofFn_coins` (`ObliviousTransfer/Simulators.lean:210–212`) is a verbatim copy of public `Composability.NMSim.length_ofFn_coins` (`Encryption/PublicKey/NonMalleability/Simulation/Rounds.lean:41–43`); direct reuse would add 69 NM modules to the OT closure. (G34-01, `OT.getD_zero_eq`/`OT.getD_one_eq'` re-proving `headD_drop`, is fixed by LE-gate34, not debt.) | `coinsEquiv`, `ofFn_coinsEquiv`; `exists_pkPredictor` | Open (deferred) | Ruling Seyoon 2026-11-15: ledger debt, disclosed (not fixed in the landing: reuse needs a new import and a definition change). Cleanup: replace `splitLen` by `(coinsEquiv h).symm`; publish `pkPredictor_apply` and re-derive the signed predictor from `exists_pkPredictor`; decide the promotion requests. G34-02 cleanup: promote `length_ofFn_coins` to the `NUPPT` layer (`Asymptotic/Adversary` or `Randomized/NonUniform`) and re-point both copies. |
| DL-49 | sc-compose fill (delivery review 2026-11-15, SC-F01; disclosed in the checkpoint REPORTs): helpers under `SecureComputation/ComposeSecurity/` restate public lemmas because the brief's two extra imports were read as exhaustive: a third `negligible_polyExpr_mul`; `appendCoins` (= `coinsEquiv`); `ofFn_blocks_symm` (= `FunFamily.ofFn_blocks_symm`); `polyTimeComputable_flatMap_range`, `flatMap_range_ite`, `iterSnd_poly`, `encodeMsgs_eq_flatMap`, `msgAt_encodeMsgs` and the `padTo` family (from `Composability/ZeroKnowledge/ThreeColoring/Machines.lean`). | `EnsembleLemmas.negligible_polyExpr_mul` (`Asymptotic/EnsemblesLemmas.lean:377`), `coinsEquiv`, `FunFamily.ofFn_blocks_symm`, the `ThreeColoring/Machines` helpers | Open (deferred) | Ruling Seyoon 2026-11-15: ledger debt. Cleanup: import the public lemmas (or promote the ThreeColoring helpers to a shared machine layer) and re-point the sc-compose copies proof-only. |

## ===== briefs/pass-shelat-ch5-8/fills/seq-zk/final-r1/landing/PROVENANCE.txt =====

seq-zk issued-r1 (PS10 Theorem 175.1: the five seqRep theorems) maintainer delivery review r1 (Codex lead + 3 sub-agents), 2026-11-16 UTC.
$SP = /tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad. Paths below are relative to this directory.
Method: the common review brief (Updates 1-3) as in derand-r1 (same tools); run after the derand review and the coordinator's jobs
  gate34-le / int-319, each of which restored dl-oleans-2 to 457ba704. Nothing pushed, no PR, records checkout only read.
  No lake build, no cache get. python3 -I. One Lean process at a time, only on $SP/dl-oleans-2.

brief: records fills/seq-zk/issued-r1/brief.md SHA-256 d8b9feeced5c7f2396705fee9439344c3d774e9641b19b358fa13f6f5b0046fc (= dispatch.md);
  package SHA256SUMS 7/7 OK (logs/issue-package-check.txt); SOURCE-SHA256SUMS 237/237 OK at the issue base
  107f1e8c218733eac12d6b9bee6fece441271317 (logs/source-sums-check.txt); base-sorries.txt 23 in 9 modules.
delivery: exchange a6be22fa168fcd0a40971383d8ffb3f1adb9731d ("fill seq-zk: final"); checkpoints d316d29a, 36f1896d, 65bc1c08. All four touch
  only inbox/fills/seq-zk/; nothing later touches it (logs/exchange-commits.txt). Unsigned, Seyoon's identity. Worker REPORT
  logs/worker-REPORT.md. The payload is 1.12 GB (3074 files): verified WITHOUT extraction by tools/gitmancheck.py (new; streams git
  blobs, exact path sets): logs/payload-check.txt top SHA256SUMS 3073/3073 OK, evidence/SHA256SUMS 3023/3023 OK, no missing/extra;
  logs/payload-inventory.sha256 lists every delivered file. Only REPORT, patches, src, scope-request and four small evidence files were
  extracted (fresh directory, removed after use); extracts in logs/delivery-extracts/.
integrity: logs/git-am-integrity.log: git am of the 6 patches at 107f1e8c, committer metadata from COMMITS.tsv, gpgsign false: all six
  hashes reproduce (a758032d, e978a282, 04c253e4, 5a80d36a, 7cecd426, d842dc8f681f6b89499129f5b64a50d0e4587935), tree
  718703de4ccc88cdbcbc3a3302c8a03790671483. COMMITS.tsv signing column: "unsigned; commit.gpgsign=false" x6. logs/src-equality.txt: the 41
  changed paths (SequentialZK.lean, 39 new SequentialZK/ helpers, M ZeroKnowledge/Defs.lean) equal src/, which holds exactly them.
  logs/defs-diff.txt: the Defs change is the 9-line StatZK_iff reader; its added lines equal the scope-request patch
  (logs/delivery-extracts/scope-request/StatZK-iff.patch) except the position of one blank line.
Codex host / sub-agents: evidence/subagents/{seq-zk-a,seq-zk-b,seq-zk-c} exist (221, 173, 222 files). logs/ownership-check.txt: the
  REPORT's ownership table assigns each of the 39 helpers to exactly one agent (lead 5, a 10, b 9, c 15); SequentialZK.lean and Defs
  are the lead's; the table is consistent with the delivered file set (not independently verifiable beyond the records).
  logs/final-sweep-attribution.txt: all 276 final-sweep checks (evidence/logs/sweep-final-01/results.jsonl, 12:49-13:20Z) match a
  lean_check_tree slot acquisition of the same module with the lead's tag (seq-zk). logs/slots-check.txt: never above 3 slots across
  the seq-zk tags. Preflight headroom 4.754 GiB >= 4.
landing: land/pass-shelat-seq-zk (local), worktree $SP/wt-land-seq-zk (sparse, briefs/ excluded; .lake/packages linked). Worker head
  d842dc8f rebased onto origin 05d26fe5b41fcb9426ec220d877d03264b9c8e8c (#314-#317 merged; records after): rc 0, the 41 files unchanged
  (landing/landing.log). FINAL head e9b5ea47a1c3dcd664caf2dbf308f89c1beffbb8, tree a6acdfbf697f8eb20d72f2ff1c7ead7b1ce01817; commits
  landing/commits.txt (6, author Seyoon kept, committer Claude, all SSH-signed), series landing/series/; 41 files +6491/-14
  (landing/changed-paths-vs-origin.txt). No landing edit.
build: order/ (downorder at e9b5ea47 vs eff2dcd0): changed 110 (69 base delta + 41 unit), down 303 = build-queue.txt (through root
  TCSlib and both audits/*/Checks). Backups tree/backed-up.txt (214), new tree/new-oleans.txt (89). build/: 303/303 rc 0, 0 errors in
  both forms, error substring 0, 1670 s (logs/build-summary.txt). Unit: SequentialZK 117.8 s, 1 warning (unused hQ, disclosed); the
  41 unit modules 213.5 s in all (logs/module-times.txt). tree/tree-check-head.txt (1288 modules, logs/records-head.jsonl): RESULT OK
  (after deleting the 165 probe oleans, logs/probe-oleans-deleted-head.txt).
statements (vs 107f1e8c): statements/frozen-check.txt: SequentialZK 27 -> 39 and Defs 35 -> 36 declarations, 0 header/prose/body
  differences; control (one header character of ZK.seqRep) exactly 1. decls2-vs-base.tsv: 196 ADDED, 0 CHANGED, 0 REMOVED.
  touched.tsv: 5 CHANGED (the targets), 13 ADDED in existing files (12 owned + StatZK_iff), 190 in new files, 57 UNCHANGED.
  sizes-widths.txt: 41 files, max 990 lines, max width 99, 0 over 100. No @[simp] (only @[simps (config := {isSimp := false})]).
  docaudit.tsv: 113 OK, 88 NO-FORMULA (prose descriptions of equations, or Prop statements without a relation symbol), 1 NO-DOC =
  prefixProver, whose docstring precedes its @[simps] attribute (tool artifact). sketchaudit: 48 proofs >= 15 lines, all sketched.
  logs/nameclash.txt: 0 exact clashes.
axioms: probe-sources/head/CensusHead.lean (tools/mkcensus_seqzk.py, new) -> probe-runs/: the five targets, PerfectZK.seqRep,
  PerfectZKAbort.seqRep, Composability.colSeq_efficientProverProof_zk, negligible_colSeqSound, StatZK_iff, zk_of_padded_spec:
  [propext, Classical.choice, Quot.sound]. logs/census-summary.txt: 414 stored constants (= the worker), axiom union standard, no
  sorryAx, no simp; one instance (PhaseMetadata.instNonempty, a Nonempty instance). Base (CensusBase on the restored tree):
  targets and the two consumers carry sorryAx. logs/census-base-vs-head.tsv: 107 -> 414, removed 0, type-changed 0, attr-changed 0,
  added 307 (231 named), axioms-changed 7.
admissions: logs/sorry-census.txt: issued 23 in 9 modules -> 18; only SequentialZK differs (5 -> 0); outside the order only
  SeedMajority (#312) and SpecialEncryptionMulti (#311), base delta.
Rule 10: collector -> probe-runs/; seals tools/mkseals_ab.py -> seals/{A,B}, tools/mkseals_coe.py -> seals-coe/{A,B} (SEAL_CHUNK=2200,
  no probe needed it: max 2068 requests); 154 probes seal-runs/ (10 coe probes byte-identical to strict not re-run,
  logs/seal-coe-identical.txt). logs/seal-head-*.tsv: every probe has install and EOF records; all pass except ZeroKnowledge/Defs:
  10 errors in A and B, strict and coe. Base (base-seals{,-coe}/, 8 probes base-seal-runs/, base worktree at 107f1e8c on the restored
  tree; logs/base-closure-vs-eff2dcd0.txt, base-owner-sources.txt: base sources and closures equal eff2dcd0): SequentialZK 0, Defs
  10 errors. logs/seal-defs-base-vs-head.txt: the same 6 failing declarations base and head (perfectZK_zeroRounds,
  AbortRetry.attempt_poly, exists_retrySimulator, statClose_retry, PerfectZKAbort.statZK, negligible_inv_pow_sqrt_div; base names
  mapped with base spans, statements/touched-base.json). New failing declarations: 0. StatZK_iff passes.
  Controls tools/mkctl_seqzk.py (new; rows PolyExpr.eval, FinDist CoeFun, ZK/ZK_iff, StatZK/StatZK_iff, Protocol.seqRep (not
  selected: no helper imports the owned file), Composability.prefixProver/prefixProver_coins) -> controls/ (10 probes, 9 negatives),
  controls-strict/ (14, 15), control-runs/: logs/ctlcheck.log ALL_OK True; strict: negatives each fail once, ctlCoeReader fails in the
  6 strict sealed probes (logs/controls-strict-attribution.txt). The sealed `Iff.rfl` form of StatZK fails and StatZK_iff passes:
  the approved reader is needed and sufficient.
  Explicit-unfold scan: scan/, logs/scan2-head.log: 1245 items; 13 "foreign" = local `let F`/`let g` bindings resolved by name to
  globals (logs/scan-foreign-attribution.txt): 0 real foreign definitions.
lint: lint/: Cryptography 92/101 at head and tip 05d26fe5; the only changed line: Defs' check-8 list loses StatZK (StatZK_iff).
  Complexity 25/391, identical.
content: the five targets are short instantiations: ZK.seqRep = zk_of_padded_spec h hB Q seqRep_proverSpec; StatZK.seqRep =
  statZK_of_padded_spec; InteractiveProof.seqRep from seqVerifier_efficient, PaddedProverSpec.complete and seqRep_sound_first (phase 0);
  InteractiveProofErr.seqRep from (seqRep_verifierSpec Q x).sound (hQ unused, disclosed); EfficientProverProofErr.seqRep adds
  seqProver_efficient, ProverBounded.seqRep and seqRep_complete. Statements frozen, kernel-checked, standard axioms: proved as stated.
  Target sketches rewritten to the delivered route (normalized simulator, conditional hybrids, Q·δ and Q·ε sums).
duplication: logs/duplication-review.txt (spot checks; nothing undisclosed found).
open PRs (logs/open-pr-overlap.txt): merge-tree of e9b5ea47 with #313, #318 (origin f62a25b3 and local LE-gate34 b0bad23a), #319 (origin
  and local 47daa907) and the derand landing 941b5a1e: all clean. None of their modules is downstream of the unit
  (order/unitdown/, 65 modules); shared downstream only root TCSlib and facades.
restore (restore/restore-log.txt, tools/restore.sh): 214 restored (0 hash failures), 89 new deleted: SNAPSHOT EQUAL; base probes then
  ran and their 6 probe oleans were deleted (restore/base-probe-oleans-deleted.txt). tree/snapshot-post-final.txt: 1230 files,
  457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f = snapshot-pre; tree/tree-check-post.txt RESULT OK.
cleanup: payload extract, backups (bk-seqzk), the base worktree removed; PlProbe/ removed from the landing worktree (clean at e9b5ea47).
SHA256SUMS: every file here except itself; ../seq-zk-r1-evidence.zip holds exactly the manifest's paths plus SHA256SUMS.

## ===== briefs/pass-shelat-ch5-8/maintainer/ledoc-derand-seqzk-2026-11-16/PROVENANCE.txt =====

LE-doc on two landing branches: derand F-04 (#326) and seq-zk S-02 (#327), maintainer job, 2026-11-16 UTC
$SP = /tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad. Paths below are relative to this directory.
Rules: python3 -I; no Lean run in this job (the edited files are compiled by the companion integration job, ../int-all-open/,
  see "build" below); nothing pushed; no commit or branch change in /home/user/tcslib (only `git fetch`); the two commits are
  on the existing local landing branches, in their worktrees $SP/wt-land-derand and $SP/wt-land-seq-zk (sparse, briefs/
  excluded, .lake/packages linked), author = committer = Claude <noreply@anthropic.com>, SSH-signed by the environment
  default (gpgsig present; `%G?` prints N only because no allowedSignersFile is configured), both trailers in the message.
Method and tools: the sc-compose final-r1 LE-doc (records fills/sc-compose/final-r1/review-evidence.zip, SHA-256
  c11ce8bb81d2ab7bf19259740f78c1dd2006d08e14e6672f9b257a131445a24b; extracted into a fresh directory, 850/850 OK against
  evidence-SHA256SUMS, SHA256SUMS = evidence-SHA256SUMS). tools-used/: unmodified copies of its tools/ docaudit.py, doconly.py,
  doconly_sg.py (the doc-only strip comparison), touched.py, frozencheck_lib.py, ledoc_sc.py, ledoc_list_sc.py, decls2.py,
  sizewidth.py (byte-equal to the derand and seq-zk reviews' copies of docaudit/touched/frozencheck_lib/decls2/sizewidth).
  New: ledoc_sqz.py (ledoc_sc.py keyed by docaudit's file:line through touched.json, frozen-target skip, an overrides file,
  a wrap that leaves room for the closing ` -/`), ledoc_derand.py (one exact replacement). Inputs: the derand review
  (fills/derand/final-r1/review-evidence.zip, ef0776d5b100fdb1b183d4f47a34e54fba70a8b099bd2998e759be4982f4cfcb, 1317/1317 OK)
  and the seq-zk review (fills/seq-zk/final-r1/review-evidence.zip, f9c394794fd7637237a274163a396eaa78452250c5e31abc5d2878b9e353392f,
  1106/1106 OK), both path sets exact, SHA256SUMS = evidence-SHA256SUMS.

pre-edit docaudit reproduced (statements/*-pre/): touched.py (issue base -> landing head) + docaudit.py on the landing worktree
  give touched.tsv and docaudit.tsv byte-identical to each review's statements/ (derand 01de2d8b -> 941b5a1e: 48 OK, 8 NO-FORMULA;
  seq-zk 107f1e8c -> e9b5ea47: 113 OK, 86 NO-FORMULA, 2 NO-FORMULA+LABEL, 1 NO-DOC).

derand F-04 (land/pass-shelat-derand, $SP/wt-land-derand)
  parent 941b5a1e5116b1ecf3afa56188abd88159389600 (= origin/land/pass-shelat-derand = refs/pull/326/head at the start)
  head   c27005d67298f79c785a4e8ac1648da0a67d3614, tree 7ea8bf7eebce9ed3be8403a80b96a1f79cc8216e
  subject "derand landing edit LE-doc: formula docstring for inBPP_iff (F-04)" (landing/derand-commit-msg.txt).
  Edit (tools-used/ledoc_derand.py; landing/derand-le-doc.diff, patch landing/derand-patch/): the Randomized.inBPP_iff docstring
  (TCSlib/Complexity/Randomized/Classes.lean) states the theorem's own statement, in the header's order,
  `InBPP E L ↔ ∃ (M : List Bool → List Bool → Bool) (a k : ℕ), E.Eff (boolVerifier M) ∧ ∀ x : List Bool, (x ∈ L → 2/3 ≤
  randProb (polyLen a k x.length) fun r => M x r = true) ∧ (x ∉ L → 2/3 ≤ randProb (polyLen a k x.length) fun r => M x r = false)`,
  with its [AB09, Definition 7.3] tag. It replaces the 4-line prose (whose content the formula states) by 4 lines, so the file
  stays at 1415 lines and its recorded size WARN line is unchanged; widths 91/85/88/75.
  Checks: checks/derand-doconly.txt (doconly_sg.py, doc and module comments stripped) and derand-doconly-plain.txt (doconly.py):
  code-identical True, docstrings 65->65 (64->64), 1 changed, max width 97: RESULT OK.
  statements/derand-post/: touched-vs-parent.tsv 1 CHANGED (inBPP_iff), 146 UNCHANGED; docaudit (01de2d8b -> c27005d6): 49 OK,
  7 NO-FORMULA = the review's 7 Prop formulas without a relation symbol (polyTimeComputable_* x6, eff_mapCoins; tool
  limitation); inBPP_iff OK.
  lint/: campaign_style_lint.py --check8b at c27005d6: Cryptography 92 FAIL / 101 WARN, Complexity 25 / 390; FAIL/WARN line
  sets identical to the review's landing-head lint (linediff-*-derand-review-vs-ledoc.txt empty).

seq-zk S-02 (land/pass-shelat-seq-zk, $SP/wt-land-seq-zk)
  parent e9b5ea47a1c3dcd664caf2dbf308f89c1beffbb8 (= origin/land/pass-shelat-seq-zk = refs/pull/327/head at the start)
  head   bd19c433a4cf3d4027ffc891d7d3c06e927e9dfa, tree cc520026f83524433328359af759084d23cabd0e
  subject "seq-zk landing edit LE-doc: formula docstrings for 81 new public declarations (S-02)" (landing/seq-zk-commit-msg.txt).
  DEVIATION from the requested subject ("88"): the review's 88 NO-FORMULA rows are not 88 new declarations. 5 of them are the
  frozen targets ZK.seqRep, StatZK.seqRep, InteractiveProof.seqRep, InteractiveProofErr.seqRep, EfficientProverProofErr.seqRep
  (status CHANGED, not new; the brief freezes their statements and statement prose: "Preserve the target statements, every
  other declaration, the statement prose"; the sc-compose LE-doc likewise skipped its frozen targets), and 2 new ones,
  Protocol.ProverBounded.seqRep and SequentialZK.zk_of_padded_spec, already state their conclusion in backticks
  (`(π.seqRep Q).ProverBounded R B`, `ZK ρ R`; flagged only because a Prop has no relation symbol). The other 81 are edited.
  If the maintainer wants the 5 target docstrings edited too, that is a separate frozen-prose decision (SequentialZK.lean would
  then be about 997-1000 lines).
  Edit (tools-used/ledoc_sqz.py --apply; plan landing/seq-zk-le-doc-plan.tsv: 81 INSERT, 5 SKIP-frozen-target,
  2 SKIP-already-stated; diff landing/seq-zk-le-doc.diff, stat .stat, patch landing/seq-zk-patch/): for each of the 81, the
  declaration's own Lean conclusion (the header after the first depth-0 ':' following the binders; 60 rows) or, for a
  def/abbrev whose type is not a relation, its `_eq` reader's conclusion (13 rows), added as "`<formula>`." at the end of the
  statement prose (before **Proof sketch** when present). 8 are given by hand (statements/seq-zk-overrides.tsv) because the
  scanner cannot read them: the PhaseMetadata Nonempty instance (anonymous), the `let` bodies of phasePrefix_succ_simulate,
  exists_phaseSimulator and phaseStep_eq (written `let a := …; …`), phaseSuffix and phaseSuffix_eq (the `match`),
  phaseVerifier (its _eq reader's structure instance, with the field comma) and the Prop structure PaddedVerifierSpec (its
  first three field equations). 11 extracted conclusions longer than 240 characters are cut at a space and end in " …" (the
  sc-compose rule). 23 files (22 under Composability/SequentialZK*, plus ZeroKnowledge/Defs.lean for StatZK_iff, the S-01
  addition to the frozen file: docstring only), +219/-61 lines (the -61 are the old last prose lines, re-emitted unchanged
  before the inserted formula).
  Checks: checks/seq-zk-doconly.txt (doconly_sg.py) and seq-zk-doconly-plain.txt (doconly.py): all 23 files code-identical
  True, docstring counts unchanged, 81 docstrings changed in all, max width 100: RESULT OK. Sizes: largest file
  SequentialZK.lean 990 -> 992 lines; no line over 100 characters; added lines checked for Markdown block starters and
  comment delimiters (none).
  statements/seq-zk-post/: touched-vs-parent.tsv 81 CHANGED, 184 UNCHANGED (exactly the plan's 81). docaudit (107f1e8c ->
  bd19c433): 190 OK, 2 LABEL (continuationProb_eq, phaseGap_eq: "defining equation" wording, the equation now stated),
  1 NO-DOC (prefixProver: docstring before @[simps], tool artifact, as in the review), 9 NO-FORMULA = the 5 frozen targets,
  the 2 already-stated ones, and 2 edited rows whose formula is a Prop without a relation symbol (the instance's
  `Nonempty (PhaseMetadata n a v q h)`, statClose_step's `StatClose (realStep …) (simStep …) δ`; tool limitation).
  lint/: at bd19c433 Cryptography 92/101, Complexity 25/391; FAIL/WARN line sets identical to the review's landing-head lint.

build: both heads are compiled in ../int-all-open/ (the combined trees e2e26b9e and final 639d16d9 hold c27005d6's 15 and
  bd19c433's 41 files byte-for-byte): Classes.lean and the 23 edited seq-zk files rc 0, 0 errors (both forms), 0 sorry;
  warnings only Classes 2 (lines 586, 1302: the linter warnings of the unchanged code, as in the derand review) and
  SequentialZK 1 (the disclosed unused hQ). The separate tip+#326 and tip+#327 checks there rebuilt the same 24 modules at the
  tip-merged sources: rc 0, oleans byte-identical to the combined build's.
worktrees: both clean at the new heads (checks/*-worktree-status.txt empty); left in place (they are the landing worktrees).
SHA256SUMS: every file here except itself (paths without "./"); ../ledoc-derand-seqzk-evidence.zip holds exactly these paths
  plus SHA256SUMS.

## ===== briefs/pass-shelat-ch5-8/gates/39-seq-zk/pr-description.md =====

This is the landing PR for the Pass–shelat `seq-zk` fill, a Codex lead with three sub-agents. It proves all five `seqRep` theorems of [PS10, Theorem 175.1] and [Gol01, §4.3.4] in `Composability/SequentialZK.lean`: `ZK.seqRep`, `StatZK.seqRep`, `InteractiveProof.seqRep`, `InteractiveProofErr.seqRep` and `EfficientProverProofErr.seqRep`.

**Head:** `e9b5ea47a1c3dcd664caf2dbf308f89c1beffbb8`.
**Base:** `cryptography/pass-shelat-ch2-4` at `05d26fe5`.

## What changes
41 Lean files, +6491/−14:
- the owned `SequentialZK.lean`;
- 39 new helpers under `SequentialZK/`;
- `ZeroKnowledge/Defs.lean`, +9 lines: the `Iff.rfl` reader `StatZK_iff`. Seyoon approved this reader, and confirmed the approval on 2026-11-16 (S-01).

Each target is a thin instantiation of the helper theorems. `REPORT.md` assigns each helper to exactly one agent, and the lead ran the final sweep.

**Commits:** six Codex worker commits. A formula-docstring landing edit (S-02, 88 declarations) will follow before the gate.

## Review
The record is `briefs/pass-shelat-ch5-8/fills/seq-zk/final-r1/review.md`. Verdict: **ACCEPT**.
- **Statements:** the header, prose and definition-body checks show 0 differences. decls2 gives 196 ADDED, 0 CHANGED.
- **Axioms:** the five targets, `PerfectZK.seqRep`, `PerfectZKAbort.seqRep` and the `ThreeColoring` consumers use only the standard axioms. There are 414 stored constants, none with `sorryAx`.
- **Build:** 303 modules give rc 0, 0 errors. The whole-tree check covers 1288 modules: OK.
- **Rule 10:** 154 seal runs. The only failures are in `Defs`, in the same 6 declarations that already fail at base, so 0 new failing declarations. `StatZK_iff` is clean.
- **Admissions:** 23 → 18.
- **Lint:** unchanged.

A Codex gate follows. Seyoon merges.

---
_Generated by [Claude Code](https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA)_

## ===== briefs/pass-shelat-ch5-8/gates/39-seq-zk/pr.diff.txt =====

diff --git a/TCSlib/Cryptography/Composability/SequentialZK.lean b/TCSlib/Cryptography/Composability/SequentialZK.lean
index d966b6f11..fb38ff2fe 100644
--- a/TCSlib/Cryptography/Composability/SequentialZK.lean
+++ b/TCSlib/Cryptography/Composability/SequentialZK.lean
@@ -5,13 +5,53 @@ Released under Apache 2.0 license as described in the file LICENSE.
 import TCSlib.Cryptography.Asymptotic.Adversary
 import TCSlib.Cryptography.ZeroKnowledge.Defs
 import TCSlib.Cryptography.ZeroKnowledge.InteractiveProofs
+import TCSlib.Cryptography.Composability.SequentialZK.Advice
+import TCSlib.Cryptography.Composability.SequentialZK.BoundedMetadata
+import TCSlib.Cryptography.Composability.SequentialZK.ComputationalAdvice
+import TCSlib.Cryptography.Composability.SequentialZK.ComputationalHybrid
+import TCSlib.Cryptography.Composability.SequentialZK.ComputationalPhaseBound
+import TCSlib.Cryptography.Composability.SequentialZK.ComputationalReduction
+import TCSlib.Cryptography.Composability.SequentialZK.ComputationalTransfer
+import TCSlib.Cryptography.Composability.SequentialZK.Congruence
+import TCSlib.Cryptography.Composability.SequentialZK.ContinuationProbability
+import TCSlib.Cryptography.Composability.SequentialZK.Efficiency
+import TCSlib.Cryptography.Composability.SequentialZK.EndpointSampling
+import TCSlib.Cryptography.Composability.SequentialZK.ErrSoundness
+import TCSlib.Cryptography.Composability.SequentialZK.ExecutionBounds
+import TCSlib.Cryptography.Composability.SequentialZK.HybridRecursion
+import TCSlib.Cryptography.Composability.SequentialZK.Normalization
+import TCSlib.Cryptography.Composability.SequentialZK.NormalizationMachine
+import TCSlib.Cryptography.Composability.SequentialZK.NormalizedStep
+import TCSlib.Cryptography.Composability.SequentialZK.PaddedProverSpec
+import TCSlib.Cryptography.Composability.SequentialZK.PhaseView
+import TCSlib.Cryptography.Composability.SequentialZK.Phases
+import TCSlib.Cryptography.Composability.SequentialZK.PrefixFolds
+import TCSlib.Cryptography.Composability.SequentialZK.PrefixLaws
+import TCSlib.Cryptography.Composability.SequentialZK.ProofTransfers
+import TCSlib.Cryptography.Composability.SequentialZK.RealPhases
+import TCSlib.Cryptography.Composability.SequentialZK.RealPrefixBounds
+import TCSlib.Cryptography.Composability.SequentialZK.ReductionAdvantage
+import TCSlib.Cryptography.Composability.SequentialZK.RepeatedSoundness
+import TCSlib.Cryptography.Composability.SequentialZK.RepeatedVerifier
+import TCSlib.Cryptography.Composability.SequentialZK.SimulatorMachine
+import TCSlib.Cryptography.Composability.SequentialZK.Soundness
+import TCSlib.Cryptography.Composability.SequentialZK.Statistical
+import TCSlib.Cryptography.Composability.SequentialZK.StatisticalPostprocess
+import TCSlib.Cryptography.Composability.SequentialZK.StatisticalPrefix
+import TCSlib.Cryptography.Composability.SequentialZK.StatisticalRecursion
+import TCSlib.Cryptography.Composability.SequentialZK.StatisticalTransfer
+import TCSlib.Cryptography.Composability.SequentialZK.SuffixLaws
+import TCSlib.Cryptography.Composability.SequentialZK.SuffixMachine
+import TCSlib.Cryptography.Composability.SequentialZK.VerifierPrefix
+import TCSlib.Cryptography.Composability.SequentialZK.WrappedVerifier
+import TCSlib.Cryptography.Asymptotic.ReductionSupport
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
 set_option autoImplicit false
 
 /-!
-# Sequential composition of zero-knowledge proofs (statement phase)
+# Sequential composition of zero-knowledge proofs
 
 [PS10, Theorem 175.1]: if `(P, V)` is a perfect or computational zero-knowledge proof for `L`
 and `Q` is a polynomial, the protocol `(P_Q, V_Q)` that runs `(P, V)` on the common input `x`
@@ -61,6 +101,48 @@ the `2k` moves `2kj, …, 2kj + 2k − 1`.
 - **At least one phase** for soundness: with `Q(n) = 0`, `V_Q` accepts everything, so the
   interactive-proof statement assumes `1 ≤ Q(n)`.
 
+## Contents
+
+* `SequentialZK.Advice`: uniform finite selectors.
+* `SequentialZK.BoundedMetadata`: finite bounded phase advice.
+* `SequentialZK.ComputationalAdvice`: uniform negligible selectors.
+* `SequentialZK.ComputationalHybrid`: conditional computational gaps and endpoints.
+* `SequentialZK.ComputationalPhaseBound`: a common negligible phase bound.
+* `SequentialZK.ComputationalReduction`: efficient advised continuation machines.
+* `SequentialZK.ComputationalTransfer`: computational zero-knowledge transfer.
+* `SequentialZK.Congruence`: reached-history execution congruence.
+* `SequentialZK.ContinuationProbability`: continuation acceptance and drift.
+* `SequentialZK.Efficiency`: phase and verdict machines.
+* `SequentialZK.EndpointSampling`: coin and view endpoint equivalences.
+* `SequentialZK.ErrSoundness`: acceptance bounds from soundness.
+* `SequentialZK.ExecutionBounds`: bounded real messages.
+* `SequentialZK.HybridRecursion`: conditional finite hybrid bounds.
+* `SequentialZK.Normalization`: bounded message slots.
+* `SequentialZK.NormalizationMachine`: normalization machines.
+* `SequentialZK.NormalizedStep`: one normalized phase comparison.
+* `SequentialZK.PaddedProverSpec`: the repeated-prover contract.
+* `SequentialZK.PhaseView`: canonical view validation.
+* `SequentialZK.Phases`: fixed-prefix phase executions.
+* `SequentialZK.PrefixFolds`: typed phase-prefix samplers.
+* `SequentialZK.PrefixLaws`: phase-fold recursion equations.
+* `SequentialZK.ProofTransfers`: bounded completeness transfer.
+* `SequentialZK.RealPhases`: real and filler phase endpoints.
+* `SequentialZK.RealPrefixBounds`: bounded actual real prefixes.
+* `SequentialZK.ReductionAdvantage`: typed reduction comparisons.
+* `SequentialZK.RepeatedSoundness`: the exact power soundness bound.
+* `SequentialZK.RepeatedVerifier`: the repeated-verifier contract.
+* `SequentialZK.SimulatorMachine`: the uniform normalized simulator.
+* `SequentialZK.Soundness`: execution prefixes and adaptive probability.
+* `SequentialZK.Statistical`: averaging and finite chains.
+* `SequentialZK.StatisticalPostprocess`: statistical mapping and marginalization.
+* `SequentialZK.StatisticalPrefix`: normalized prefix comparisons.
+* `SequentialZK.StatisticalRecursion`: linear error accumulation.
+* `SequentialZK.StatisticalTransfer`: statistical zero-knowledge transfer.
+* `SequentialZK.SuffixLaws`: normalized suffix equations.
+* `SequentialZK.SuffixMachine`: strict-PPT normalized suffix simulation.
+* `SequentialZK.VerifierPrefix`: prefix tape dependence.
+* `SequentialZK.WrappedVerifier`: the deterministic phase verifier.
+
 ## Main definitions
 
 * `Composability.proverMoveIndex`, `Composability.verifierMoveIndex`,
@@ -75,15 +157,16 @@ the `2k` moves `2kj, …, 2kj + 2k − 1`.
   position.
 * `Protocol.seqRep_exec_phase`: phase `j` of an honest execution of `π.seqRep Q` is an execution
   of `π` with the coin slices `j`.
-* `ZK.seqRep`, `StatZK.seqRep` (Thm 175.1, stated; `sorry`s under the source's sketch), and
-  `PerfectZK.seqRep` (proved from `StatZK.seqRep`).
+* `ZK.seqRep` (Thm 175.1, proved): computational zero knowledge composes sequentially.
+* `StatZK.seqRep` (proved): statistical error composes as `Q · δ`;
+  `PerfectZK.seqRep` is proved from it at zero error.
 * `PerfectZKAbort.seqRep`: the aborting case, derived from `PerfectZKAbort.statZK` and
   `StatZK.seqRep`, with error `Q(n) · 2^{-n}`.
-* `InteractiveProof.seqRep` (stated; a `sorry` under its sketch): the repetition is an
-  interactive proof.
-* `InteractiveProofErr.seqRep`, `EfficientProverProofErr.seqRep` (stated; `sorry`s under their
-  sketches): sequential repetition multiplies the soundness error, `s ↦ s^Q` (ruling G3-7d, for
-  the text's form of Thm 124.1).
+* `InteractiveProof.seqRep` (proved): sequential repetition with at least one phase preserves
+  interactive proofs, using the same negligible soundness bound.
+* `InteractiveProofErr.seqRep`, `EfficientProverProofErr.seqRep` (proved): sequential
+  repetition multiplies the soundness error, `s ↦ s^Q` (ruling G3-7d, for the text's form of
+  Thm 124.1).
 
 ## References
 
@@ -185,6 +268,23 @@ theorem verifierMoveIndex_exec (P V : Strategy) (vFirst : Bool) (x zP zV rP rV :
   rw [exec_snd_length, countP_not_moverIsV]
   cases vFirst <;> simp [moverIsV_true, moverIsV_false, verifierMoveIndex] at hg ⊢ <;> omega
 
+/-- For `P,V,vFirst,x,zP,zV,rP,rV,k,j`, each party has received exactly `j*k` messages
+at move `2*k*j`: both components of `exec P V vFirst x zP zV rP rV (2*k*j)` have length
+`j*k`. [PS10, Theorem 175.1, padded-phase boundaries].
+`(exec P V vFirst x zP zV rP rV (2 * k * j)).1.length = j * k ∧ (exec P V vFirst x zP zV rP rV (2 *
+k * j)).2.length = j * k`. -/
+theorem exec_boundary_lengths (P V : Strategy) (vFirst : Bool)
+    (x zP zV rP rV : List Bool) (k j : ℕ) :
+    (exec P V vFirst x zP zV rP rV (2 * k * j)).1.length = j * k ∧
+      (exec P V vFirst x zP zV rP rV (2 * k * j)).2.length = j * k := by
+  constructor
+  · rw [exec_fst_length, countP_moverIsV,
+      show 2 * k * j = 2 * (j * k) by ring]
+    cases vFirst <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega
+  · rw [exec_snd_length, countP_not_moverIsV,
+      show 2 * k * j = 2 * (j * k) by ring]
+    cases vFirst <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega
+
 end Composability
 
 open Composability
@@ -263,6 +363,19 @@ theorem seqRep_rounds_eval (π : Protocol) (Q : PolyExpr) (n : ℕ) :
   simp [seqRep, PolyExpr.eval_mul, PolyExpr.eval_const]
   ring
 
+/-- The repeated prover keeps the message bound: `π.ProverBounded R B` implies
+`(π.seqRep Q).ProverBounded R B`, since every real reply is an original reply and every
+filler reply is empty. [PS10, Theorem 175.1]. -/
+theorem ProverBounded.seqRep {π : Protocol} {R : List Bool → List Bool → Prop}
+    {B : PolyExpr} (hB : π.ProverBounded R B) (Q : PolyExpr) :
+    (π.seqRep Q).ProverBounded R B := by
+  rw [proverBounded_iff] at hB ⊢
+  intro x y r hist hxy
+  rw [seqRep_P, seqProver_next]
+  split_ifs
+  · exact hB x y _ _ hxy
+  · exact Nat.zero_le _
+
 /-- **Phase `j` of an honest execution of the repetition is an execution of `π`** with the coin
 slices `j`: after the `j` earlier phases and the `k` real moves of phase `j`, the messages each
 party received in phase `j` are those it receives in `π` with those coins.
@@ -362,6 +475,351 @@ theorem seqRep_exec_phase (π : Protocol) (Q : PolyExpr) (x y z rP rV : List Boo
       simp only [seqProver, ← hk, ← hvF]
       rw [hidx, hmod, if_pos htk, hdiv, ih₁]
 
+/-- Up to `t ≤ π.rounds.eval |x|`, the repeated verifier against any prover `P'` has the
+same execution as the original verifier on coin block zero, provided `1 ≤ Q.eval |x|`.
+
+**Proof sketch.** Induct on the real move index. The received history has length at most
+that index, so it cannot trigger the repeated verdict. At a verifier move the recovered
+index is the move index, its phase is zero, and its residue is the index itself. Thus the
+same original verifier reply is appended. Prover moves agree because their histories agree.
+-/
+theorem seqVerifier_exec_first (π : Protocol) (Q : PolyExpr) (P' : Strategy)
+    (x y z rP rV : List Bool) (hQ : 1 ≤ Q.eval x.length) {t : ℕ}
+    (ht : t ≤ π.rounds.eval x.length) :
+    exec P' (π.seqVerifier Q) π.verifierFirst x y z rP rV t =
+      exec P' π.V π.verifierFirst x y z rP (coinBlock (π.V.coinLen x.length) 0 rV) t := by
+  -- Induct through the first phase, keeping both received histories synchronized.
+  induction t with
+  | zero => rw [exec_zero, exec_zero]
+  | succ t ih =>
+    have htk : t < π.rounds.eval x.length := by omega
+    rw [exec_succ, exec_succ, ih (by omega)]
+    by_cases hm : moverIsV π.verifierFirst t = true
+    · simp only [hm, if_true]
+      -- The active move count excludes the aggregate-verdict branch in this prefix.
+      have hl := exec_length P' π.V π.verifierFirst x y z rP
+        (coinBlock (π.V.coinLen x.length) 0 rV) t
+      have hkQ : π.rounds.eval x.length ≤ Q.eval x.length * π.rounds.eval x.length := by
+        simpa only [one_mul] using Nat.mul_le_mul_right (π.rounds.eval x.length) hQ
+      have hne : (exec P' π.V π.verifierFirst x y z rP
+          (coinBlock (π.V.coinLen x.length) 0 rV) t).2.length ≠
+            Q.eval x.length * π.rounds.eval x.length := by omega
+      have hidx := verifierMoveIndex_exec P' π.V π.verifierFirst x y z rP
+        (coinBlock (π.V.coinLen x.length) 0 rV) t hm
+      have hn : (π.seqVerifier Q).next x z rV
+          (exec P' π.V π.verifierFirst x y z rP
+            (coinBlock (π.V.coinLen x.length) 0 rV) t).2 =
+          π.V.next x z (coinBlock (π.V.coinLen x.length) 0 rV)
+            (exec P' π.V π.verifierFirst x y z rP
+              (coinBlock (π.V.coinLen x.length) 0 rV) t).2 := by
+        rw [seqVerifier_next, if_neg hne, hidx,
+          Nat.mod_eq_of_lt (by omega), if_pos htk, Nat.div_eq_of_lt (by omega),
+          Nat.zero_mul, List.drop_zero]
+      rw [hn]
+    · simp only [hm, Bool.false_eq_true, if_false]
+
+/-- The repeated output is the aggregate verdict on the final received history:
+`(π.seqRep Q).outV P' x y z r = π.seqVerdict (Q.eval |x|) x z (List.ofFn r.2) hist`,
+where `hist` is the verifier component of the repeated transcript.
+
+**Proof sketch.** There are exactly `Q(|x|) · k` prover moves in the even-length repeated
+execution. This is the terminal-history test in the repeated verifier, so its terminal
+branch computes the aggregate verdict. -/
+theorem seqRep_outV_eq (π : Protocol) (Q : PolyExpr) (P' : Strategy)
+    (x y z : List Bool) (r : (π.seqRep Q).ExecCoins P' x) :
+    (π.seqRep Q).outV P' x y z r =
+      π.seqVerdict (Q.eval x.length) x z (List.ofFn r.2)
+        ((π.seqRep Q).transcriptWith P' x y z r).2 := by
+  have hl : ((π.seqRep Q).transcriptWith P' x y z r).2.length =
+      Q.eval x.length * π.rounds.eval x.length := by
+    rw [transcriptWith_eq, exec_snd_length, countP_not_moverIsV,
+      seqRep_rounds_eval, seqRep_verifierFirst]
+    rw [show 2 * π.rounds.eval x.length * Q.eval x.length =
+      2 * (Q.eval x.length * π.rounds.eval x.length) by ring]
+    cases π.verifierFirst <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega
+  rw [outV_eq]
+  have hn := congrArg (fun V : Strategy => V.next x z (List.ofFn r.2)
+    ((π.seqRep Q).transcriptWith P' x y z r).2) (seqRep_V π Q)
+  dsimp only at hn
+  rw [hn, seqVerifier_next, if_pos hl]
+
+/-- The final repeated history restricted to the real prover slots of phase `j < Q(|x|)`
+is the original verifier history on coin slices `j`. [PS10, Theorem 175.1].
+
+**Proof sketch.** The history just after the phase's real moves is a prefix of the final
+history. Its length is the `j · k` slots of preceding phases plus the number of real prover
+moves. Taking this prefix and dropping the preceding phases recovers the phase reader.
+-/
+theorem seqRep_exec_phase_take (π : Protocol) (Q : PolyExpr) (x y z rP rV : List Bool)
+    {j : ℕ} (hj : j < Q.eval x.length) :
+    ((exec (π.seqRep Q).P (π.seqRep Q).V π.verifierFirst x y z rP rV
+      (2 * π.rounds.eval x.length * Q.eval x.length)).2.drop
+        (j * π.rounds.eval x.length)).take
+          (proverMoves π.verifierFirst (π.rounds.eval x.length)) =
+      (exec π.P π.V π.verifierFirst x y z (coinBlock (π.P.coinLen x.length) j rP)
+        (coinBlock (π.V.coinLen x.length) j rV) (π.rounds.eval x.length)).2 := by
+  let k := π.rounds.eval x.length
+  have hjk := Nat.mul_le_mul_right k hj
+  have hle : 2 * k * j + k ≤ 2 * k * Q.eval x.length := by
+    have hscaled := Nat.mul_le_mul_left 2 hjk
+    rw [show 2 * ((j + 1) * k) = 2 * k * j + 2 * k by ring,
+      show 2 * (Q.eval x.length * k) = 2 * k * Q.eval x.length by ring] at hscaled
+    omega
+  have hl : (exec (π.seqRep Q).P (π.seqRep Q).V π.verifierFirst x y z rP rV
+      (2 * k * j + k)).2.length = j * k + proverMoves π.verifierFirst k := by
+    rw [exec_snd_length, countP_not_moverIsV, proverMoves_eq, countP_not_moverIsV]
+    rw [show 2 * k * j + k = 2 * (j * k) + k by ring]
+    cases π.verifierFirst <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega
+  have hp := exec_snd_take (π.seqRep Q).P (π.seqRep Q).V π.verifierFirst x y z rP rV
+    (2 * k * j + k) (2 * k * Q.eval x.length - (2 * k * j + k))
+  rw [Nat.add_sub_of_le hle, hl] at hp
+  rw [List.take_drop, hp]
+  exact (seqRep_exec_phase π Q x y z rP rV hj).2
+
+/-- Perfect completeness on `x, y, z` is preserved by every number of sequential phases:
+if `Pr[π.outV π.P x y z = [true]] = 1`, then
+`Pr[(π.seqRep Q).outV (π.seqRep Q).P x y z = [true]] = 1`.
+[PS10, Theorem 175.1].
+
+**Proof sketch.** Probability one on the finite coin space means every original coin pair
+accepts. For each repeated coin pair and phase, its coin slices have the original lengths.
+The phase-history reader therefore identifies its verdict with an accepting original run.
+All phase tests are true, so the aggregate output is true, including an empty phase list.
+-/
+theorem seqRep_complete (π : Protocol) (Q : PolyExpr) (x y z : List Bool)
+    (hc : uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1) :
+    uprob (fun r : (π.seqRep Q).ExecCoins (π.seqRep Q).P x =>
+      (π.seqRep Q).outV (π.seqRep Q).P x y z r = [true]) = 1 := by
+  -- Reduce completeness to pointwise acceptance on every repeated coin tape.
+  apply HardcoreBit.uprob_eq_one_of_forall
+  intro r
+  rw [seqRep_outV_eq, seqVerdict_eq]
+  have hall : (List.range (Q.eval x.length)).all (fun j => decide
+      (π.V.next x z (coinBlock (π.V.coinLen x.length) j (List.ofFn r.2))
+        ((((π.seqRep Q).transcriptWith (π.seqRep Q).P x y z r).2.drop
+          (j * π.rounds.eval x.length)).take
+            (proverMoves π.verifierFirst (π.rounds.eval x.length))) = [true])) = true := by
+    rw [List.all_eq_true]
+    intro j hj
+    have hjQ : j < Q.eval x.length := List.mem_range.mp hj
+    apply decide_eq_true
+    rw [transcriptWith_eq, seqRep_verifierFirst, seqRep_rounds_eval,
+      seqRep_exec_phase_take π Q x y z (List.ofFn r.1) (List.ofFn r.2) hjQ]
+    -- Each phase uses original-length tapes, so the base acceptance fact applies.
+    have hlP : (List.ofFn r.1).length = Q.eval x.length * π.P.coinLen x.length := by
+      rw [List.length_ofFn, Strategy.coinLen_eq, seqRep_P, seqProver_coins,
+        PolyExpr.eval_mul, Strategy.coinLen_eq]
+    have hlV : (List.ofFn r.2).length = Q.eval x.length * π.V.coinLen x.length := by
+      rw [List.length_ofFn, Strategy.coinLen_eq, seqRep_V, seqVerifier_coins,
+        PolyExpr.eval_mul, Strategy.coinLen_eq]
+    have hbP : (coinBlock (π.P.coinLen x.length) j (List.ofFn r.1)).length =
+        π.P.coinLen x.length := length_coinBlock (by
+      rw [hlP]; exact Nat.mul_le_mul_right _ hjQ)
+    have hbV : (coinBlock (π.V.coinLen x.length) j (List.ofFn r.2)).length =
+        π.V.coinLen x.length := length_coinBlock (by
+      rw [hlV]; exact Nat.mul_le_mul_right _ hjQ)
+    have hrun := HardcoreBit.forall_of_uprob_eq_one hc
+      (padFin (π.P.coinLen x.length) (coinBlock (π.P.coinLen x.length) j (List.ofFn r.1)),
+       padFin (π.V.coinLen x.length) (coinBlock (π.V.coinLen x.length) j (List.ofFn r.2)))
+    rw [outV_eq, transcriptWith_eq, ofFn_padFin_of_length hbP,
+      ofFn_padFin_of_length hbV] at hrun
+    exact hrun
+  rw [hall]
+  rfl
+
+/-- If the original verifier rejects phase zero against `P'`, then the repeated verifier
+rejects the same repeated tape, when `1 ≤ Q.eval |x|`. [PS10, Theorem 175.1].
+
+**Proof sketch.** The first real phase agrees with the original verifier on coin block zero.
+Its prover-message history is the initial segment of the final history. Rejection therefore
+makes the phase-zero test in the aggregate conjunction false, forcing the repeated output
+to be `[false]`. -/
+theorem seqRep_reject_of_first (π : Protocol) (Q : PolyExpr) (P' : Strategy)
+    (x y z : List Bool) (r : (π.seqRep Q).ExecCoins P' x) (hQ : 1 ≤ Q.eval x.length)
+    (hr : π.V.next x z (coinBlock (π.V.coinLen x.length) 0 (List.ofFn r.2))
+      (exec P' π.V π.verifierFirst x y z (List.ofFn r.1)
+        (coinBlock (π.V.coinLen x.length) 0 (List.ofFn r.2))
+        (π.rounds.eval x.length)).2 = [false]) :
+    (π.seqRep Q).outV P' x y z r = [false] := by
+  -- Compare the first real phase with its prefix in the complete transcript.
+  let k := π.rounds.eval x.length
+  have hkQ : k ≤ Q.eval x.length * k := by
+    simpa only [one_mul] using Nat.mul_le_mul_right k hQ
+  have hle : k ≤ 2 * k * Q.eval x.length := by
+    have hscaled := Nat.mul_le_mul_left 2 hkQ
+    rw [show 2 * (Q.eval x.length * k) = 2 * k * Q.eval x.length by ring] at hscaled
+    omega
+  have hp := exec_snd_take P' (π.seqVerifier Q) π.verifierFirst x y z
+    (List.ofFn r.1) (List.ofFn r.2) k (2 * k * Q.eval x.length - k)
+  rw [Nat.add_sub_of_le hle,
+    seqVerifier_exec_first π Q P' x y z (List.ofFn r.1) (List.ofFn r.2) hQ le_rfl] at hp
+  have hl : (exec P' π.V π.verifierFirst x y z (List.ofFn r.1)
+      (coinBlock (π.V.coinLen x.length) 0 (List.ofFn r.2)) k).2.length =
+        proverMoves π.verifierFirst k := by
+    rw [exec_snd_length, proverMoves_eq]
+  rw [hl] at hp
+  rw [seqRep_outV_eq, seqVerdict_eq]
+  -- A failed initial phase test makes the aggregate conjunction false.
+  have hnot : (List.range (Q.eval x.length)).all (fun j => decide
+      (π.V.next x z (coinBlock (π.V.coinLen x.length) j (List.ofFn r.2))
+        ((((π.seqRep Q).transcriptWith P' x y z r).2.drop (j * k)).take
+          (proverMoves π.verifierFirst k)) = [true])) ≠ true := by
+    intro hall
+    have hz := List.all_eq_true.mp hall 0 (List.mem_range.mpr hQ)
+    simp only [Nat.zero_mul, List.drop_zero] at hz
+    rw [transcriptWith_eq, seqRep_verifierFirst, seqRep_rounds_eval] at hz
+    have hpV := congrArg (fun V : Strategy =>
+      (exec P' V π.verifierFirst x y z (List.ofFn r.1) (List.ofFn r.2)
+        (2 * k * Q.eval x.length)).2.take (proverMoves π.verifierFirst k)) (seqRep_V π Q)
+    dsimp only at hpV
+    rw [hpV.trans hp, hr] at hz
+    contradiction
+  rw [if_neg hnot]
+
+/-- The repeated rejection probability dominates the original rejection probability on
+phase zero, against the same prover `P'`, when `1 ≤ Q.eval |x|`.
+[PS10, Theorem 175.1].
+
+**Proof sketch.** Restrict the repeated verifier's uniform tape to its initial original-length
+prefix; this map preserves uniformity and leaves the prover's tape unchanged. Original
+rejection on this projection implies repeated rejection by the first-phase reader, so
+monotonicity of probability gives the bound. -/
+theorem seqRep_sound_first (π : Protocol) (Q : PolyExpr) (P' : Strategy)
+    (x y z : List Bool) (hQ : 1 ≤ Q.eval x.length) :
+    uprob (fun r : π.ExecCoins P' x => π.outV P' x y z r = [false]) ≤
+      uprob (fun r : (π.seqRep Q).ExecCoins P' x =>
+        (π.seqRep Q).outV P' x y z r = [false]) := by
+  have hlen : (π.seqRep Q).V.coinLen x.length =
+      Q.eval x.length * π.V.coinLen x.length := by
+    rw [Strategy.coinLen_eq, seqRep_V, seqVerifier_coins, PolyExpr.eval_mul,
+      Strategy.coinLen_eq]
+  have hcle : π.V.coinLen x.length ≤ (π.seqRep Q).V.coinLen x.length := by
+    rw [hlen]
+    simpa only [one_mul] using Nat.mul_le_mul_right (π.V.coinLen x.length) hQ
+  let f : (π.seqRep Q).ExecCoins P' x → π.ExecCoins P' x :=
+    fun r => (r.1, fun i => r.2 (Fin.castLE hcle i))
+  have hf : HardcoreBit.PushesUniform f := HardcoreBit.pushesUniform_id.prodMap
+    (HardcoreBit.pushesUniform_restrict (Fin.castLE_injective hcle))
+  calc
+    _ = uprob (fun r : (π.seqRep Q).ExecCoins P' x =>
+        π.outV P' x y z (f r) = [false]) := (hf.uprob_eq _).symm
+    _ ≤ _ := uprob_mono fun r hr => by
+      apply seqRep_reject_of_first π Q P' x y z r hQ
+      rw [outV_eq, transcriptWith_eq] at hr
+      change π.V.next x z (List.ofFn (fun i => r.2 (Fin.castLE hcle i)))
+        (exec P' π.V π.verifierFirst x y z (List.ofFn r.1)
+          (List.ofFn (fun i => r.2 (Fin.castLE hcle i)))
+          (π.rounds.eval x.length)).2 = [false] at hr
+      rw [← take_ofFn_castLE hcle r.2] at hr
+      simpa only [coinBlock_eq, Nat.zero_mul, List.drop_zero] using hr
+
+/-- An efficient original prover gives an efficient sequential prover:
+`π.P.Efficient → (π.seqProver Q).Efficient`. [PS10, Theorem 175.1]. -/
+theorem seqProver_efficient (π : Protocol) (Q : PolyExpr) (hP : π.P.Efficient) :
+    (π.seqProver Q).Efficient := by
+  apply SeqEfficiency.phase_efficient (π.seqProver Q) π.P π.rounds π.verifierFirst hP
+  intro x z r hist
+  dsimp only
+  rw [seqProver_next, proverMoveIndex_eq]
+
+/-- An efficient original verifier gives an efficient sequential verifier:
+`π.V.Efficient → (π.seqVerifier Q).Efficient`. [PS10, Theorem 175.1]. -/
+theorem seqVerifier_efficient (π : Protocol) (Q : PolyExpr) (hV : π.V.Efficient) :
+    (π.seqVerifier Q).Efficient := by
+  classical
+  apply SeqEfficiency.verifier_efficient (π.seqVerifier Q) π.V π.rounds Q π.verifierFirst hV
+  intro x z r hist
+  dsimp only
+  rw [seqVerifier_next, verifierMoveIndex_eq, seqVerdict_eq, proverMoves_eq,
+    countP_not_moverIsV]
+  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq]
+
+/-- The repeated verifier satisfies the padded-verifier equations on `x`, with
+`q=Q.eval |x|` and `p=proverMoves π.verifierFirst (π.rounds.eval |x|)`.
+[PS10, Theorem 175.1].
+
+**Proof sketch.** Read the coin, round, mover and next-message fields of the construction.
+The existing move-index and message-count readers give each remaining contract field.
+The aggregate verdict is its published conjunction of phase tests. -/
+theorem seqRep_verifierSpec (π : Protocol) (Q : PolyExpr) (x : List Bool) :
+    PaddedVerifierSpec π (π.seqRep Q) x (Q.eval x.length)
+      (proverMoves π.verifierFirst (π.rounds.eval x.length))
+      (fun z r hist => π.seqVerdict (Q.eval x.length) x z r hist) := by
+  -- Expose the construction equations through the abstract verifier contract.
+  refine {
+    coinLen_eq := ?_
+    rounds_eq := seqRep_rounds_eval π Q x.length
+    first_eq := seqRep_verifierFirst π Q
+    next_eq := ?_
+    terminal_eq := ?_
+    index_eq := ?_
+    boundary_lengths := ?_
+    local_length := ?_
+    period := ?_
+  }
+  · rw [Strategy.coinLen_eq, seqRep_V, seqVerifier_coins, PolyExpr.eval_mul,
+      Strategy.coinLen_eq]
+  · intro z r hist
+    rw [seqRep_V, seqVerifier_next, verifierMoveIndex_eq]
+  · intro z r hist
+    exact seqVerdict_eq π (Q.eval x.length) x z r hist
+  -- Recover active indices and phase counts through the published execution readers.
+  · intro P y z rP rV t hm
+    simpa only [verifierMoveIndex_eq] using
+      verifierMoveIndex_exec P (π.seqRep Q).V π.verifierFirst x y z rP rV t hm
+  · intro P y z rP rV j _
+    exact exec_boundary_lengths P (π.seqRep Q).V π.verifierFirst x y z rP rV
+      (π.rounds.eval x.length) j
+  · intro P y z rP rV
+    rw [exec_snd_length, proverMoves_eq]
+  · intro j t
+    rw [show 2 * π.rounds.eval x.length * j + t =
+      2 * (π.rounds.eval x.length * j) + t by ring]
+    exact moverIsV_two_mul_add _ _ _
+
+/-- The repeated prover satisfies the padded-prover equations on `x`, with
+`q=Q.eval |x|` and `p=if π.verifierFirst then k/2 else (k+1)/2`, for
+`k=π.rounds.eval |x|`. [PS10, Theorem 175.1].
+
+**Proof sketch.** Read the prover's coin and reply equations. Recover actual move indices
+using the existing prover index reader and obtain phase-boundary and local counts from
+the published execution-length readers. The even phase length preserves the mover pattern.
+-/
+theorem seqRep_proverSpec (π : Protocol) (Q : PolyExpr) (x : List Bool) :
+    SequentialZK.PaddedProverSpec π (π.seqRep Q) x (Q.eval x.length)
+      (if π.verifierFirst then π.rounds.eval x.length / 2
+        else (π.rounds.eval x.length + 1) / 2) := by
+  -- Expose the prover construction and its padded execution fields.
+  refine {
+    prover_coinLen := ?_
+    rounds_eval := seqRep_rounds_eval π Q x.length
+    first := seqRep_verifierFirst π Q
+    next := ?_
+    prover_index := ?_
+    boundary := ?_
+    original_count := ?_
+    real_le := ?_
+    period := ?_
+  }
+  · rw [Strategy.coinLen_eq, seqRep_P, seqProver_coins, PolyExpr.eval_mul,
+      Strategy.coinLen_eq]
+  · intro y r hist
+    rw [seqRep_P, seqProver_next, proverMoveIndex_eq]
+  -- The same index, boundary and mover readers discharge the remaining contract.
+  · intro V y z rP rV n hm
+    simpa only [proverMoveIndex_eq] using
+      proverMoveIndex_exec (π.seqRep Q).P V π.verifierFirst x y z rP rV n hm
+  · intro V y z rP rV j
+    exact exec_boundary_lengths (π.seqRep Q).P V π.verifierFirst x y z rP rV
+      (π.rounds.eval x.length) j
+  · intro V y z rP rV
+    rw [exec_snd_length, countP_not_moverIsV]
+  · cases π.verifierFirst <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega
+  · intro j t
+    rw [show 2 * π.rounds.eval x.length * j + t =
+      2 * (π.rounds.eval x.length * j) + t by ring]
+    exact moverIsV_two_mul_add _ _ _
+
 end Protocol
 
 /-! ### Theorem 175.1 -/
@@ -407,7 +865,7 @@ zero-knowledge protocol with a bounded prover is zero-knowledge.
    output. By `ZK π R` at `Lz'`, summing the `Q(n)` gaps gives `Q(n) * ε(n)`, negligible. -/
 theorem ZK.seqRep {B : PolyExpr} (h : ZK π R) (hB : π.ProverBounded R B) (Q : PolyExpr) :
     ZK (π.seqRep Q) R := by
-  sorry
+  exact SequentialZK.zk_of_padded_spec h hB Q (fun x => π.seqRep_proverSpec Q x)
 
 /-- **Theorem 175.1, statistical case**: statistical error `δ` composes to `Q · δ`, under the
 same prover bound.
@@ -421,11 +879,12 @@ For a fixed earlier prefix, change one phase from real to simulated at distance
 `δ(|x|)` (`StatZK π R δ` holds for every auxiliary input). The common normalization and
 simulated-suffix computation do not increase statistical distance. Average over prefixes
 and sum the `Q(|x|)` gaps by the triangle inequality, giving exactly `Q(|x|) · δ(|x|)`.
-The empty-history construction handles `k = 0` or `Q(|x|) = 0` directly. -/
+The empty-history construction handles `k = 0` or `Q(|x|) = 0` directly. The padded-prover
+contract and split/block coin equivalences identify the two endpoint laws exactly. -/
 theorem StatZK.seqRep {B : PolyExpr} {δ : ℕ → ℝ} (h : StatZK π R δ)
     (hB : π.ProverBounded R B) (Q : PolyExpr) :
     StatZK (π.seqRep Q) R (fun n => Q.eval n * δ n) := by
-  sorry
+  exact SequentialZK.statZK_of_padded_spec h hB Q (fun x => π.seqRep_proverSpec Q x)
 
 /-- **Theorem 175.1, perfect case**: the sequential repetition of a perfect zero-knowledge
 protocol with a bounded prover is perfect zero-knowledge (`StatZK.seqRep` at `δ = 0`). -/
@@ -470,7 +929,14 @@ theorem PerfectZKAbort.seqRep {B : PolyExpr} (h : PerfectZKAbort π R)
    exists since `1 ≤ Q(|x|)`. -/
 theorem InteractiveProof.seqRep {L : Language Bool} (h : InteractiveProof π L) (Q : PolyExpr)
     (hQ : ∀ n, 1 ≤ Q.eval n) : InteractiveProof (π.seqRep Q) L := by
-  sorry
+  constructor
+  · rw [Protocol.seqRep_V]
+    exact π.seqVerifier_efficient Q h.efficientV
+  · exact SequentialZK.PaddedProverSpec.complete (fun x => π.seqRep_proverSpec Q x)
+      (fun x y z hc => π.seqRep_complete Q x y z hc) h.complete
+  · obtain ⟨ε, hε, hs⟩ := h.sound
+    refine ⟨ε, hε, fun x hx P' z => ?_⟩
+    exact (hs x hx P' z).trans_le (π.seqRep_sound_first Q P' x [] z (hQ x.length))
 
 /-- **Sequential repetition multiplies the soundness error** [PS10, p. 120: the protocol "can be
 repeated many times … to drive the probability of error as low as desired"; and p. 127, the
@@ -492,7 +958,13 @@ repeated many times … to drive the probability of error as low as desired"; an
 theorem InteractiveProofErr.seqRep {L : Language Bool} {s : ℕ → ℝ} (h : InteractiveProofErr π L s)
     (Q : PolyExpr) (hQ : ∀ n, 1 ≤ Q.eval n) :
     InteractiveProofErr (π.seqRep Q) L (fun n => s n ^ Q.eval n) := by
-  sorry
+  constructor
+  · rw [Protocol.seqRep_V]
+    exact π.seqVerifier_efficient Q h.efficientV
+  · exact SequentialZK.PaddedProverSpec.complete (fun x => π.seqRep_proverSpec Q x)
+      (fun x y z hc => π.seqRep_complete Q x y z hc) h.complete
+  · intro x hx P' z
+    exact (π.seqRep_verifierSpec Q x).sound h hx P' z
 
 /-- **The efficient-prover form**: the sequential repetition of an interactive proof with an
 efficient prover and soundness error `s` is one with soundness error `s^Q`; the repeated prover
@@ -504,6 +976,17 @@ every witness phase by phase, as in `InteractiveProof.seqRep`. -/
 theorem EfficientProverProofErr.seqRep {L : Language Bool} {s : ℕ → ℝ}
     (h : EfficientProverProofErr π L R s) (Q : PolyExpr) (hQ : ∀ n, 1 ≤ Q.eval n) :
     EfficientProverProofErr (π.seqRep Q) L R (fun n => s n ^ Q.eval n) := by
-  sorry
+  refine {
+    toInteractiveProofErr := h.toInteractiveProofErr.seqRep Q hQ
+    efficientP := ?_
+    boundedP := ?_
+    completeWitness := ?_
+  }
+  · rw [Protocol.seqRep_P]
+    exact π.seqProver_efficient Q h.efficientP
+  · obtain ⟨B, hB⟩ := h.boundedP
+    exact ⟨B, hB.seqRep Q⟩
+  · intro x y hxy z
+    exact π.seqRep_complete Q x y z (h.completeWitness x y hxy z)
 
 end TCSlib.Cryptography
diff --git a/TCSlib/Cryptography/Composability/SequentialZK/Advice.lean b/TCSlib/Cryptography/Composability/SequentialZK/Advice.lean
new file mode 100644
index 000000000..c67004088
--- /dev/null
+++ b/TCSlib/Cryptography/Composability/SequentialZK/Advice.lean
@@ -0,0 +1,67 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import Mathlib.Data.Fintype.Lattice
+import Mathlib.Data.Real.Archimedean
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Finite advice selection with an unbounded witness domain
+
+## Main definitions
+
+This module introduces no definitions.
+
+## Main results
+
+* `exists_uniform_bound_selector` chooses one finite metadata value whose bounds, uniform
+  over an arbitrary witness type, imply the same bounds for every metadata value.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  Theorem 175.1 (sequential repetition of zero knowledge).
+-/
+
+namespace TCSlib.Cryptography.Composability
+
+/-- Let `A` be finite and nonempty, let `W` be arbitrary, and suppose
+`g a w ≤ M` for every `a : A` and `w : W`, where `0 ≤ M`. There exists `a : A` such that,
+for every `ε ≥ 0`, `(∀ w, g a w ≤ ε) → ∀ b w, g b w ≤ ε`.
+The selector depends only on `g`, before `ε` is chosen, and need not encode any witness.
+[PS10, Theorem 175.1, finite advice selection for the hybrid reduction].
+
+**Proof sketch.** For each metadata value, take the supremum of zero together with all
+its witness-indexed values. The sets are nonempty and bounded above by `M`. Select a
+metadata value maximizing these finitely many real suprema. A uniform bound at that
+selected value bounds its supremum, while each other value is at most its own supremum.
+This uses no attainment assumption for the witness-indexed suprema. -/
+theorem exists_uniform_bound_selector {A W : Type*} [Finite A] [Nonempty A]
+    (g : A → W → ℝ) (M : ℝ) (hM : 0 ≤ M) (hg : ∀ a w, g a w ≤ M) :
+    ∃ a : A, ∀ ε : ℝ, 0 ≤ ε →
+      (∀ w, g a w ≤ ε) → ∀ b w, g b w ≤ ε := by
+  let score (a : A) : ℝ := sSup (insert 0 (Set.range (g a)))
+  have hbounded (a : A) : BddAbove (insert 0 (Set.range (g a))) := by
+    refine ⟨M, ?_⟩
+    intro r hr
+    rcases hr with rfl | ⟨w, rfl⟩
+    · exact hM
+    · exact hg a w
+  obtain ⟨a, ha⟩ := Finite.exists_max score
+  refine ⟨a, ?_⟩
+  intro ε hε hga b w
+  have hpoint : g b w ≤ score b :=
+    le_csSup (hbounded b) (Or.inr ⟨w, rfl⟩)
+  have htop : score a ≤ ε := by
+    apply csSup_le (s := insert 0 (Set.range (g a))) ⟨0, Or.inl rfl⟩
+    intro r hr
+    rcases hr with rfl | ⟨v, rfl⟩
+    · exact hε
+    · exact hga v
+  exact (hpoint.trans (ha b)).trans htop
+
+end TCSlib.Cryptography.Composability
diff --git a/TCSlib/Cryptography/Composability/SequentialZK/BoundedMetadata.lean b/TCSlib/Cryptography/Composability/SequentialZK/BoundedMetadata.lean
new file mode 100644
index 000000000..1b788fa26
--- /dev/null
+++ b/TCSlib/Cryptography/Composability/SequentialZK/BoundedMetadata.lean
@@ -0,0 +1,142 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Composability.SequentialZK.ComputationalReduction
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Finite bounded phase-reduction metadata
+
+The phase reduction's common input, verifier auxiliary word, verifier tape, phase index,
+and raw encoded prefix range over an explicit finite nonempty product. Exact-length Boolean
+vectors represent the fixed-size fields, and dependent pairs retain the precise lengths of
+bounded fields. There is no witness or output test in this metadata. [PS10, Theorem 175.1].
+
+## Main definitions
+
+* `PhaseMetadata n a v q h`: finite metadata with the five prescribed length/index bounds.
+* `PhaseMetadata.toData`: the raw reduction-advice word represented by this metadata.
+
+## Main results
+
+* `PhaseMetadata.word_lengths`: all five component bounds.
+* `PhaseMetadata.toData_length_le`: packed advice has at most `2n+2a+2v+2q+h+8` bits.
+* `PhaseMetadata.cover`: every tuple satisfying the five bounds is represented exactly.
+* `PhaseMetadata.cover_data`: every bounded raw advice word equals some `m.toData`.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §7.2.1, Theorem 175.1.
+* [Gol01] O. Goldreich, *Foundations of Cryptography, Volume I: Basic Tools*, Cambridge
+  University Press, 2001, §4.3.4.
+-/
+
+namespace TCSlib.Cryptography.SequentialZK
+
+/-- `PhaseMetadata n a v q h` is a common input of exactly `n` bits, auxiliary word of at
+most `a` bits, verifier tape of exactly `v` bits, phase index at most `q`, and raw prefix word
+of at most `h` bits. Standard product, function and sigma instances make this type finite.
+[PS10, Theorem 175.1, bounded phase-reduction advice].
+`PhaseMetadata n a v q h = ((Fin n → Bool) × (Σ l : Fin (a + 1), Fin l → Bool) × (Fin v → Bool) ×
+Fin (q + 1) × (Σ l : Fin (h + 1), Fin l → Bool))`. -/
+abbrev PhaseMetadata (n a v q h : ℕ) : Type :=
+  (Fin n → Bool) × (Σ l : Fin (a + 1), Fin l → Bool) × (Fin v → Bool) ×
+    Fin (q + 1) × (Σ l : Fin (h + 1), Fin l → Bool)
+
+/-- The metadata type is
+`(Fin n → Bool) × (Σ l : Fin (a+1), Fin l → Bool) × (Fin v → Bool) ×
+ Fin (q+1) × (Σ l : Fin (h+1), Fin l → Bool)`. -/
+theorem PhaseMetadata_eq (n a v q h : ℕ) : PhaseMetadata n a v q h =
+    ((Fin n → Bool) × (Σ l : Fin (a + 1), Fin l → Bool) × (Fin v → Bool) ×
+      Fin (q + 1) × (Σ l : Fin (h + 1), Fin l → Bool)) := rfl
+
+namespace PhaseMetadata
+
+/-- The all-false fixed-size words, empty bounded words and phase zero inhabit
+`PhaseMetadata n a v q h`, including when any or all bounds vanish.
+`Nonempty (PhaseMetadata n a v q h)`. -/
+instance {n a v q h : ℕ} : Nonempty (PhaseMetadata n a v q h) :=
+  ⟨(fun _ => false, ⟨⟨0, Nat.zero_lt_succ a⟩, Fin.elim0⟩, fun _ => false,
+    ⟨0, Nat.zero_lt_succ q⟩, ⟨⟨0, Nat.zero_lt_succ h⟩, Fin.elim0⟩)⟩
+
+/-- For metadata `m`, its raw advice is
+`reductionData (ofFn m.1) (ofFn m.2.1.2) (ofFn m.2.2.1) m.2.2.2.1
+  (ofFn m.2.2.2.2.2)`. [PS10, Theorem 175.1, phase-reduction advice].
+`m.toData = reductionData (List.ofFn m.1) (List.ofFn m.2.1.2) (List.ofFn m.2.2.1) m.2.2.2.1
+(List.ofFn m.2.2.2.2.2)`. -/
+def toData {n a v q h : ℕ} (m : PhaseMetadata n a v q h) : List Bool :=
+  reductionData (List.ofFn m.1) (List.ofFn m.2.1.2) (List.ofFn m.2.2.1) m.2.2.2.1
+    (List.ofFn m.2.2.2.2.2)
+
+/-- The packed metadata equation is `m.toData =
+reductionData (ofFn m.1) (ofFn m.2.1.2) (ofFn m.2.2.1) m.2.2.2.1
+  (ofFn m.2.2.2.2.2)`. -/
+theorem toData_eq {n a v q h : ℕ} (m : PhaseMetadata n a v q h) :
+    m.toData = reductionData (List.ofFn m.1) (List.ofFn m.2.1.2) (List.ofFn m.2.2.1)
+      m.2.2.2.1 (List.ofFn m.2.2.2.2.2) := rfl
+
+/-- For metadata `m`, its common-input and verifier-tape word lengths are exactly `n,v`,
+its auxiliary and prefix word lengths are at most `a,h`, and its phase index is at most `q`.
+`(List.ofFn m.1).length = n ∧ (List.ofFn m.2.1.2).length ≤ a ∧ (List.ofFn m.2.2.1).length = v ∧
+(m.2.2.2.1 : ℕ) ≤ q ∧ (List.ofFn m.2.2.2.2.2).length ≤ h`.
+-/
+theorem word_lengths {n a v q h : ℕ} (m : PhaseMetadata n a v q h) :
+    (List.ofFn m.1).length = n ∧ (List.ofFn m.2.1.2).length ≤ a ∧
+    (List.ofFn m.2.2.1).length = v ∧ (m.2.2.2.1 : ℕ) ≤ q ∧
+    (List.ofFn m.2.2.2.2.2).length ≤ h := by
+  simp only [List.length_ofFn]
+  exact ⟨True.intro, Nat.le_of_lt_succ m.2.1.1.isLt, True.intro,
+    Nat.le_of_lt_succ m.2.2.2.1.isLt, Nat.le_of_lt_succ m.2.2.2.2.1.isLt⟩
+
+/-- For metadata `m : PhaseMetadata n a v q h`,
+`m.toData.length ≤ 2*n + 2*a + 2*v + 2*q + h + 8`.
+[PS10, Theorem 175.1, polynomial phase-reduction advice bound]. -/
+theorem toData_length_le {n a v q h : ℕ} (m : PhaseMetadata n a v q h) :
+    m.toData.length ≤ 2 * n + 2 * a + 2 * v + 2 * q + h + 8 := by
+  obtain ⟨hx, hz, hrV, hj, hpre⟩ := m.word_lengths
+  rw [toData_eq, reductionData_length]
+  omega
+
+/-- For `x,z,rV,j,preWord` with `|x|=n`, `|z|≤a`, `|rV|=v`, `j≤q`, `|preWord|≤h`,
+there is metadata `m : PhaseMetadata n a v q h` whose five represented components are
+exactly `x,z,rV,j,preWord`. [PS10, Theorem 175.1, exact finite advice coverage].
+
+**Proof sketch.** Use each bounded word's actual length as its sigma index and its padded
+Boolean vector as its value. Fixed-size words use the given exact length. The public
+`ofFn_padFin_of_length` equation recovers each original word without changing any bits;
+the phase field stores the supplied bounded index directly. -/
+theorem cover {n a v q h : ℕ} (x z rV : List Bool) (j : ℕ) (preWord : List Bool)
+    (hx : x.length = n) (hz : z.length ≤ a) (hrV : rV.length = v)
+    (hj : j ≤ q) (hpre : preWord.length ≤ h) :
+    ∃ m : PhaseMetadata n a v q h,
+      List.ofFn m.1 = x ∧ List.ofFn m.2.1.2 = z ∧ List.ofFn m.2.2.1 = rV ∧
+      (m.2.2.2.1 : ℕ) = j ∧ List.ofFn m.2.2.2.2.2 = preWord := by
+  let m : PhaseMetadata n a v q h :=
+    (padFin n x, ⟨⟨z.length, Nat.lt_succ_of_le hz⟩, padFin z.length z⟩,
+      padFin v rV, ⟨j, Nat.lt_succ_of_le hj⟩,
+      ⟨⟨preWord.length, Nat.lt_succ_of_le hpre⟩, padFin preWord.length preWord⟩)
+  refine ⟨m, ?_, ?_, ?_, rfl, ?_⟩
+  · exact ofFn_padFin_of_length hx
+  · exact ofFn_padFin_of_length rfl
+  · exact ofFn_padFin_of_length hrV
+  · exact ofFn_padFin_of_length rfl
+
+/-- For `x,z,rV,j,preWord` with `|x|=n`, `|z|≤a`, `|rV|=v`, `j≤q`, `|preWord|≤h`,
+there is `m : PhaseMetadata n a v q h` with
+`m.toData = reductionData x z rV j preWord`. -/
+theorem cover_data {n a v q h : ℕ} (x z rV : List Bool) (j : ℕ) (preWord : List Bool)
+    (hx : x.length = n) (hz : z.length ≤ a) (hrV : rV.length = v)
+    (hj : j ≤ q) (hpre : preWord.length ≤ h) :
+    ∃ m : PhaseMetadata n a v q h, m.toData = reductionData x z rV j preWord := by
+  obtain ⟨m, hx', hz', hrV', hj', hpre'⟩ := cover x z rV j preWord hx hz hrV hj hpre
+  refine ⟨m, ?_⟩
+  rw [toData_eq, hx', hz', hrV', hj', hpre']
+
+end PhaseMetadata
+
+end TCSlib.Cryptography.SequentialZK
diff --git a/TCSlib/Cryptography/Composability/SequentialZK/ComputationalAdvice.lean b/TCSlib/Cryptography/Composability/SequentialZK/ComputationalAdvice.lean
new file mode 100644
index 000000000..b069dda50
--- /dev/null
+++ b/TCSlib/Cryptography/Composability/SequentialZK/ComputationalAdvice.lean
@@ -0,0 +1,74 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Composability.SequentialZK.Advice
+import TCSlib.Cryptography.Foundations.Negligible
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# One negligible bound for all bounded advice and arbitrary witnesses
+
+## Main definitions
+
+This module introduces no definitions.
+
+## Main results
+
+* `exists_uniform_negligible_bound` selects finite advice pointwise before requesting its
+  negligible bound, then obtains a uniform bound for every valid advice and witness.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  Theorem 175.1 (the nonuniform hybrid reduction for sequential zero knowledge).
+-/
+
+namespace TCSlib.Cryptography.SequentialZK
+
+/-- Let `A n` be finite nonempty metadata types, `W` an arbitrary witness type, and
+`gap n a w ≤ 1`. Suppose every choice `choice : ∀ n, A n` has one negligible `ε` bounding
+`gap n (choice n) w` for all valid witnesses and all `n`. Then one negligible `ε` satisfies
+`gap n a w ≤ |ε n|` for every `n,a,w` with `valid n a w`.
+Neither the metadata choice nor its negligible bound encodes a witness.
+[PS10, Theorem 175.1, advice selection before the negligible bound].
+
+**Proof sketch.** Gate the gap by validity, assigning zero to invalid pairs. At every
+length apply the bounded-family selector to this gated family and choose its finite
+metadata value. Request the negligible bound for that single metadata function. Its
+absolute value bounds every gated value at the selected metadata, including invalid
+pairs. The selector then bounds every gated value at that length, hence every valid gap.
+The argument uses no witness-length bound and no attained witness maximum. -/
+theorem exists_uniform_negligible_bound {A : ℕ → Type*} {W : Type*}
+    [∀ n, Finite (A n)] [∀ n, Nonempty (A n)]
+    (gap : (n : ℕ) → A n → W → ℝ) (valid : (n : ℕ) → A n → W → Prop)
+    (hgap : ∀ n a w, gap n a w ≤ 1)
+    (hchoice : ∀ choice : (n : ℕ) → A n, ∃ ε : ℕ → ℝ, Negligible ε ∧
+      ∀ n w, valid n (choice n) w → gap n (choice n) w ≤ ε n) :
+    ∃ ε : ℕ → ℝ, Negligible ε ∧
+      ∀ n a w, valid n a w → gap n a w ≤ |ε n| := by
+  classical
+  let g (n : ℕ) (a : A n) (w : W) : ℝ := if valid n a w then gap n a w else 0
+  have hbounded (n : ℕ) (a : A n) (w : W) : g n a w ≤ 1 := by
+    dsimp only [g]
+    split_ifs
+    · exact hgap n a w
+    · exact zero_le_one
+  have hselector (n : ℕ) :=
+    Composability.exists_uniform_bound_selector (g n) 1 zero_le_one (hbounded n)
+  choose choice hselect using hselector
+  obtain ⟨ε, hε, hselected⟩ := hchoice choice
+  refine ⟨ε, hε, ?_⟩
+  intro n a w hvalid
+  have hchosen (v : W) : g n (choice n) v ≤ |ε n| := by
+    by_cases hv : valid n (choice n) v
+    · exact (show g n (choice n) v = gap n (choice n) v from if_pos hv).le.trans
+        ((hselected n v hv).trans (le_abs_self _))
+    · exact (show g n (choice n) v = 0 from if_neg hv).le.trans (abs_nonneg _)
+  have hall := hselect n (|ε n|) (abs_nonneg _) hchosen a w
+  simpa only [g, if_pos hvalid] using hall
+
+end TCSlib.Cryptography.SequentialZK
diff --git a/TCSlib/Cryptography/Composability/SequentialZK/ComputationalHybrid.lean b/TCSlib/Cryptography/Composability/SequentialZK/ComputationalHybrid.lean
new file mode 100644
index 000000000..d0dc40060
--- /dev/null
+++ b/TCSlib/Cryptography/Composability/SequentialZK/ComputationalHybrid.lean
@@ -0,0 +1,204 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Composability.SequentialZK.ContinuationProbability
+import TCSlib.Cryptography.Composability.SequentialZK.HybridRecursion
+import TCSlib.Cryptography.Composability.SequentialZK.EndpointSampling
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Computational prefix hybrids and actual-view endpoint transfer
+
+## Main definitions
+
+This module introduces no definitions.
+
+## Main results
+
+* `prefix_distAdv_le` converts local raw-view continuation gaps into a `Q(|x|)*ε` bound.
+* `prefix_distAdv_joint_le` averages this bound over the verifier's independent tape.
+* `distAdv_view_endpoints` reindexes typed joint prefixes as actual real/simulator views.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  Theorem 175.1 (sequential repetition of zero knowledge).
+-/
+
+namespace TCSlib.Cryptography.SequentialZK
+
+open Complexity
+
+/-- At fixed verifier tape `rV`, suppose every actual real prefix before phase `i<Q(|x|)`
+has `phaseGap … i pre ≤ ε`, where `0≤ε`. For a bounded honest prover and the padded-prover
+contract, the canonical real and simulated prefix views have distinguishing advantage at
+most `Q(|x|)*ε`. No metadata validity or finite witness assumption appears in this theorem.
+[PS10, Theorem 175.1, conditional computational hybrid argument].
+
+**Proof sketch.** Use suffix acceptance as the continuation potential. Its drift under
+one real step is exactly the raw-view gap by the published real/simulated continuation
+identities. The generic conditional hybrid bound gives `Q(|x|)*ε`. At the final phase the
+suffix is empty, so averaging the potential is acceptance of the real prefix. At phase
+zero the suffix starts from the empty history and is exactly the typed simulated prefix.
+-/
+theorem prefix_distAdv_le {C : Type*} [Fintype C] {π ρ : Protocol}
+    (S : NUPPT) (B Q : PolyExpr) {x : List Bool} {p : ℕ}
+    (d : PaddedProverSpec π ρ x (Q.eval x.length) p) (V : Strategy)
+    (y z rV : List Bool) (D : List Bool → C → Bool)
+    (hp : p = if π.verifierFirst then π.rounds.eval x.length / 2
+      else (π.rounds.eval x.length + 1) / 2)
+    (hbound : ∀ r hist, (π.P.next x y r hist).length ≤ B.eval x.length)
+    (ε : ℝ) (hε : 0 ≤ ε)
+    (hlocal : ∀ i < Q.eval x.length, ∀ coins : Fin i → π.P.Coins x.length,
+      phaseGap π V S B Q x y z rV D i
+        (realPrefix π V x y z rV p i coins) ≤ ε) :
+    distAdv
+      (fun coins : Fin (Q.eval x.length) → π.P.Coins x.length =>
+        View.encode ⟨x, z, rV, realPrefix π V x y z rV p (Q.eval x.length) coins⟩)
+      (fun coins : Fin (Q.eval x.length) → S.Coins x.length =>
+        View.encode ⟨x, z, rV, simPrefix S x z rV (π.rounds.eval x.length)
+          (B.eval x.length) p (Q.eval x.length) coins⟩) D ≤
+      (Q.eval x.length : ℝ) * ε := by
+  -- At the final phase the suffix is empty, so the potential is real-prefix acceptance.
+  let realView := fun coins : Fin (Q.eval x.length) → π.P.Coins x.length =>
+    View.encode ⟨x, z, rV, realPrefix π V x y z rV p (Q.eval x.length) coins⟩
+  have hfinal :
+      uexp (fun coins : Fin (Q.eval x.length) → π.P.Coins x.length =>
+        continuationProb S π.rounds B Q π.verifierFirst x z rV D (Q.eval x.length)
+          (realPrefix π V x y z rV p (Q.eval x.length) coins)) =
+        acceptProb realView D := by
+    have hinner (coins : Fin (Q.eval x.length) → π.P.Coins x.length) :
+        continuationProb S π.rounds B Q π.verifierFirst x z rV D (Q.eval x.length)
+            (realPrefix π V x y z rV p (Q.eval x.length) coins) =
+          acceptProb (fun _ : Fin (Q.eval x.length) → S.Coins x.length => realView coins) D := by
+      rw [continuationProb_eq, Nat.sub_self]
+      simp only [phaseSuffix_zero]
+      rfl
+    have hmean := congrArg (fun f : (Fin (Q.eval x.length) → π.P.Coins x.length) → ℝ =>
+      uexp f) (funext hinner)
+    have havg := acceptProb_prod
+      (fun r : (Fin (Q.eval x.length) → π.P.Coins x.length) ×
+        (Fin (Q.eval x.length) → S.Coins x.length) => realView r.1) D
+    rw [acceptProb_fst realView D] at havg
+    exact hmean.trans havg.symm
+  -- At phase zero the same suffix is the complete simulated prefix.
+  have hinitial : continuationProb S π.rounds B Q π.verifierFirst x z rV D 0 [] =
+      acceptProb
+        (fun coins : Fin (Q.eval x.length) → S.Coins x.length =>
+          View.encode ⟨x, z, rV, simPrefix S x z rV (π.rounds.eval x.length)
+            (B.eval x.length) p (Q.eval x.length) coins⟩) D := by
+    rw [continuationProb_eq, Nat.sub_zero]
+    congr 1
+    funext coins
+    rw [phaseSuffix_zero_nil, hp]
+    have hprefix := simPrefix_eq_phasePrefix S π.rounds B π.verifierFirst x z rV
+      (List.ofFn ((FunFamily.blocks (Q.eval x.length) (S.coinLen x.length)).symm coins))
+      (Q.eval x.length) coins (fun i => by
+        have hb := FunFamily.ofFn_blocks (Q.eval x.length) (S.coinLen x.length)
+          ((FunFamily.blocks (Q.eval x.length) (S.coinLen x.length)).symm coins) i
+        rw [Equiv.apply_symm_apply] at hb
+        exact (coinBlock_eq _ _ _).trans hb.symm)
+    rw [hprefix]
+  -- Average the local raw-view gaps and apply the published conditional hybrid theorem.
+  have hgap := hybrid_recursion_gap_le
+    (fun i => realPrefix π V x y z rV p i) ([] : List (List Bool))
+    (realStep π V x y z rV p)
+    (fun r => realPrefix_zero π V x y z rV p r)
+    (fun i r a => realPrefix_snoc π V x y z rV p i r a)
+    (continuationProb S π.rounds B Q π.verifierFirst x z rV D)
+    (Q.eval x.length) ε hε (fun i hi coins => by
+      rw [← phaseGap_eq_drift S B Q d V y z rV D hp hbound i hi
+        (realPrefix π V x y z rV p i coins)]
+      exact hlocal i hi coins)
+  rw [hfinal, hinitial] at hgap
+  simpa only [distAdv_def] using hgap
+
+/-- If the fixed-verifier-tape local gaps satisfy the same bound for every verifier tape,
+the joint canonical real/simulated prefix views have advantage at most `Q(|x|)*ε`.
+[PS10, Theorem 175.1, averaging the verifier tape].
+`distAdv (fun r : V.Coins x.length × (Fin (Q.eval x.length) → π.P.Coins x.length) => View.encode ⟨x,
+z, List.ofFn r.1, realPrefix π V x y z (List.ofFn r.1) p (Q.eval x.length) r.2⟩) (fun r : V.Coins
+x.length × (Fin (Q.eval x.length) → …`. -/
+theorem prefix_distAdv_joint_le {C : Type*} [Fintype C] {π ρ : Protocol}
+    (S : NUPPT) (B Q : PolyExpr) {x : List Bool} {p : ℕ}
+    (d : PaddedProverSpec π ρ x (Q.eval x.length) p) (V : Strategy)
+    (y z : List Bool) (D : List Bool → C → Bool)
+    (hp : p = if π.verifierFirst then π.rounds.eval x.length / 2
+      else (π.rounds.eval x.length + 1) / 2)
+    (hbound : ∀ r hist, (π.P.next x y r hist).length ≤ B.eval x.length)
+    (ε : ℝ) (hε : 0 ≤ ε)
+    (hlocal : ∀ rV : V.Coins x.length, ∀ i < Q.eval x.length,
+      ∀ coins : Fin i → π.P.Coins x.length,
+      phaseGap π V S B Q x y z (List.ofFn rV) D i
+        (realPrefix π V x y z (List.ofFn rV) p i coins) ≤ ε) :
+    distAdv
+      (fun r : V.Coins x.length × (Fin (Q.eval x.length) → π.P.Coins x.length) =>
+        View.encode ⟨x, z, List.ofFn r.1,
+          realPrefix π V x y z (List.ofFn r.1) p (Q.eval x.length) r.2⟩)
+      (fun r : V.Coins x.length × (Fin (Q.eval x.length) → S.Coins x.length) =>
+        View.encode ⟨x, z, List.ofFn r.1,
+          simPrefix S x z (List.ofFn r.1) (π.rounds.eval x.length)
+            (B.eval x.length) p (Q.eval x.length) r.2⟩) D ≤
+      (Q.eval x.length : ℝ) * ε := by
+  rw [distAdv_def, acceptProb_prod, acceptProb_prod]
+  apply abs_uexp_sub_le (mul_nonneg (Nat.cast_nonneg _) hε)
+  intro rV
+  simpa only [distAdv_def] using
+    prefix_distAdv_le S B Q d V y z (List.ofFn rV) D hp hbound ε hε (hlocal rV)
+
+/-- Reindexing two samplers by equivalences and supplied pointwise endpoint readers
+preserves the distinguishing advantage of any fixed `D`.
+`distAdv F' G' D = distAdv F G D`. -/
+theorem distAdv_reindex {A B A' B' O C : Type*}
+    [Fintype A] [Fintype B] [Fintype A'] [Fintype B'] [Fintype C]
+    (F : A → O) (G : B → O) (F' : A' → O) (G' : B' → O) (D : O → C → Bool)
+    (eA : A' ≃ A) (eB : B' ≃ B)
+    (hF : ∀ a, F' a = F (eA a)) (hG : ∀ b, G' b = G (eB b)) :
+    distAdv F' G' D = distAdv F G D := by
+  have hleft : acceptProb F' D = acceptProb F D :=
+    (congrArg (fun sampler => acceptProb sampler D) (funext hF)).trans
+      (acceptProb_comp_equiv eA F D)
+  have hright : acceptProb G' D = acceptProb G D :=
+    (congrArg (fun sampler => acceptProb sampler D) (funext hG)).trans
+      (acceptProb_comp_equiv eB G D)
+  rw [distAdv_def, distAdv_def, hleft, hright]
+
+/-- The actual encoded repeated view and `SQ.simulate` have exactly the advantage of the
+joint typed real/simulated prefix views, assuming their published padded-prover and raw
+simulator endpoint equations. [PS10, Theorem 175.1, computational endpoint transfer].
+`distAdv (fun r => ((ρ.withV V).viewV x y z r).encode) (SQ.simulate x z) D = distAdv (fun r :
+V.Coins x.length × (Fin q → π.P.Coins x.length) => View.encode ⟨x, z, List.ofFn r.1, realPrefix π V
+x y z (List.ofFn r.1) p q r.2⟩) (fun r : …`. -/
+theorem distAdv_view_endpoints {C : Type*} [Fintype C] {π ρ : Protocol}
+    {x : List Bool} {q p : ℕ} (d : PaddedProverSpec π ρ x q p) (V : Strategy)
+    (y z : List Bool) (S SQ : NUPPT) (B : PolyExpr)
+    (hp : p = if π.verifierFirst then π.rounds.eval x.length / 2
+      else (π.rounds.eval x.length + 1) / 2)
+    (hlen : SQ.coinLen x.length = V.coinLen x.length + q * S.coinLen x.length)
+    (hsim : ∀ r : SQ.Coins x.length, SQ.simulate x z r =
+      View.encode ⟨x, z, (List.ofFn r).take (V.coinLen x.length),
+        phasePrefix S π.rounds B π.verifierFirst x z
+          ((List.ofFn r).take (V.coinLen x.length))
+          ((List.ofFn r).drop (V.coinLen x.length)) q⟩) (D : List Bool → C → Bool) :
+    distAdv (fun r => ((ρ.withV V).viewV x y z r).encode) (SQ.simulate x z) D =
+      distAdv
+        (fun r : V.Coins x.length × (Fin q → π.P.Coins x.length) =>
+          View.encode ⟨x, z, List.ofFn r.1,
+            realPrefix π V x y z (List.ofFn r.1) p q r.2⟩)
+        (fun r : V.Coins x.length × (Fin q → S.Coins x.length) =>
+          View.encode ⟨x, z, List.ofFn r.1,
+            simPrefix S x z (List.ofFn r.1) (π.rounds.eval x.length)
+              (B.eval x.length) p q r.2⟩) D := by
+  apply distAdv_reindex _ _ _ _ D (d.realCoinsEquiv V)
+    (coinBlocksEquiv (V.coinLen x.length) q (S.coinLen x.length) hlen)
+  · exact fun r => d.viewV_eq_realPrefix V y z r
+  · intro r
+    simpa only [hp] using
+      simulate_eq_simPrefix S SQ π.rounds B π.verifierFirst x z q (V.coinLen x.length)
+        hlen hsim r
+
+end TCSlib.Cryptography.SequentialZK
diff --git a/TCSlib/Cryptography/Composability/SequentialZK/ComputationalPhaseBound.lean b/TCSlib/Cryptography/Composability/SequentialZK/ComputationalPhaseBound.lean
new file mode 100644
index 000000000..1f453ff9f
--- /dev/null
+++ b/TCSlib/Cryptography/Composability/SequentialZK/ComputationalPhaseBound.lean
@@ -0,0 +1,184 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Composability.SequentialZK.BoundedMetadata
+import TCSlib.Cryptography.Composability.SequentialZK.ComputationalAdvice
+import TCSlib.Cryptography.Composability.SequentialZK.ReductionAdvantage
+import TCSlib.Cryptography.Composability.SequentialZK.ContinuationProbability
+import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.ColZKLemmas
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# One negligible bound for all bounded phase continuations
+
+## Main definitions
+
+This module introduces no definitions or computational hosts.
+
+## Main results
+
+* `exists_negligible_phase_bound`: the wrapped original simulator gives one negligible
+  bound for every bounded phase metadata tuple, with no witness in the reduction advice.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  Theorem 175.1.
+-/
+
+namespace TCSlib.Cryptography.SequentialZK
+
+open Complexity Turing
+
+/-- Let `π,R,V,S` have a uniform simulator satisfying the computational comparison for
+`π` against `phaseVerifier V`, for every auxiliary polynomial and nonuniform distinguisher.
+For fixed `Lz,D,Q,B`, one negligible `ε` bounds `phaseGap` by `|ε(|x|)|` for every witness,
+auxiliary word `|z|≤Lz(|x|)`, verifier tape of its exact prescribed length, phase `j<Q(|x|)`,
+and prefix with encoding length at most `Q(|x|)*π.rounds(|x|)*(2*B(|x|)+2)`.
+No prover bound, witness bound or reachability premise is required for this comparison.
+[PS10, Theorem 175.1, common negligible phase bound for sequential zero knowledge].
+
+**Proof sketch.**
+Use a syntactic polynomial for the complete encoded-prefix envelope.
+Pack the input, auxiliary word, verifier tape, phase and raw prefix into finite metadata.
+These metadata types remain nonempty at every parameter, including zero phases.
+The existing advantage bound by one bounds every metadata and witness gap.
+Validity is a proof-only relation: the witness is valid, the prefix is canonical, and the
+phase lies strictly below the repetition count. No machine tests this relation.
+Apply the published finite advice selector before requesting any negligible bound.
+For any selected metadata function, its public length reader gives a polynomial advice bound.
+The uniform continuation sampler and ordinary advice closure build one nonuniform reduction.
+Canonical-prefix validity identifies its packed advice with input paired with phase auxiliary.
+The public second-projection length bound therefore bounds that auxiliary word.
+Apply the given original simulator comparison to this reduction and auxiliary polynomial.
+The exact typed reduction advantage reader identifies the selected local phase gap.
+The finite selector propagates this negligible bound to every valid metadata tuple.
+Finally the public exact-cover reader represents each supplied typed prefix and bounded tuple.
+The decoder's public encoding equation recovers that prefix without changing any bits.
+Substitution yields the claimed common bound for all witnesses and all fixed verifier tapes. -/
+theorem exists_negligible_phase_bound (π : Protocol) (R : List Bool → List Bool → Prop)
+    (V : Strategy) (S : NUPPT) (hS : S.Uniform)
+    (hclose : ∀ (Lz' : PolyExpr) (Red : NUPPT), ∃ ε : ℕ → ℝ, Negligible ε ∧
+      ∀ x y aux, R x y → aux.length ≤ Lz'.eval x.length →
+        distAdv (fun r => ((π.withV (phaseVerifier V)).viewV x y aux r).encode)
+          (S.simulate x aux) (Red.distinguisherL x.length) ≤ ε x.length)
+    (Lz : PolyExpr) (D : NUPPT) (Q B : PolyExpr) :
+    ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ x y z rV j pre, R x y →
+      z.length ≤ Lz.eval x.length → rV.length = V.coinLen x.length → j < Q.eval x.length →
+      (Strategy.encodeMsgs pre).length ≤
+        Q.eval x.length * π.rounds.eval x.length * (2 * B.eval x.length + 2) →
+      phaseGap π V S B Q x y z rV (D.distinguisherL x.length) j pre ≤ |ε x.length| := by
+  classical
+  -- Fix finite metadata bounds and the common polynomial advice envelope.
+  let H : PolyExpr := .mul (.mul Q π.rounds) (.add (.mul (.const 2) B) (.const 2))
+  let b : PolyExpr := .add (.add (.add (.add (.add (.mul (.const 2) .var)
+    (.mul (.const 2) Lz)) (.mul (.const 2) V.coins)) (.mul (.const 2) Q)) H) (.const 8)
+  have hH (n : ℕ) : H.eval n = Q.eval n * π.rounds.eval n * (2 * B.eval n + 2) := by
+    simp only [H, PolyExpr.eval_mul, PolyExpr.eval_add, PolyExpr.eval_const]
+  have hb (n : ℕ) : b.eval n =
+      2 * n + 2 * Lz.eval n + 2 * V.coinLen n + 2 * Q.eval n + H.eval n + 8 := by
+    simp only [b, PolyExpr.eval_mul, PolyExpr.eval_add, PolyExpr.eval_const,
+      PolyExpr.eval_var, Strategy.coinLen_eq]
+  let A (n : ℕ) := PhaseMetadata n (Lz.eval n) (V.coinLen n) (Q.eval n) (H.eval n)
+  let gap (n : ℕ) (m : A n) (y : List Bool) : ℝ :=
+    phaseGap π V S B Q (List.ofFn m.1) y (List.ofFn m.2.1.2) (List.ofFn m.2.2.1)
+      (D.distinguisherL (List.ofFn m.1).length) m.2.2.2.1
+      (BinArith.decWords (List.ofFn m.2.2.2.2.2))
+  let valid (n : ℕ) (m : A n) (y : List Bool) : Prop :=
+    R (List.ofFn m.1) y ∧
+      Strategy.encodeMsgs (BinArith.decWords (List.ofFn m.2.2.2.2.2)) =
+        List.ofFn m.2.2.2.2.2 ∧ (m.2.2.2.1 : ℕ) < Q.eval n
+  have hgap (n : ℕ) (m : A n) (y : List Bool) : gap n m y ≤ 1 := by
+    dsimp only [gap]
+    rw [phaseGap_eq]
+    exact ColZK.distAdv_le_one _ _ _
+  -- The selector sees a bounded gap and a proof-only validity predicate.
+  have hchoice (choice : (n : ℕ) → A n) : ∃ ε : ℕ → ℝ, Negligible ε ∧
+      ∀ n y, valid n (choice n) y → gap n (choice n) y ≤ ε n := by
+    let X (n : ℕ) := List.ofFn (choice n).1
+    let Z (n : ℕ) := List.ofFn (choice n).2.1.2
+    let RV (n : ℕ) := List.ofFn (choice n).2.2.1
+    let J (n : ℕ) : ℕ := (choice n).2.2.2.1
+    let PW (n : ℕ) := List.ofFn (choice n).2.2.2.2.2
+    -- One metadata choice gives ordinary bounded advice, independent of the witness.
+    have hdata (n : ℕ) : (reductionData (X n) (Z n) (RV n) (J n) (PW n)).length ≤
+        b.eval n := by
+      rw [hb]
+      simpa only [PhaseMetadata.toData_eq, X, Z, RV, J, PW] using
+        (choice n).toData_length_le
+    obtain ⟨Red, hcoins, hrun⟩ := exists_phaseReduction S hS D π.rounds B Q
+      π.verifierFirst X Z RV J PW b hdata
+    obtain ⟨ε, hε, hbound⟩ := hclose b Red
+    refine ⟨ε, hε, ?_⟩
+    intro n y hy
+    have hx : (X n).length = n := List.length_ofFn
+    have hcanon : Strategy.encodeMsgs (BinArith.decWords (PW n)) = PW n := hy.2.1
+    have hpack : reductionData (X n) (Z n) (RV n) (J n) (PW n) =
+        pairEncode (X n) (phaseAux (Z n) (RV n) (J n) (BinArith.decWords (PW n))) := by
+      exact (congrArg (reductionData (X n) (Z n) (RV n) (J n)) hcanon.symm).trans
+        (reductionData_encodeMsgs (X n) (Z n) (RV n) (J n) (BinArith.decWords (PW n)))
+    -- Canonical raw advice is input paired with auxiliary; projection bounds its length.
+    have haux : (phaseAux (Z n) (RV n) (J n) (BinArith.decWords (PW n))).length ≤
+        b.eval (X n).length := by
+      rw [hx]
+      calc
+        _ = (pairSndD (reductionData (X n) (Z n) (RV n) (J n) (PW n))).length := by
+          rw [hpack, pairSndD_pairEncode]
+        _ ≤ (reductionData (X n) (Z n) (RV n) (J n) (PW n)).length :=
+          length_pairSndD_le _
+        _ ≤ b.eval n := hdata n
+    -- The selected advised reduction is exactly the typed local continuation experiment.
+    have hlocal := hbound (X n) y
+      (phaseAux (Z n) (RV n) (J n) (BinArith.decWords (PW n))) hy.1 haux
+    have hrunAt : ∀ raw r, Red.runAtL (X n).length raw r =
+        D.runAtL (X n).length
+          (phaseContinuation S π.rounds B Q π.verifierFirst (X n) (Z n) (RV n)
+            (J n) (BinArith.decWords (PW n)) raw
+            (r.take ((PolyExpr.mul Q S.coins).eval (X n).length)))
+          (r.drop ((PolyExpr.mul Q S.coins).eval (X n).length)) := by
+      simpa only [hx] using hrun n
+    have heq := distAdv_phaseReduction S D Red π.rounds B Q π.verifierFirst (X n).length
+      (X n) (Z n) (RV n) (J n) (BinArith.decWords (PW n)) hcoins hrunAt
+      (fun r => ((π.withV (phaseVerifier V)).viewV (X n) y
+        (phaseAux (Z n) (RV n) (J n) (BinArith.decWords (PW n))) r).encode)
+      (S.simulate (X n) (phaseAux (Z n) (RV n) (J n) (BinArith.decWords (PW n))))
+    have hgapEq : gap n (choice n) y =
+        distAdv (fun r => ((π.withV (phaseVerifier V)).viewV (X n) y
+          (phaseAux (Z n) (RV n) (J n) (BinArith.decWords (PW n))) r).encode)
+          (S.simulate (X n) (phaseAux (Z n) (RV n) (J n) (BinArith.decWords (PW n))))
+          (Red.distinguisherL (X n).length) := by
+      dsimp only [gap]
+      rw [phaseGap_eq]
+      simpa only [X, Z, RV, J, PW] using heq.symm
+    have hscalar : gap n (choice n) y ≤ ε (X n).length := by
+      rw [hgapEq]
+      exact hlocal
+    simpa only [hx] using hscalar
+  -- The public selector chooses metadata before epsilon and then bounds every valid tuple.
+  obtain ⟨ε, hε, hall⟩ := exists_uniform_negligible_bound gap valid hgap hchoice
+  refine ⟨ε, hε, ?_⟩
+  -- Exact finite coverage recovers every bounded caller-supplied prefix and metadata tuple.
+  intro x y z rV j pre hxy hz hrV hj hpre
+  obtain ⟨m, hx, hz', hrV', hj', hpre'⟩ := PhaseMetadata.cover (h := H.eval x.length) x z rV j
+    (Strategy.encodeMsgs pre) rfl hz hrV hj.le (by simpa only [hH] using hpre)
+  have hdecode : BinArith.decWords (List.ofFn m.2.2.2.2.2) = pre := by
+    rw [hpre', encodeMsgs_eq_encWords, BinArith.decWords_encWords]
+  have hvalid : valid x.length m y := by
+    refine ⟨?_, ?_, ?_⟩
+    · simpa only [hx] using hxy
+    · rw [hdecode, hpre']
+    · simpa only [hj'] using hj
+  have hcovered : gap x.length m y =
+      phaseGap π V S B Q x y z rV (D.distinguisherL x.length) j pre := by
+    dsimp only [gap]
+    rw [hz', hrV', hj', hdecode]
+    exact congrArg (fun u : List Bool =>
+      phaseGap π V S B Q u y z rV (D.distinguisherL u.length) j pre) hx
+  rw [← hcovered]
+  exact hall x.length m y hvalid
+
+end TCSlib.Cryptography.SequentialZK
diff --git a/TCSlib/Cryptography/Composability/SequentialZK/ComputationalReduction.lean b/TCSlib/Cryptography/Composability/SequentialZK/ComputationalReduction.lean
new file mode 100644
index 000000000..1f76a663b
--- /dev/null
+++ b/TCSlib/Cryptography/Composability/SequentialZK/ComputationalReduction.lean
@@ -0,0 +1,285 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Composability.SequentialZK.SuffixMachine
+import TCSlib.Cryptography.Asymptotic.Adversary
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# The advised computational sequential-phase reduction
+
+A raw current-phase candidate is normalized using fixed metadata, followed by a randomized
+simulated suffix and the original distinguisher. The metadata contains no witness. Validity
+and reachability are properties of the later proof; every machine here uses total word
+projections and the canonical normalizer on arbitrary inputs.
+
+## Main definitions
+
+* `reductionData`: common input, verifier auxiliary input/tape, phase, and raw prefix word.
+* `phaseContinuation`: normalize the current candidate, simulate the suffix, and replay a view.
+
+## Main results
+
+* `phaseContinuation_poly`: the continuation is polynomial-time on total metadata functions.
+* `exists_continuationSampler`: a uniform fresh-coin sampler for the continuation.
+* `exists_phaseReduction`: compose the sampler with a distinguisher and bounded advice.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §7.2.1, Theorem 175.1.
+* [Gol01] O. Goldreich, *Foundations of Cryptography, Volume I: Basic Tools*, Cambridge
+  University Press, 2001, §4.3.4.
+-/
+
+namespace TCSlib.Cryptography.SequentialZK
+
+open Complexity Turing
+
+/-- For `x,z,rV,j,preWord`, the reduction metadata is
+`⟨x,⟨z,⟨rV,⟨1^j,preWord⟩⟩⟩⟩`. Keeping the prefix as a raw word gives an exact advice-size
+bound even on malformed metadata. [PS10, Theorem 175.1, phase-reduction advice].
+`reductionData x z rV j preWord = pairEncode x (pairEncode z (pairEncode rV (pairEncode
+(List.replicate j true) preWord)))`. -/
+def reductionData (x z rV : List Bool) (j : ℕ) (preWord : List Bool) : List Bool :=
+  pairEncode x (pairEncode z (pairEncode rV (pairEncode (List.replicate j true) preWord)))
+
+/-- The metadata equation is `reductionData x z rV j preWord =
+pairEncode x (pairEncode z (pairEncode rV (pairEncode (List.replicate j true) preWord)))`. -/
+theorem reductionData_eq (x z rV : List Bool) (j : ℕ) (preWord : List Bool) :
+    reductionData x z rV j preWord =
+      pairEncode x (pairEncode z (pairEncode rV (pairEncode (List.replicate j true) preWord))) :=
+  rfl
+
+/-- The five projection fields of `reductionData x z rV j preWord`, in order, are
+`x,z,rV,List.replicate j true,preWord`.
+`pairFstD (reductionData x z rV j preWord) = x ∧ pairFstD (pairSndD (reductionData x z rV j
+preWord)) = z ∧ pairFstD (pairSndD (pairSndD (reductionData x z rV j preWord))) = rV ∧ pairFstD
+(pairSndD (pairSndD (pairSndD (reductionData x z rV …`. -/
+theorem reductionData_fields (x z rV : List Bool) (j : ℕ) (preWord : List Bool) :
+    pairFstD (reductionData x z rV j preWord) = x ∧
+    pairFstD (pairSndD (reductionData x z rV j preWord)) = z ∧
+    pairFstD (pairSndD (pairSndD (reductionData x z rV j preWord))) = rV ∧
+    pairFstD (pairSndD (pairSndD (pairSndD (reductionData x z rV j preWord)))) =
+      List.replicate j true ∧
+    pairSndD (pairSndD (pairSndD (pairSndD (reductionData x z rV j preWord)))) = preWord := by
+  simp only [reductionData_eq, pairFstD_pairEncode, pairSndD_pairEncode, and_self]
+
+/-- For polynomial-time `X,Z,RV,PreWord` and unary polynomial-time `J`, the metadata map
+`w ↦ reductionData (X w) (Z w) (RV w) (J w) (PreWord w)` is polynomial-time.
+`PolyTimeComputable fun w => reductionData (X w) (Z w) (RV w) (J w) (PreWord w)`. -/
+theorem reductionData_poly {X Z RV PreWord : List Bool → List Bool} {J : List Bool → ℕ}
+    (hX : PolyTimeComputable X) (hZ : PolyTimeComputable Z) (hRV : PolyTimeComputable RV)
+    (hJ : PolyTimeComputable fun w => List.replicate (J w) true)
+    (hPre : PolyTimeComputable PreWord) :
+    PolyTimeComputable fun w => reductionData (X w) (Z w) (RV w) (J w) (PreWord w) :=
+  (hX.pairEncode (hZ.pairEncode (hRV.pairEncode (hJ.pairEncode hPre)))).congr
+    (fun _ => (reductionData_eq _ _ _ _ _).symm)
+
+/-- The metadata length is
+`|reductionData x z rV j preWord| = 2|x|+2|z|+2|rV|+2j+|preWord|+8`. -/
+theorem reductionData_length (x z rV : List Bool) (j : ℕ) (preWord : List Bool) :
+    (reductionData x z rV j preWord).length =
+      2 * x.length + 2 * z.length + 2 * rV.length + 2 * j + preWord.length + 8 := by
+  rw [reductionData_eq, length_pairEncode, length_pairEncode, length_pairEncode,
+    length_pairEncode, List.length_replicate]
+  omega
+
+/-- For a canonical prefix word, reduction metadata is the input paired with the phase
+auxiliary word: `reductionData x z rV j (encodeMsgs pre) = pairEncode x (phaseAux z rV j pre)`.
+-/
+theorem reductionData_encodeMsgs (x z rV : List Bool) (j : ℕ) (pre : List (List Bool)) :
+    reductionData x z rV j (Strategy.encodeMsgs pre) = pairEncode x (phaseAux z rV j pre) :=
+  (reductionData_eq _ _ _ _ _).trans (congrArg (pairEncode x) (phaseAux_eq z rV j pre).symm)
+
+/-- For `S,k,B,Q,verifierFirst,x,z,rV,j,pre,raw,rS`, normalize the raw current-phase view
+using known auxiliary input `phaseAux z rV j pre`, append the empty prover fillers, simulate
+phases `j+1` through `Q(|x|)-1`, and return the canonical final view with fields `x,z,rV`.
+All decoders and counts are total, including on malformed candidates and `j≥Q(|x|)`.
+[PS10, Theorem 175.1; Gol01, §4.3.4, one-phase hybrid continuation]. -/
+def phaseContinuation (S : NUPPT) (k B Q : PolyExpr) (verifierFirst : Bool)
+    (x z rV : List Bool) (j : ℕ) (pre : List (List Bool)) (raw rS : List Bool) : List Bool :=
+  let aux := phaseAux z rV j pre
+  let p := if verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2
+  let pre1 := pre ++ (normalizePhaseMsgs x aux p (B.eval x.length) raw ++
+    List.replicate (k.eval x.length - p) [])
+  View.encode ⟨x, z, rV, phaseSuffix S k B verifierFirst x z rV rS (j + 1) pre1
+    (Q.eval x.length - (j + 1))⟩
+
+/-- The complete `phaseContinuation` equation first forms
+`pre1 = pre ++ (normalizePhaseMsgs x (phaseAux z rV j pre) p (B(|x|)) raw ++ (k(|x|)-p) empties)`,
+then encodes `⟨x,z,rV,phaseSuffix … (j+1) pre1 (Q(|x|)-(j+1))⟩`, with
+`p = if verifierFirst then k(|x|)/2 else (k(|x|)+1)/2`. -/
+theorem phaseContinuation_eq (S : NUPPT) (k B Q : PolyExpr) (verifierFirst : Bool)
+    (x z rV : List Bool) (j : ℕ) (pre : List (List Bool)) (raw rS : List Bool) :
+    phaseContinuation S k B Q verifierFirst x z rV j pre raw rS =
+      let aux := phaseAux z rV j pre
+      let p := if verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2
+      let pre1 := pre ++ (normalizePhaseMsgs x aux p (B.eval x.length) raw ++
+        List.replicate (k.eval x.length - p) [])
+      View.encode ⟨x, z, rV, phaseSuffix S k B verifierFirst x z rV rS (j + 1) pre1
+        (Q.eval x.length - (j + 1))⟩ := rfl
+
+/-- For uniform `S`, fixed `k,B,Q,verifierFirst`, polynomial-time words `X,Z,RV,Raw,RS`,
+unary polynomial-time phase `J`, and initial messages `H` with polynomial-time encoding,
+`w ↦ phaseContinuation S k B Q verifierFirst (X w) (Z w) (RV w) (J w) (H w) (Raw w) (RS w)`
+is polynomial-time. No validity, reachability, witness, or phase-range premise is required.
+[PS10, Theorem 175.1, the one-phase hybrid machine].
+`PolyTimeComputable fun w => phaseContinuation S k B Q verifierFirst (X w) (Z w) (RV w) (J w) (H w)
+(Raw w) (RS w)`.
+
+**Proof sketch.** Build the expected phase auxiliary word and canonically normalize the
+current candidate. Append its real-message encoding and the existing empty-filler encoding
+to the earlier prefix. Unary arithmetic computes starting phase `J+1` and remaining count
+`Q(|X|)-(J+1)`. Apply the published arbitrary-prefix suffix machine, then assemble the
+canonical final view through its equation reader. All preprocessing is total. -/
+theorem phaseContinuation_poly (S : NUPPT) (hS : S.Uniform) (k B Q : PolyExpr)
+    (verifierFirst : Bool) {X Z RV Raw RS : List Bool → List Bool} {J : List Bool → ℕ}
+    {H : List Bool → List (List Bool)}
+    (hX : PolyTimeComputable X) (hZ : PolyTimeComputable Z) (hRV : PolyTimeComputable RV)
+    (hRaw : PolyTimeComputable Raw) (hRS : PolyTimeComputable RS)
+    (hJ : PolyTimeComputable fun w => List.replicate (J w) true)
+    (hH : PolyTimeComputable fun w => Strategy.encodeMsgs (H w)) :
+    PolyTimeComputable fun w => phaseContinuation S k B Q verifierFirst
+      (X w) (Z w) (RV w) (J w) (H w) (Raw w) (RS w) := by
+  -- Canonical normalization supplies the candidate phase's bounded real slots.
+  have haux := phaseAux_poly hZ hRV hJ hH
+  have hK := EncodingMachines.unaryPolyOf_poly k (EncodingMachines.unaryLength_poly hX)
+  have hP : PolyTimeComputable fun w => List.replicate
+      (if verifierFirst then k.eval (X w).length / 2 else (k.eval (X w).length + 1) / 2) true := by
+    cases verifierFirst
+    · simpa only [EncodingMachines.divNum_eq] using EncodingMachines.divNum_poly
+        (EncodingMachines.unaryAdd_poly hK (EncodingMachines.unaryConst_poly 1))
+        (EncodingMachines.unaryConst_poly 2)
+    · simpa only [EncodingMachines.divNum_eq] using
+        EncodingMachines.divNum_poly hK (EncodingMachines.unaryConst_poly 2)
+  have hbits := EncodingMachines.unaryPolyOf_poly B (EncodingMachines.unaryLength_poly hX)
+  have hnorm := polyTimeComputable_encode_normalizePhaseMsgs hX haux hRaw hP hbits
+  have hfill := encode_emptyMsgs_poly (EncodingMachines.unarySub_poly hK hP)
+  let H1 : List Bool → List (List Bool) := fun w =>
+    H w ++ (normalizePhaseMsgs (X w) (phaseAux (Z w) (RV w) (J w) (H w))
+      (if verifierFirst then k.eval (X w).length / 2 else (k.eval (X w).length + 1) / 2)
+      (B.eval (X w).length) (Raw w) ++ List.replicate
+        (k.eval (X w).length -
+          (if verifierFirst then k.eval (X w).length / 2 else (k.eval (X w).length + 1) / 2)) [])
+  have hH1 : PolyTimeComputable fun w => Strategy.encodeMsgs (H1 w) := by
+    refine (hH.append (hnorm.append hfill)).congr fun w => ?_
+    dsimp only [H1]
+    rw [CommitmentLemmas.encodeMsgs_append, CommitmentLemmas.encodeMsgs_append]
+  -- Reuse the total suffix routine after this candidate phase, then replay the view.
+  have hStart := EncodingMachines.unaryAdd_poly hJ (EncodingMachines.unaryConst_poly 1)
+  have hCount := EncodingMachines.unarySub_poly
+    (EncodingMachines.unaryPolyOf_poly Q (EncodingMachines.unaryLength_poly hX)) hStart
+  have hsuffix := phaseSuffix_poly S hS k B verifierFirst
+    hX hZ hRV hRS hStart hCount hH1
+  refine ((hX.pairEncode hZ).pairEncode (hRV.pairEncode hsuffix)).congr fun w => ?_
+  rw [phaseContinuation_eq, View.encode_mk]
+
+/-- For uniform `S` and `k,B,Q,verifierFirst`, there is a uniform sampler `U` with coins
+`Q*S.coins` whose activation on `⟨raw,reductionData x z rV j preWord⟩` is exactly
+`phaseContinuation S k B Q verifierFirst x z rV j (decWords preWord) raw r`.
+This holds for every security parameter and every raw tape, without metadata validity tests.
+[PS10, Theorem 175.1, randomized one-phase hybrid continuation].
+`∃ U : NUPPT, U.Uniform ∧ U.coins = .mul Q S.coins ∧ ∀ (n : ℕ) (raw x z rV : List Bool) (j : ℕ)
+(preWord r : List Bool), U.runAtL n (pairEncode raw (reductionData x z rV j preWord)) r =
+phaseContinuation S k B Q verifierFirst x z rV j …`.
+
+**Proof sketch.** Decode the metadata through total pair projections, its phase through
+unary length, and its earlier prefix through the total word-list decoder. Apply
+`phaseContinuation_poly` with the sampler's full coin tape. The published uniform-machine
+constructor assigns the stated coin polynomial. Public activation/layout and metadata
+readers give the exact equation, including malformed prefix words. -/
+theorem exists_continuationSampler (S : NUPPT) (hS : S.Uniform) (k B Q : PolyExpr)
+    (verifierFirst : Bool) :
+    ∃ U : NUPPT, U.Uniform ∧ U.coins = .mul Q S.coins ∧
+      ∀ (n : ℕ) (raw x z rV : List Bool) (j : ℕ) (preWord r : List Bool),
+        U.runAtL n (pairEncode raw (reductionData x z rV j preWord)) r =
+          phaseContinuation S k B Q verifierFirst x z rV j (BinArith.decWords preWord)
+            raw r := by
+  -- Decode only total metadata projections and the raw prefix interpretation.
+  let M : List Bool → List Bool := fun w => pairSndD (NUPPT.inArg w)
+  let X : List Bool → List Bool := fun w => pairFstD (M w)
+  let Z : List Bool → List Bool := fun w => pairFstD (pairSndD (M w))
+  let RV : List Bool → List Bool := fun w => pairFstD (pairSndD (pairSndD (M w)))
+  let J : List Bool → ℕ := fun w =>
+    (pairFstD (pairSndD (pairSndD (pairSndD (M w))))).length
+  let PW : List Bool → List Bool := fun w =>
+    pairSndD (pairSndD (pairSndD (pairSndD (M w))))
+  let Raw : List Bool → List Bool := fun w => pairFstD (NUPPT.inArg w)
+  have hM : PolyTimeComputable M :=
+    polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg
+  have hX : PolyTimeComputable X := polyTimeComputable_pairFstD.comp hM
+  have hZ : PolyTimeComputable Z :=
+    polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp hM)
+  have hRV : PolyTimeComputable RV := polyTimeComputable_pairFstD.comp
+    (polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp hM))
+  have hJ : PolyTimeComputable fun w => List.replicate (J w) true :=
+    EncodingMachines.unaryLength_poly (polyTimeComputable_pairFstD.comp
+      (polyTimeComputable_pairSndD.comp
+        (polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp hM))))
+  have hPW : PolyTimeComputable PW := polyTimeComputable_pairSndD.comp
+    (polyTimeComputable_pairSndD.comp
+      (polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp hM)))
+  have hH : PolyTimeComputable fun w => Strategy.encodeMsgs (BinArith.decWords (PW w)) :=
+    (polyTimeComputable_encWords_decWords hPW).congr
+      (fun _ => (encodeMsgs_eq_encWords _).symm)
+  have hRaw : PolyTimeComputable Raw :=
+    polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg
+  let F : List Bool → List Bool := fun w => phaseContinuation S k B Q verifierFirst
+    (X w) (Z w) (RV w) (J w) (BinArith.decWords (PW w)) (Raw w) (NUPPT.inCoins w)
+  have hF : PolyTimeComputable F := phaseContinuation_poly S hS k B Q verifierFirst
+    hX hZ hRV hRaw NUPPT.polyTimeComputable_inCoins hJ hH
+  -- The published uniform constructor and layout readers give the exact activation.
+  refine ⟨NUPPT.ofPolyTimeUniform hF (.mul Q S.coins),
+    NUPPT.ofPolyTimeUniform_uniform hF _, NUPPT.coins_ofPolyTimeUniform hF _, ?_⟩
+  intro n raw x z rV j preWord r
+  rw [NUPPT.runAtL_ofPolyTimeUniform, NUPPT.advInput_eq, ← NUPPT.layout_eq]
+  dsimp only [F, X, Z, RV, J, PW, Raw, M]
+  simp only [NUPPT.inArg_layout, NUPPT.inCoins_layout, reductionData_eq,
+    pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]
+
+/-- Given uniform `S`, distinguisher `D`, polynomials `k,B,Q`, orientation `verifierFirst`,
+metadata families `X,Z,RV,J,PreWord`, and a polynomial bound on their packed `reductionData`,
+there is a nonuniform reduction with coins `Q*S.coins + D.coins`. Its activation normalizes
+the current raw phase, simulates the suffix on the first `Q*S.coins` bits, and runs `D` on
+the final canonical view with the remaining coins. No witness is stored or tested.
+[PS10, Theorem 175.1; Gol01, §4.3.4, advised one-phase hybrid reduction].
+`∃ Red : NUPPT, Red.coins = .add (.mul Q S.coins) D.coins ∧ ∀ (n : ℕ) (raw r : List Bool),
+Red.runAtL n raw r = D.runAtL n (phaseContinuation S k B Q verifierFirst (X n) (Z n) (RV n) (J n)
+(BinArith.decWords (PreWord n)) raw (r.take …`.
+
+**Proof sketch.** Take the uniform continuation sampler. Precompose `D` with the second pair
+projection, then apply the published fresh-coin sequential composition so that `D` receives
+only the sampled final view. Apply the ordinary bounded-advice closure to the packed metadata
+family. The three published activation equations, the sampler's exact reader, and its coin
+polynomial identify the complete reduction without constructing a new machine or host. -/
+theorem exists_phaseReduction (S : NUPPT) (hS : S.Uniform) (D : NUPPT)
+    (k B Q : PolyExpr) (verifierFirst : Bool) (X Z RV : ℕ → List Bool)
+    (J : ℕ → ℕ) (PreWord : ℕ → List Bool) (b : PolyExpr)
+    (hdata : ∀ n, (reductionData (X n) (Z n) (RV n) (J n) (PreWord n)).length ≤ b.eval n) :
+    ∃ Red : NUPPT, Red.coins = .add (.mul Q S.coins) D.coins ∧
+      ∀ (n : ℕ) (raw r : List Bool), Red.runAtL n raw r =
+        D.runAtL n
+          (phaseContinuation S k B Q verifierFirst (X n) (Z n) (RV n) (J n)
+            (BinArith.decWords (PreWord n)) raw (r.take ((PolyExpr.mul Q S.coins).eval n)))
+          (r.drop ((PolyExpr.mul Q S.coins).eval n)) := by
+  obtain ⟨U, _, hUc, hU⟩ := exists_continuationSampler S hS k B Q verifierFirst
+  obtain ⟨D0, hD0c, _, _, hD0⟩ := NUPPT.exists_comp D
+    (pre := pairSndD) (post := fun w => w) polyTimeComputable_pairSndD polyTimeComputable_id
+  obtain ⟨C, hCc, _, hC⟩ := NUPPT.exists_seq U D0
+  let β : ℕ → List Bool := fun n => reductionData (X n) (Z n) (RV n) (J n) (PreWord n)
+  have hβ : ∀ n, (β n).length ≤ b.eval n := hdata
+  obtain ⟨Red, hRc, hR⟩ := NUPPT.exists_withAdvice C β b hβ
+  refine ⟨Red, ?_, ?_⟩
+  · rw [hRc, hCc, hUc, hD0c]
+  · intro n raw r
+    rw [hR, hC, hD0, pairSndD_pairEncode]
+    dsimp only [β]
+    rw [hU]
+    simp only [NUPPT.coinLen_eq, hUc]
+
+end TCSlib.Cryptography.SequentialZK
diff --git a/TCSlib/Cryptography/Composability/SequentialZK/ComputationalTransfer.lean b/TCSlib/Cryptography/Composability/SequentialZK/ComputationalTransfer.lean
new file mode 100644
index 000000000..9a9b45e0b
--- /dev/null
+++ b/TCSlib/Cryptography/Composability/SequentialZK/ComputationalTransfer.lean
@@ -0,0 +1,100 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Composability.SequentialZK.ComputationalPhaseBound
+import TCSlib.Cryptography.Composability.SequentialZK.ComputationalHybrid
+import TCSlib.Cryptography.Composability.SequentialZK.RealPrefixBounds
+import TCSlib.Cryptography.ZeroKnowledge.Defs
+import TCSlib.Cryptography.Asymptotic.ReductionSupport
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Computational zero knowledge from the padded-prover contract
+
+## Main definitions
+
+This module introduces no definitions or computational hosts.
+
+## Main results
+
+* `zk_of_padded_spec`: a protocol satisfying the padded-prover contract preserves
+  computational zero knowledge under the original prover-message bound.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  Theorem 175.1.
+* [Gol01] O. Goldreich, *Foundations of Cryptography, Volume I: Basic Tools*, Cambridge
+  University Press, 2001, §4.3.4.
+-/
+
+namespace TCSlib.Cryptography.SequentialZK
+
+open Complexity
+
+/-- For protocols `π,ρ`, relation `R`, prover bound `B`, and phase polynomial `Q`, if
+`ZK π R`, `π.ProverBounded R B`, and `ρ` satisfies the padded-prover specification with
+`Q(|x|)` phases and the original mover-dependent real-message count at every `x`, then
+`ZK ρ R`. [PS10, Theorem 175.1; Gol01, §4.3.4].
+
+**Proof sketch.** Apply the original zero-knowledge hypothesis to the efficient fixed-tape
+phase verifier, and realize its uniform normalized repeated simulator with one global
+verifier tape. For each auxiliary-input polynomial and distinguisher, the public bounded
+metadata reduction supplies one negligible bound for all local phase gaps, uniformly over
+all witnesses. The actual real-prefix encoding bound places every reached prefix in that
+metadata domain. The conditional hybrid theorem and averaging over verifier tapes multiply
+the common bound by the phase count. Its absolute value is negligible, and multiplication
+by the syntactic polynomial remains negligible. Exact endpoint equivalences identify the
+actual real view and the uniform simulator without changing the advantage or its bound.
+The selector's zero-phase metadata remains nonempty, and all empty-history cases are covered
+by the same endpoint readers. No witness is encoded in advice or used by the simulator. -/
+theorem zk_of_padded_spec {π ρ : Protocol} {R : List Bool → List Bool → Prop}
+    {B : PolyExpr} (h : ZK π R) (hB : π.ProverBounded R B) (Q : PolyExpr)
+    (hspec : ∀ x, PaddedProverSpec π ρ x (Q.eval x.length)
+      (if π.verifierFirst then π.rounds.eval x.length / 2
+        else (π.rounds.eval x.length + 1) / 2)) : ZK ρ R := by
+  apply (ZK_iff ρ R).2
+  intro V hV
+  -- Choose one simulator before the auxiliary bound and distinguisher are supplied.
+  obtain ⟨S, hS, hclose⟩ := (ZK_iff π R).1 h (phaseVerifier V)
+    (phaseVerifier_efficient (V := V) hV)
+  obtain ⟨SQ, hSQ, hcoins, hsim⟩ :=
+    exists_phaseSimulator S hS π.rounds B Q V.coins π.verifierFirst
+  refine ⟨SQ, hSQ, ?_⟩
+  intro Lz D
+  obtain ⟨ε, hε, hphase⟩ := exists_negligible_phase_bound π R V S hS hclose Lz D Q B
+  have habs : Negligible (fun n => |ε n|) := hε.mono ⟨0, fun n _ => by rw [abs_abs]⟩
+  refine ⟨(fun n => (Q.eval n : ℝ) * |ε n|), habs.polyExpr_mul Q, ?_⟩
+  intro x y z hxy hz
+  have hbound : ∀ r hist, (π.P.next x y r hist).length ≤ B.eval x.length :=
+    fun r hist => (Protocol.proverBounded_iff π R B).1 hB x y r hist hxy
+  -- Every actual real prefix lies in the polynomial encoded-prefix envelope.
+  have hlocal (rV : V.Coins x.length) (i : ℕ) (hi : i < Q.eval x.length)
+      (coins : Fin i → π.P.Coins x.length) :
+      phaseGap π V S B Q x y z (List.ofFn rV) (D.distinguisherL x.length) i
+        (realPrefix π V x y z (List.ofFn rV)
+          (if π.verifierFirst then π.rounds.eval x.length / 2
+            else (π.rounds.eval x.length + 1) / 2) i coins) ≤ |ε x.length| := by
+    apply hphase x y z (List.ofFn rV) i _ hxy hz
+    · rw [List.length_ofFn]
+    · exact hi
+    · have hb := (hspec x).realPrefix_bounds V y z (List.ofFn rV) i hi.le
+        (B.eval x.length) hbound coins
+      exact hb.2.2.trans (Nat.mul_le_mul_right (2 * B.eval x.length + 2)
+        (Nat.mul_le_mul_right (π.rounds.eval x.length) hi.le))
+  have hprefix := prefix_distAdv_joint_le S B Q (hspec x) V y z
+    (D.distinguisherL x.length) rfl hbound |ε x.length| (abs_nonneg _) hlocal
+  -- Reindex the actual real and simulator tapes using their published endpoint equations.
+  have hlen : SQ.coinLen x.length =
+      V.coinLen x.length + Q.eval x.length * S.coinLen x.length := by
+    rw [NUPPT.coinLen_eq, hcoins, PolyExpr.eval_add, PolyExpr.eval_mul,
+      Strategy.coinLen_eq, NUPPT.coinLen_eq]
+  with_reducible exact ((distAdv_view_endpoints (hspec x) V y z S SQ B rfl hlen
+    (fun r => by simpa only [Strategy.coinLen_eq] using hsim x z r)
+    (D.distinguisherL x.length)).trans_le hprefix)
+
+end TCSlib.Cryptography.SequentialZK
diff --git a/TCSlib/Cryptography/Composability/SequentialZK/Congruence.lean b/TCSlib/Cryptography/Composability/SequentialZK/Congruence.lean
new file mode 100644
index 000000000..a51b13d63
--- /dev/null
+++ b/TCSlib/Cryptography/Composability/SequentialZK/Congruence.lean
@@ -0,0 +1,68 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.ZeroKnowledge.Interaction
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Execution congruence on the reached histories
+
+## Main definitions
+
+This module introduces no definitions.
+
+## Main results
+
+* `Composability.exec_congr_reachable`: two executions agree up to `g` moves when the
+  parties' replies agree at each active move on the histories reached by the source run.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §4.4 (interactive executions) and Theorem 175.1 (sequential composition).
+-/
+
+namespace TCSlib.Cryptography.Composability
+
+/-- For source strategies `P`, `V`, target strategies `P2`, `V2`, mover flag `vFirst`,
+common input `x`, auxiliary inputs `zP`, `zV`, source tapes `rP`, `rV`, target tapes `rP2`,
+`rV2`, and move bound `g`, suppose the active source and target strategies give the same
+reply on the source run's received history at every `t < g`. Then
+`exec P V vFirst x zP zV rP rV g = exec P2 V2 vFirst x zP zV rP2 rV2 g`.
+[PS10, §4.4].
+
+**Proof sketch.** Induct on the move bound. The histories are empty at zero. At the next
+move, the induction hypothesis identifies the two earlier transcripts, so both active
+strategies read the same source history. The appropriate reply hypothesis makes the
+appended messages agree, preserving equality of the transcripts. -/
+theorem exec_congr_reachable (P V P2 V2 : Strategy) (vFirst : Bool)
+    (x zP zV rP rV rP2 rV2 : List Bool) (g : ℕ)
+    (hP : ∀ t < g, moverIsV vFirst t = false →
+      P.next x zP rP (exec P V vFirst x zP zV rP rV t).1 =
+        P2.next x zP rP2 (exec P V vFirst x zP zV rP rV t).1)
+    (hV : ∀ t < g, moverIsV vFirst t = true →
+      V.next x zV rV (exec P V vFirst x zP zV rP rV t).2 =
+        V2.next x zV rV2 (exec P V vFirst x zP zV rP rV t).2) :
+    exec P V vFirst x zP zV rP rV g = exec P2 V2 vFirst x zP zV rP2 rV2 g := by
+  revert hP hV
+  induction g with
+  | zero =>
+    intro _ _
+    rw [exec_zero, exec_zero]
+  | succ g ih =>
+    intro hP hV
+    have hprev := ih (fun t ht => hP t (by omega)) (fun t ht => hV t (by omega))
+    -- Read both next moves on the common earlier transcript.
+    rw [exec_succ, exec_succ, ← hprev]
+    by_cases hm : moverIsV vFirst g = true
+    · simp only [hm, if_true]
+      rw [hV g (Nat.lt_succ_self g) hm]
+    · simp only [Bool.not_eq_true] at hm
+      simp only [hm, Bool.false_eq_true, if_false]
+      rw [hP g (Nat.lt_succ_self g) hm]
+
+end TCSlib.Cryptography.Composability
diff --git a/TCSlib/Cryptography/Composability/SequentialZK/ContinuationProbability.lean b/TCSlib/Cryptography/Composability/SequentialZK/ContinuationProbability.lean
new file mode 100644
index 000000000..39fc4f186
--- /dev/null
+++ b/TCSlib/Cryptography/Composability/SequentialZK/ContinuationProbability.lean
@@ -0,0 +1,370 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Composability.SequentialZK.SuffixLaws
+import TCSlib.Cryptography.Composability.SequentialZK.ComputationalReduction
+import TCSlib.Cryptography.Composability.SequentialZK.NormalizedStep
+import TCSlib.Cryptography.Composability.SequentialZK.PaddedProverSpec
+import TCSlib.Cryptography.Pseudorandom.Indistinguishability
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Acceptance potentials for simulated continuations
+
+## Main definitions
+
+* `continuationProb` is the acceptance probability after the remaining normalized phases.
+* `phaseGap` is the local raw real-view/simulator gap through the normalized continuation.
+
+## Main results
+
+* `acceptProb_prod` averages acceptance over the first sampler-seed coordinate.
+* `acceptProb_update_tuple` specializes the published uniform-coordinate replacement law.
+* `continuationProb_bellman` separates a fresh normalized simulator call from its suffix.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  Theorem 175.1 (sequential repetition of zero knowledge).
+-/
+
+namespace TCSlib.Cryptography.SequentialZK
+
+open Complexity
+
+/-- Acceptance over sampler seeds `A×B` is the average over `a:A` of acceptance over `B`.
+`acceptProb F D = uexp (fun a => acceptProb (fun b => F (a, b)) D)`. -/
+theorem acceptProb_prod {A B O C : Type*} [Fintype A] [Fintype B] [Fintype C]
+    (F : A × B → O) (D : O → C → Bool) :
+    acceptProb F D = uexp (fun a => acceptProb (fun b => F (a, b)) D) := by
+  rw [acceptProb_def, ← uprob_comp_equiv (Equiv.prodAssoc A B C).symm, uprob_prod]
+  simp only [acceptProb_def, Equiv.prodAssoc_symm_apply]
+
+/-- Replacing coordinate `i` of a uniform tuple by an independent uniform value leaves
+acceptance unchanged: `Pr[D(F(update table i fresh))] = Pr[D(F table)]`. -/
+theorem acceptProb_update_tuple {I A O C : Type*} [DecidableEq I] [Fintype I]
+    [Fintype A] [Nonempty A] [Fintype C] (i : I) (F : (I → A) → O)
+    (D : O → C → Bool) :
+    acceptProb (fun r : A × (I → A) => F (Function.update r.2 i r.1)) D =
+      acceptProb F D := by
+  have hupdate := acceptProb_update (τ := Unit) i (fun table _ => F table) D
+  have hleft :
+      acceptProb (fun r : (A × (I → A)) × Unit =>
+        F (Function.update r.1.2 i r.1.1)) D =
+      acceptProb (fun r : A × ((I → A) × Unit) =>
+        F (Function.update r.2.1 i r.1)) D :=
+    acceptProb_comp_equiv (Equiv.prodAssoc A (I → A) Unit)
+      (fun r : A × ((I → A) × Unit) => F (Function.update r.2.1 i r.1)) D
+  rw [acceptProb_fst (τ := Unit)
+    (fun r : A × (I → A) => F (Function.update r.2 i r.1)) D] at hleft
+  exact hleft.trans (hupdate.trans (acceptProb_fst F D))
+
+/-- If `post (raw (a,z)) b = F a b` and `Z` is nonempty, post-processing `raw` with fresh
+`B` coins and applying `D` has acceptance `E_a[acceptProb (F a) D]`. -/
+theorem acceptProb_postprocess_fst {A Z B Raw O C : Type*}
+    [Fintype A] [Fintype Z] [Nonempty Z] [Fintype B] [Fintype C]
+    (raw : A × Z → Raw) (post : Raw → B → O) (F : A → B → O)
+    (hpoint : ∀ a z b, post (raw (a, z)) b = F a b) (D : O → C → Bool) :
+    acceptProb raw (fun out (r : B × C) => D (post out r.1) r.2) =
+      uexp (fun a => acceptProb (F a) D) := by
+  rw [acceptProb_bind, acceptProb_prod]
+  have hfunctions : (fun r : A × Z => acceptProb (fun b => post (raw r) b) D) =
+      (fun r : A × Z => acceptProb (F r.1) D) := by
+    funext r
+    congr 1
+    funext b
+    exact hpoint r.1 r.2 b
+  rw [hfunctions]
+  exact HardcoreBit.uexp_fst (β := Z) (fun a : A => acceptProb (F a) D)
+
+/-- `continuationProb … D i pre` is acceptance by `D` after simulating phases
+`i,…,Q(|x|)-1` from `pre`, with an independent full table of `Q(|x|)` simulator tapes.
+Only the suffix's own blocks are used. [PS10, Theorem 175.1, hybrid continuation potential].
+`continuationProb S k B Q verifierFirst x z rV D i pre = acceptProb (fun coins : Fin (Q.eval
+x.length) → S.Coins x.length => View.encode ⟨x, z, rV, phaseSuffix S k B verifierFirst x z rV
+(List.ofFn ((FunFamily.blocks (Q.eval x.length) …`.
+-/
+noncomputable def continuationProb {C : Type*} [Fintype C]
+    (S : NUPPT) (k B Q : PolyExpr) (verifierFirst : Bool) (x z rV : List Bool)
+    (D : List Bool → C → Bool) (i : ℕ) (pre : List (List Bool)) : ℝ :=
+  acceptProb (fun coins : Fin (Q.eval x.length) → S.Coins x.length =>
+    View.encode ⟨x, z, rV, phaseSuffix S k B verifierFirst x z rV
+      (List.ofFn ((FunFamily.blocks (Q.eval x.length) (S.coinLen x.length)).symm coins))
+      i pre (Q.eval x.length - i)⟩) D
+
+/-- The defining equation of `continuationProb` is the acceptance of the canonical view
+whose message list is the remaining `phaseSuffix`, sampled from the full typed coin table.
+`continuationProb S k B Q verifierFirst x z rV D i pre = acceptProb (fun coins : Fin (Q.eval
+x.length) → S.Coins x.length => View.encode ⟨x, z, rV, phaseSuffix S k B verifierFirst x z rV
+(List.ofFn ((FunFamily.blocks (Q.eval x.length) …`. -/
+theorem continuationProb_eq {C : Type*} [Fintype C]
+    (S : NUPPT) (k B Q : PolyExpr) (verifierFirst : Bool) (x z rV : List Bool)
+    (D : List Bool → C → Bool) (i : ℕ) (pre : List (List Bool)) :
+    continuationProb S k B Q verifierFirst x z rV D i pre =
+      acceptProb (fun coins : Fin (Q.eval x.length) → S.Coins x.length =>
+        View.encode ⟨x, z, rV, phaseSuffix S k B verifierFirst x z rV
+          (List.ofFn ((FunFamily.blocks (Q.eval x.length) (S.coinLen x.length)).symm coins))
+          i pre (Q.eval x.length - i)⟩) D := rfl
+
+/-- For `i<Q(|x|)`, the continuation potential equals acceptance after one fresh typed
+simulator update at `i`, then the remaining suffix on an independent full simulator table.
+
+**Proof sketch.** Reseed table entry `i` independently using the published uniform-update
+law. The front-step suffix reader makes that entry the current normalized update. Every
+later suffix block has index greater than `i`, so overwriting entry `i` leaves the remaining
+suffix unchanged. The resulting sampler is the desired independent current coin and suffix.
+-/
+theorem continuationProb_bellman {C : Type*} [Fintype C]
+    (S : NUPPT) (k B Q : PolyExpr) (verifierFirst : Bool) (x z rV : List Bool)
+    (D : List Bool → C → Bool) (i : ℕ) (hi : i < Q.eval x.length)
+    (pre : List (List Bool)) :
+    continuationProb S k B Q verifierFirst x z rV D i pre =
+      acceptProb (fun r : S.Coins x.length × (Fin (Q.eval x.length) → S.Coins x.length) =>
+        View.encode ⟨x, z, rV, phaseSuffix S k B verifierFirst x z rV
+          (List.ofFn ((FunFamily.blocks (Q.eval x.length) (S.coinLen x.length)).symm r.2))
+          (i + 1)
+          (simStep S x z rV (k.eval x.length) (B.eval x.length)
+            (if verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2)
+            i pre r.1) (Q.eval x.length - (i + 1))⟩) D := by
+  let F : (Fin (Q.eval x.length) → S.Coins x.length) → List Bool := fun coins =>
+    View.encode ⟨x, z, rV, phaseSuffix S k B verifierFirst x z rV
+      (List.ofFn ((FunFamily.blocks (Q.eval x.length) (S.coinLen x.length)).symm coins))
+      i pre (Q.eval x.length - i)⟩
+  -- Independently reseed the current table entry without changing its uniform law.
+  have hupdate := acceptProb_update_tuple (⟨i, hi⟩ : Fin (Q.eval x.length)) F D
+  -- Separate that entry as the current update; all future blocks ignore the overwrite.
+  have hpoint (r : S.Coins x.length × (Fin (Q.eval x.length) → S.Coins x.length)) :
+      F (Function.update r.2 ⟨i, hi⟩ r.1) =
+        View.encode ⟨x, z, rV, phaseSuffix S k B verifierFirst x z rV
+          (List.ofFn ((FunFamily.blocks (Q.eval x.length) (S.coinLen x.length)).symm r.2))
+          (i + 1)
+          (simStep S x z rV (k.eval x.length) (B.eval x.length)
+            (if verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2)
+            i pre r.1) (Q.eval x.length - (i + 1))⟩ := by
+    have hblock := FunFamily.ofFn_blocks (Q.eval x.length) (S.coinLen x.length)
+      ((FunFamily.blocks (Q.eval x.length) (S.coinLen x.length)).symm
+        (Function.update r.2 ⟨i, hi⟩ r.1)) ⟨i, hi⟩
+    rw [Equiv.apply_symm_apply, Function.update_self] at hblock
+    have hcoin : coinBlock (S.coinLen x.length) i
+        (List.ofFn ((FunFamily.blocks (Q.eval x.length) (S.coinLen x.length)).symm
+          (Function.update r.2 ⟨i, hi⟩ r.1))) = List.ofFn r.1 :=
+      (coinBlock_eq _ _ _).trans hblock.symm
+    dsimp only [F]
+    rw [show Q.eval x.length - i = (Q.eval x.length - (i + 1)) + 1 by omega,
+      phaseSuffix_front, phaseStep_eq_simStep S k B verifierFirst x z rV _ i pre r.1 hcoin,
+      phaseSuffix_update_before S k B verifierFirst x z rV (Q.eval x.length) r.2
+        ⟨i, hi⟩ r.1 (i + 1) _ (Q.eval x.length - (i + 1))
+        (by change i < i + 1; omega) (by omega)]
+  rw [continuationProb_eq]
+  exact hupdate.symm.trans (congrArg (fun sampler => acceptProb sampler D) (funext hpoint))
+
+/-- For a bounded honest prover and padded-prover specification `d`, the raw original
+phase view, normalized and passed to `phaseContinuation`, has acceptance equal to the
+average next continuation potential of `realStep`. The wrapper's zero verifier coins
+are removed through the public uniform-product laws.
+`acceptProb (fun r : (π.withV (phaseVerifier V)).ExecCoins (π.withV (phaseVerifier V)).P x =>
+((π.withV (phaseVerifier V)).viewV x y (phaseAux z rV i pre) r).encode) (fun raw (r : (Fin (Q.eval
+x.length) → S.Coins x.length) × C) => D …`.
+
+**Proof sketch.** The published real-view fixed point identifies normalized messages with
+the original phase's verifier history. The specification supplies its exact message count;
+the caller supplies the uniform prover-message bound. The continuation then starts from
+exactly `realStep`. Its value is independent of the wrapper's zero-bit verifier tape, so
+averaging and projecting that factor leaves the expectation over the original prover coins.
+-/
+theorem continuationProb_real {C : Type*} [Fintype C] {π ρ : Protocol}
+    (S : NUPPT) (B Q : PolyExpr) {x : List Bool} {p : ℕ}
+    (d : PaddedProverSpec π ρ x (Q.eval x.length) p) (V : Strategy)
+    (y z rV : List Bool) (D : List Bool → C → Bool)
+    (hp : p = if π.verifierFirst then π.rounds.eval x.length / 2
+      else (π.rounds.eval x.length + 1) / 2)
+    (hbound : ∀ r hist, (π.P.next x y r hist).length ≤ B.eval x.length)
+    (i : ℕ) (pre : List (List Bool)) :
+    acceptProb
+      (fun r : (π.withV (phaseVerifier V)).ExecCoins (π.withV (phaseVerifier V)).P x =>
+        ((π.withV (phaseVerifier V)).viewV x y (phaseAux z rV i pre) r).encode)
+      (fun raw (r : (Fin (Q.eval x.length) → S.Coins x.length) × C) =>
+        D (phaseContinuation S π.rounds B Q π.verifierFirst x z rV i pre raw
+          (List.ofFn ((FunFamily.blocks (Q.eval x.length) (S.coinLen x.length)).symm r.1)))
+          r.2) =
+      uexp (fun coin : π.P.Coins x.length =>
+        continuationProb S π.rounds B Q π.verifierFirst x z rV D (i + 1)
+          (realStep π V x y z rV p i pre coin)) := by
+  let aux := phaseAux z rV i pre
+  -- Build the seed conversion from public field readers, without reducing `withV`.
+  let eP : π.P.Coins x.length ≃ (π.withV (phaseVerifier V)).P.Coins x.length :=
+    Equiv.arrowCongr (finCongr (by rw [Protocol.withV_P])) (Equiv.refl Bool)
+  let eV := (π.withV_vCoinsEquiv (phaseVerifier V) x.length).symm
+  let e : π.P.Coins x.length × (phaseVerifier V).Coins x.length ≃
+      (π.withV (phaseVerifier V)).ExecCoins (π.withV (phaseVerifier V)).P x :=
+    eP.prodCongr eV
+  have heP (a : π.P.Coins x.length) (v : (phaseVerifier V).Coins x.length) :
+      List.ofFn (e (a, v)).1 = List.ofFn a := by
+    change List.ofFn (eP a) = List.ofFn a
+    exact (List.ofFn_congr (show π.P.coinLen x.length =
+      (π.withV (phaseVerifier V)).P.coinLen x.length by rw [Protocol.withV_P]) a).symm
+  have heV (a : π.P.Coins x.length) (v : (phaseVerifier V).Coins x.length) :
+      List.ofFn (e (a, v)).2 = List.ofFn v := by
+    change List.ofFn (eV v) = List.ofFn v
+    have hv := π.withV_vCoinsEquiv_ofFn (phaseVerifier V) x.length
+      ((π.withV_vCoinsEquiv (phaseVerifier V) x.length).symm v)
+    rw [Equiv.apply_symm_apply] at hv
+    exact hv.symm
+  let raw : π.P.Coins x.length × (phaseVerifier V).Coins x.length → List Bool :=
+    fun r => ((π.withV (phaseVerifier V)).viewV x y aux (e r)).encode
+  have hraw (a : π.P.Coins x.length) (v : (phaseVerifier V).Coins x.length) :
+      raw (a, v) =
+        View.encode ⟨x, aux, List.ofFn v,
+          (exec π.P (phaseVerifier V) π.verifierFirst x y aux (List.ofFn a)
+            (List.ofFn v) (π.rounds.eval x.length)).2⟩ := by
+    dsimp only [raw]
+    rw [Protocol.viewV_withV, heP a v, heV a v]
+  -- Normalize at the converted actual seed, then read both tapes through their equations.
+  have hfixed (a : π.P.Coins x.length) (v : (phaseVerifier V).Coins x.length) :
+      normalizePhaseMsgs x aux p (B.eval x.length)
+          (View.encode ⟨x, aux, List.ofFn v,
+            (exec π.P (phaseVerifier V) π.verifierFirst x y aux (List.ofFn a)
+              (List.ofFn v) (π.rounds.eval x.length)).2⟩) =
+        (exec π.P (phaseVerifier V) π.verifierFirst x y aux (List.ofFn a) []
+          (π.rounds.eval x.length)).2 := by
+    have hc : (π.withV (phaseVerifier V)).V.coinLen x.length = 0 := by
+      rw [Protocol.withV_V, phaseVerifier_coinLen]
+    have hb : ∀ r hist,
+        ((π.withV (phaseVerifier V)).P.next x y r hist).length ≤ B.eval x.length := by
+      simpa only [Protocol.withV_P] using hbound
+    have hn (rP : List Bool) :
+        (exec (π.withV (phaseVerifier V)).P (π.withV (phaseVerifier V)).V
+          (π.withV (phaseVerifier V)).verifierFirst x y aux rP []
+          ((π.withV (phaseVerifier V)).rounds.eval x.length)).2.length = p := by
+      simp only [Protocol.withV_P, Protocol.withV_V, Protocol.withV_verifierFirst,
+        Protocol.withV_rounds]
+      exact d.original_count (phaseVerifier V) y aux rP []
+    have hf := normalizePhaseMsgs_viewV (π.withV (phaseVerifier V)) x y aux p
+      (B.eval x.length) hc hb hn (e (a, v))
+    change normalizePhaseMsgs x aux p (B.eval x.length) (raw (a, v)) = _ at hf
+    rw [hraw a v, heP a v] at hf
+    simpa only [Protocol.withV_P, Protocol.withV_V, Protocol.withV_verifierFirst,
+      Protocol.withV_rounds] using hf
+  let post := fun out (coins : Fin (Q.eval x.length) → S.Coins x.length) =>
+    phaseContinuation S π.rounds B Q π.verifierFirst x z rV i pre out
+      (List.ofFn ((FunFamily.blocks (Q.eval x.length) (S.coinLen x.length)).symm coins))
+  let F := fun (a : π.P.Coins x.length)
+      (coins : Fin (Q.eval x.length) → S.Coins x.length) =>
+    View.encode ⟨x, z, rV, phaseSuffix S π.rounds B π.verifierFirst x z rV
+      (List.ofFn ((FunFamily.blocks (Q.eval x.length) (S.coinLen x.length)).symm coins))
+      (i + 1) (realStep π V x y z rV p i pre a) (Q.eval x.length - (i + 1))⟩
+  have hpoint (a : π.P.Coins x.length) (v : (phaseVerifier V).Coins x.length)
+      (coins : Fin (Q.eval x.length) → S.Coins x.length) : post (raw (a, v)) coins =
+      F a coins := by
+    dsimp only [post, F]
+    rw [phaseContinuation_eq, realStep_eq]
+    dsimp only
+    rw [← hp, hraw a v, hfixed a v]
+  -- Reindex the actual execution law before removing the unused wrapper-tape factor.
+  have hindex := acceptProb_comp_equiv e
+    (fun r : (π.withV (phaseVerifier V)).ExecCoins (π.withV (phaseVerifier V)).P x =>
+      ((π.withV (phaseVerifier V)).viewV x y aux r).encode)
+    (fun out (r : (Fin (Q.eval x.length) → S.Coins x.length) × C) => D (post out r.1) r.2)
+  have hreal := acceptProb_postprocess_fst raw post F hpoint D
+  simpa only [continuationProb_eq] using hindex.symm.trans hreal
+
+/-- For `i<Q(|x|)`, the simulated raw phase passed to `phaseContinuation` has acceptance
+exactly `continuationProb … i pre`, with an independent full table of suffix coins.
+
+**Proof sketch.** Move the independent suffix coins into the simulated sampler. The
+published continuation equation is exactly one typed normalized simulator step followed
+by the remaining suffix. The Bellman reader identifies this sampler's acceptance with
+the original continuation potential. -/
+theorem continuationProb_sim {C : Type*} [Fintype C]
+    (S : NUPPT) (k B Q : PolyExpr) (verifierFirst : Bool) (x z rV : List Bool)
+    (D : List Bool → C → Bool) (i : ℕ) (hi : i < Q.eval x.length)
+    (pre : List (List Bool)) :
+    acceptProb (S.simulate x (phaseAux z rV i pre))
+      (fun raw (r : (Fin (Q.eval x.length) → S.Coins x.length) × C) =>
+        D (phaseContinuation S k B Q verifierFirst x z rV i pre raw
+          (List.ofFn ((FunFamily.blocks (Q.eval x.length) (S.coinLen x.length)).symm r.1)))
+          r.2) = continuationProb S k B Q verifierFirst x z rV D i pre := by
+  -- Expose the fresh simulator coin and the independent full suffix table.
+  rw [acceptProb_bind (S.simulate x (phaseAux z rV i pre))
+    (fun raw (coins : Fin (Q.eval x.length) → S.Coins x.length) =>
+      phaseContinuation S k B Q verifierFirst x z rV i pre raw
+        (List.ofFn ((FunFamily.blocks (Q.eval x.length) (S.coinLen x.length)).symm coins))) D]
+  let F := fun r : S.Coins x.length × (Fin (Q.eval x.length) → S.Coins x.length) =>
+    View.encode ⟨x, z, rV, phaseSuffix S k B verifierFirst x z rV
+      (List.ofFn ((FunFamily.blocks (Q.eval x.length) (S.coinLen x.length)).symm r.2))
+      (i + 1)
+      (simStep S x z rV (k.eval x.length) (B.eval x.length)
+        (if verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2)
+        i pre r.1) (Q.eval x.length - (i + 1))⟩
+  have hpoint :
+      (fun r : S.Coins x.length × (Fin (Q.eval x.length) → S.Coins x.length) =>
+        phaseContinuation S k B Q verifierFirst x z rV i pre
+          (S.simulate x (phaseAux z rV i pre) r.1)
+          (List.ofFn ((FunFamily.blocks (Q.eval x.length) (S.coinLen x.length)).symm r.2))) =
+        F := by
+    funext r
+    dsimp only [F]
+    rw [phaseContinuation_eq, simStep_eq]
+  rw [hpoint]
+  exact (continuationProb_bellman S k B Q verifierFirst x z rV D i hi pre).symm
+
+/-- The local raw-view gap at `i,pre`: original `π.P` against the fixed-tape phase verifier
+versus `S.simulate`, tested by the normalized `phaseContinuation` with independent full
+simulator-table coins and `D` coins. The witness `y` appears only in the mathematical real
+sampler. [PS10, Theorem 175.1, one-phase hybrid gap].
+`phaseGap π V S B Q x y z rV D i pre = distAdv (fun r : (π.withV (phaseVerifier V)).ExecCoins
+(π.withV (phaseVerifier V)).P x => ((π.withV (phaseVerifier V)).viewV x y (phaseAux z rV i pre)
+r).encode) (S.simulate x (phaseAux z rV i pre)) …`. -/
+noncomputable def phaseGap {C : Type*} [Fintype C] (π : Protocol) (V : Strategy)
+    (S : NUPPT) (B Q : PolyExpr) (x y z rV : List Bool) (D : List Bool → C → Bool)
+    (i : ℕ) (pre : List (List Bool)) : ℝ :=
+  distAdv
+    (fun r : (π.withV (phaseVerifier V)).ExecCoins (π.withV (phaseVerifier V)).P x =>
+      ((π.withV (phaseVerifier V)).viewV x y (phaseAux z rV i pre) r).encode)
+    (S.simulate x (phaseAux z rV i pre))
+    (fun raw (r : (Fin (Q.eval x.length) → S.Coins x.length) × C) =>
+      D (phaseContinuation S π.rounds B Q π.verifierFirst x z rV i pre raw
+        (List.ofFn ((FunFamily.blocks (Q.eval x.length) (S.coinLen x.length)).symm r.1))) r.2)
+
+/-- The defining equation of `phaseGap` is the displayed raw real-view/simulator
+`distAdv` after `phaseContinuation`, using a full independent typed simulator table.
+`phaseGap π V S B Q x y z rV D i pre = distAdv (fun r : (π.withV (phaseVerifier V)).ExecCoins
+(π.withV (phaseVerifier V)).P x => ((π.withV (phaseVerifier V)).viewV x y (phaseAux z rV i pre)
+r).encode) (S.simulate x (phaseAux z rV i pre)) …`. -/
+theorem phaseGap_eq {C : Type*} [Fintype C] (π : Protocol) (V : Strategy)
+    (S : NUPPT) (B Q : PolyExpr) (x y z rV : List Bool) (D : List Bool → C → Bool)
+    (i : ℕ) (pre : List (List Bool)) :
+    phaseGap π V S B Q x y z rV D i pre =
+      distAdv
+        (fun r : (π.withV (phaseVerifier V)).ExecCoins (π.withV (phaseVerifier V)).P x =>
+          ((π.withV (phaseVerifier V)).viewV x y (phaseAux z rV i pre) r).encode)
+        (S.simulate x (phaseAux z rV i pre))
+        (fun raw (r : (Fin (Q.eval x.length) → S.Coins x.length) × C) =>
+          D (phaseContinuation S π.rounds B Q π.verifierFirst x z rV i pre raw
+            (List.ofFn ((FunFamily.blocks (Q.eval x.length) (S.coinLen x.length)).symm r.1)))
+            r.2) := rfl
+
+/-- For a bounded real prover, the local raw-view gap `phaseGap` is exactly the absolute
+drift of `continuationProb` under the real next phase, for `i<Q(|x|)`. -/
+theorem phaseGap_eq_drift {C : Type*} [Fintype C] {π ρ : Protocol}
+    (S : NUPPT) (B Q : PolyExpr) {x : List Bool} {p : ℕ}
+    (d : PaddedProverSpec π ρ x (Q.eval x.length) p) (V : Strategy)
+    (y z rV : List Bool) (D : List Bool → C → Bool)
+    (hp : p = if π.verifierFirst then π.rounds.eval x.length / 2
+      else (π.rounds.eval x.length + 1) / 2)
+    (hbound : ∀ r hist, (π.P.next x y r hist).length ≤ B.eval x.length)
+    (i : ℕ) (hi : i < Q.eval x.length) (pre : List (List Bool)) :
+    phaseGap π V S B Q x y z rV D i pre =
+      |uexp (fun coin : π.P.Coins x.length =>
+        continuationProb S π.rounds B Q π.verifierFirst x z rV D (i + 1)
+          (realStep π V x y z rV p i pre coin)) -
+        continuationProb S π.rounds B Q π.verifierFirst x z rV D i pre| := by
+  rw [phaseGap_eq, distAdv_def,
+    continuationProb_real S B Q d V y z rV D hp hbound i pre,
+    continuationProb_sim S π.rounds B Q π.verifierFirst x z rV D i hi pre]
+
+end TCSlib.Cryptography.SequentialZK
diff --git a/TCSlib/Cryptography/Composability/SequentialZK/Efficiency.lean b/TCSlib/Cryptography/Composability/SequentialZK/Efficiency.lean
new file mode 100644
index 000000000..445b33622
--- /dev/null
+++ b/TCSlib/Cryptography/Composability/SequentialZK/Efficiency.lean
@@ -0,0 +1,309 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.EfficiencyRep
+import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Machines
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Polynomial-time operations for sequential repetition
+
+The next-message machines for the sequential repetition construction use unary arithmetic,
+encoded-history slices, and one activation of an efficient strategy. The registered iteration
+hosts and the existing graph-protocol machines provide these operations.
+
+## Main definitions
+
+## Main results
+
+* `SeqEfficiency.take_encodeMsgs`: recover a prefix of an encoded message history by a bit cut.
+* `SeqEfficiency.takeMsgs_poly`: the encoded-history prefix cut is polynomial-time.
+* `SeqEfficiency.phase_poly`, `phase_efficient`: an efficient strategy gives efficient phase moves.
+* `SeqEfficiency.verdict_poly`, `verifier_efficient`: all-phase verdicts and repeated verification
+  are efficient.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  Theorem 175.1, efficiency of sequential repetition.
+-/
+
+namespace TCSlib.Cryptography.Composability.SeqEfficiency
+
+open Complexity Turing
+
+/-- For a history `hist` and count `c`, cutting its encoding immediately before the encoding
+of `hist.drop c` gives `Strategy.encodeMsgs (hist.take c)`.
+`(Strategy.encodeMsgs hist).take ((Strategy.encodeMsgs hist).length - (pairSndD^[c]
+(Strategy.encodeMsgs hist)).length) = Strategy.encodeMsgs (hist.take c)`. -/
+theorem take_encodeMsgs (hist : List (List Bool)) (c : ℕ) :
+    (Strategy.encodeMsgs hist).take ((Strategy.encodeMsgs hist).length -
+      (pairSndD^[c] (Strategy.encodeMsgs hist)).length) = Strategy.encodeMsgs (hist.take c) := by
+  rw [GI.iterate_pairSndD_encodeMsgs]
+  have h := congrArg Strategy.encodeMsgs (List.take_append_drop c hist)
+  rw [CommitmentLemmas.encodeMsgs_append] at h
+  rw [← h]
+  simp only [List.length_append, Nat.add_sub_cancel_right, List.take_left]
+
+/-- For polynomial-time `M` and a unary polynomial-time count `c`, the word
+`(M w).take ((M w).length - (pairSndD^[c w] (M w)).length)` is polynomial-time. On an
+encoded history it is the encoding of the first `c w` messages (`take_encodeMsgs`).
+`PolyTimeComputable fun w => (M w).take ((M w).length - (pairSndD^[c w] (M w)).length)`. -/
+theorem takeMsgs_poly {M : List Bool → List Bool} (hM : PolyTimeComputable M)
+    {c : List Bool → ℕ} (hc : PolyTimeComputable fun w => List.replicate (c w) true) :
+    PolyTimeComputable fun w =>
+      (M w).take ((M w).length - (pairSndD^[c w] (M w)).length) :=
+  EncodingMachines.truncate_poly hM
+    (EncodingMachines.unarySub_poly (EncodingMachines.unaryLength_poly hM)
+      (EncodingMachines.unaryLength_poly (ColMachines.iterSnd_poly hM hc)))
+
+/-- If `P` is efficient, a polynomial-time word function computes the padded phase message
+on every interactive layout. For `g = if previousFirst then 2|hist|-1 else 2|hist|` and
+`j = g / (2k(|x|))`, the message is `P.next x z (coinBlock (P.coinLen |x|) j r)
+(hist.drop (j*k(|x|)))` when `g % (2k(|x|)) < k(|x|)`, and `[]` otherwise.
+[PS10, Theorem 175.1, efficiency of a repeated party].
+
+**Proof sketch.** Recover the history length in unary, compute its move index, phase and
+position using the existing unary arithmetic machines, and drop the earlier encoded messages.
+Slice the random tape with the existing coin-block machine. Assemble the original strategy's
+machine layout and run its polynomial-time output function; a conditional emits `[]` in a
+filler position. All malformed word inputs are handled by the existing total projections.
+The equation on actual layouts follows from the published message-count and suffix readers. -/
+theorem phase_poly (P : Strategy) (k : PolyExpr) (previousFirst : Bool) (hP : P.Efficient) :
+    ∃ F : List Bool → List Bool, PolyTimeComputable F ∧
+      ∀ (x z r : List Bool) (hist : List (List Bool)),
+      let g := if previousFirst then 2 * hist.length - 1 else 2 * hist.length
+      let j := g / (2 * k.eval x.length)
+      F (GI.ilayout x z hist r) =
+        if g % (2 * k.eval x.length) < k.eval x.length then
+          P.next x z (coinBlock (P.coinLen x.length) j r)
+            (hist.drop (j * k.eval x.length))
+        else [] := by
+  obtain ⟨A, hA, _, hnext⟩ := (Strategy.efficient_iff P).1 hP
+  let K : List Bool → ℕ := fun w => k.eval (GI.argX w).length
+  let index : List Bool → ℕ := fun w =>
+    if previousFirst then 2 * GI.msgCount (GI.argM w) - 1
+    else 2 * GI.msgCount (GI.argM w)
+  let phase : List Bool → ℕ := fun w => index w / (2 * K w)
+  -- The index and phase are computed entirely by the unary arithmetic toolkit.
+  have hK : PolyTimeComputable fun w => List.replicate (K w) true :=
+    EncodingMachines.unaryPolyOf_poly k (EncodingMachines.unaryLength_poly GI.argX_poly)
+  have hdouble := EncodingMachines.unaryMul_poly (EncodingMachines.unaryConst_poly 2)
+    GI.cnt_poly
+  have hindex : PolyTimeComputable fun w => List.replicate (index w) true := by
+    cases previousFirst
+    · exact hdouble
+    · exact EncodingMachines.unarySub_poly hdouble (EncodingMachines.unaryConst_poly 1)
+  have hden := EncodingMachines.unaryMul_poly (EncodingMachines.unaryConst_poly 2) hK
+  have hphase : PolyTimeComputable fun w => List.replicate (phase w) true := by
+    simpa only [EncodingMachines.divNum_eq] using EncodingMachines.divNum_poly hindex hden
+  have hmod : PolyTimeComputable fun w => List.replicate (index w % (2 * K w)) true := by
+    simpa only [EncodingMachines.modNum_eq] using EncodingMachines.modNum_poly hindex hden
+  have htest := EncodingMachines.ltTest_poly hmod hK
+  -- Reuse the encoded-list iteration and the coin slicing machines.
+  have hdrop := ColMachines.iterSnd_poly GI.argM_poly
+    (EncodingMachines.unaryMul_poly hphase hK)
+  have hcoins : PolyTimeComputable fun w =>
+      coinBlock (P.coins.eval (GI.argX w).length) (phase w) (NUPPT.inCoins w) := by
+    simpa only [List.length_replicate] using
+      GI.coinSlice_poly P.coins GI.argX_poly hphase NUPPT.polyTimeComputable_inCoins
+  have hlay := NUPPT.polyTimeComputable_layout
+    (EncodingMachines.unaryLength_poly GI.argX_poly)
+    ((GI.argX_poly.pairEncode GI.argZ_poly).pairEncode hdrop)
+    (polyTimeComputable_const []) hcoins
+  let F : List Bool → List Bool := fun w =>
+    if index w % (2 * K w) < K w then
+      A.output (NUPPT.layout (List.replicate (GI.argX w).length true)
+        (pairEncode (pairEncode (GI.argX w) (GI.argZ w))
+          (pairSndD^[phase w * K w] (GI.argM w))) []
+        (coinBlock (P.coins.eval (GI.argX w).length) (phase w) (NUPPT.inCoins w)))
+    else []
+  have hF : PolyTimeComputable F := by
+    simpa only [decide_eq_true_eq] using
+      polyTimeComputable_ite htest (A.polyTimeComputable_output.comp hlay)
+        (polyTimeComputable_const [])
+  refine ⟨F, hF, ?_⟩
+  intro x z r hist
+  dsimp only [F, phase, index, K]
+  simp only [GI.argX_ilayout, GI.argZ_ilayout, GI.argM_ilayout, GI.inCoins_ilayout,
+    GI.msgCount_encodeMsgs, GI.iterate_pairSndD_encodeMsgs]
+  rw [hnext, Strategy.ofNUPPT_next, NUPPT.runAtL_eq_output_layout, hA.advice_eq,
+    Strategy.coinLen_eq]
+
+/-- For strategies `S, P`, a round polynomial `k` and orientation `previousFirst`, if `P`
+is efficient and every message of `S` is the padded phase message of `P`, then `S.Efficient`.
+The equation hypothesis uses `g = if previousFirst then 2|hist|-1 else 2|hist|` and
+`j = g / (2k(|x|))`; no hypothesis on the random-tape polynomial of `S` is required.
+[PS10, Theorem 175.1, efficiency of a repeated party]. -/
+theorem phase_efficient (S P : Strategy) (k : PolyExpr) (previousFirst : Bool)
+    (hP : P.Efficient)
+    (hnext : ∀ (x z r : List Bool) (hist : List (List Bool)),
+      let g := if previousFirst then 2 * hist.length - 1 else 2 * hist.length
+      let j := g / (2 * k.eval x.length)
+      S.next x z r hist =
+        if g % (2 * k.eval x.length) < k.eval x.length then
+          P.next x z (coinBlock (P.coinLen x.length) j r)
+            (hist.drop (j * k.eval x.length))
+        else []) : S.Efficient := by
+  obtain ⟨F, hF, heq⟩ := phase_poly P k previousFirst hP
+  apply GI.efficient_of_polyTime S hF
+  intro x z r hist
+  exact (hnext x z r hist).trans (heq x z r hist).symm
+
+/-- If `V` is efficient, a polynomial-time word function computes `[true]` exactly when
+all `Q(|x|)` phase verdicts are `[true]`. Phase `j` uses coin block `j` and the first
+`p = if verifierFirst then k(|x|)/2 else (k(|x|)+1)/2` messages after the first `j*k(|x|)`
+messages. [PS10, Theorem 175.1, efficiency of the repeated verifier].
+
+**Proof sketch.** For a unary phase index, drop the earlier encoded messages and cut out the
+real messages using `takeMsgs_poly`. Run the original verifier's uniform machine on that
+history and the selected coin block. The published bounded first-index search finds the first
+verdict different from `[true]`; its search bound is the unary polynomial `Q(|x|)`. The
+output is `[true]` exactly when the search is exhausted. The empty search is exhausted too,
+so the construction covers `Q(|x|) = 0` and `k(|x|) = 0`. -/
+theorem verdict_poly (V : Strategy) (k Q : PolyExpr) (verifierFirst : Bool)
+    (hV : V.Efficient) :
+    ∃ F : List Bool → List Bool, PolyTimeComputable F ∧
+      ∀ (x z r : List Bool) (hist : List (List Bool)),
+      F (GI.ilayout x z hist r) =
+        if ∀ j < Q.eval x.length,
+          V.next x z (coinBlock (V.coinLen x.length) j r)
+            ((hist.drop (j * k.eval x.length)).take
+              (if verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2)) =
+                [true]
+        then [true] else [false] := by
+  classical
+  obtain ⟨A, hA, _, hnext⟩ := (Strategy.efficient_iff V).1 hV
+  let K : List Bool → ℕ := fun w => k.eval (GI.argX w).length
+  let count : List Bool → ℕ := fun w =>
+    if verifierFirst then K w / 2 else (K w + 1) / 2
+  let act : List Bool → ℕ → List Bool := fun w j =>
+    let M := pairSndD^[j * K w] (GI.argM w)
+    A.output (NUPPT.layout (List.replicate (GI.argX w).length true)
+      (pairEncode (pairEncode (GI.argX w) (GI.argZ w))
+        (M.take (M.length - (pairSndD^[count w] M).length))) []
+      (coinBlock (V.coins.eval (GI.argX w).length) j (NUPPT.inCoins w)))
+  have hK : PolyTimeComputable fun w => List.replicate (K w) true :=
+    EncodingMachines.unaryPolyOf_poly k (EncodingMachines.unaryLength_poly GI.argX_poly)
+  have hcount : PolyTimeComputable fun w => List.replicate (count w) true := by
+    cases verifierFirst
+    · simpa only [EncodingMachines.divNum_eq] using EncodingMachines.divNum_poly
+        (EncodingMachines.unaryAdd_poly hK (EncodingMachines.unaryConst_poly 1))
+        (EncodingMachines.unaryConst_poly 2)
+    · simpa only [EncodingMachines.divNum_eq] using
+        EncodingMachines.divNum_poly hK (EncodingMachines.unaryConst_poly 2)
+  -- The search test is one original verifier activation on a phase slice.
+  have hX := GI.argX_poly.comp polyTimeComputable_pairSndD
+  have hZ := GI.argZ_poly.comp polyTimeComputable_pairSndD
+  have hR := NUPPT.polyTimeComputable_inCoins.comp polyTimeComputable_pairSndD
+  have hJ := EncodingMachines.unaryLength_poly polyTimeComputable_pairFstD
+  have hdrop := ColMachines.iterSnd_poly (GI.argM_poly.comp polyTimeComputable_pairSndD)
+    (EncodingMachines.unaryMul_poly hJ (hK.comp polyTimeComputable_pairSndD))
+  have htake := takeMsgs_poly hdrop (hcount.comp polyTimeComputable_pairSndD)
+  have hcoins : PolyTimeComputable fun w =>
+      coinBlock (V.coins.eval (GI.argX (pairSndD w)).length) (pairFstD w).length
+        (NUPPT.inCoins (pairSndD w)) :=
+    GI.coinSlice_poly V.coins hX polyTimeComputable_pairFstD hR
+  have hact : PolyTimeComputable fun w => act (pairSndD w) (pairFstD w).length :=
+    A.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout
+      (EncodingMachines.unaryLength_poly hX)
+      ((hX.pairEncode hZ).pairEncode htake) (polyTimeComputable_const []) hcoins)
+  have heq : PolyTimeComputable fun w =>
+      [decide (act (pairSndD w) (pairFstD w).length = [true])] := by
+    refine (polyTimeComputable_pairEq.comp
+      (hact.pairEncode (polyTimeComputable_const [true]))).congr fun w => ?_
+    rw [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
+  have hbad : PolyTimeComputable fun w =>
+      [decide (act (pairSndD w) (pairFstD w).length ≠ [true])] := by
+    simpa only [decide_not] using polyTimeComputable_not heq
+  have hQ := EncodingMachines.unaryPolyOf_poly Q
+    (EncodingMachines.unaryLength_poly GI.argX_poly)
+  have hfirst := EncodingMachines.polyTimeComputable_firstIdx
+    (p := fun w j => decide (act w j ≠ [true])) hbad hQ
+  let F : List Bool → List Bool := fun w =>
+    if EncodingMachines.firstIdx (fun j => decide (act w j ≠ [true]))
+        (Q.eval (GI.argX w).length) = Q.eval (GI.argX w).length
+    then [true] else [false]
+  have hF : PolyTimeComputable F := by
+    simpa only [decide_eq_true_eq] using polyTimeComputable_ite
+      (EncodingMachines.eqTest_poly hfirst hQ)
+      (polyTimeComputable_const [true]) (polyTimeComputable_const [false])
+  -- On an actual layout, all operations are read through published equations.
+  have hact_eq : ∀ x z r hist j, act (GI.ilayout x z hist r) j =
+      V.next x z (coinBlock (V.coinLen x.length) j r)
+        ((hist.drop (j * k.eval x.length)).take
+          (if verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2)) := by
+    intro x z r hist j
+    dsimp only [act, K, count]
+    simp only [GI.argX_ilayout, GI.argZ_ilayout, GI.argM_ilayout, GI.inCoins_ilayout]
+    rw [GI.iterate_pairSndD_encodeMsgs (j * k.eval x.length) hist, take_encodeMsgs]
+    rw [hnext, Strategy.ofNUPPT_next, NUPPT.runAtL_eq_output_layout, hA.advice_eq,
+      Strategy.coinLen_eq]
+  refine ⟨F, hF, ?_⟩
+  intro x z r hist
+  dsimp only [F]
+  rw [GI.argX_ilayout]
+  have he : (EncodingMachines.firstIdx
+      (fun j => decide (act (GI.ilayout x z hist r) j ≠ [true])) (Q.eval x.length) =
+        Q.eval x.length) ↔
+      ∀ j < Q.eval x.length,
+        V.next x z (coinBlock (V.coinLen x.length) j r)
+          ((hist.drop (j * k.eval x.length)).take
+            (if verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2)) =
+              [true] := by
+    rw [EncodingMachines.firstIdx_eq_iff]
+    simp only [decide_eq_false_iff_not, not_not, hact_eq]
+  simp only [he]
+
+/-- For strategies `S, V`, round/count polynomials `k, Q` and an orientation `verifierFirst`,
+if `V` is efficient and `S` computes the repeated terminal verdict when `|hist| = Q(|x|)k(|x|)`
+and the padded phase message otherwise, then `S.Efficient`.
+The terminal verdict is `[true]` iff every phase's original verdict is `[true]`.
+[PS10, Theorem 175.1, efficiency of the repeated verifier].
+
+**Proof sketch.** Use `phase_poly` for the nonterminal branch and `verdict_poly` for the
+terminal branch. The branch test compares the encoded history's unary message count with
+the unary product `Q(|x|)k(|x|)`. The polynomial-time conditional computes `S` on every actual
+interactive layout, so `GI.efficient_of_polyTime` supplies its uniform machine. -/
+theorem verifier_efficient (S V : Strategy) (k Q : PolyExpr) (verifierFirst : Bool)
+    (hV : V.Efficient)
+    (hnext : ∀ (x z r : List Bool) (hist : List (List Bool)),
+      let g := if verifierFirst then 2 * hist.length else 2 * hist.length - 1
+      let j := g / (2 * k.eval x.length)
+      S.next x z r hist =
+        if hist.length = Q.eval x.length * k.eval x.length then
+          if ∀ i < Q.eval x.length,
+            V.next x z (coinBlock (V.coinLen x.length) i r)
+              ((hist.drop (i * k.eval x.length)).take
+                (if verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2)) =
+                  [true]
+          then [true] else [false]
+        else if g % (2 * k.eval x.length) < k.eval x.length then
+          V.next x z (coinBlock (V.coinLen x.length) j r)
+            (hist.drop (j * k.eval x.length))
+        else []) : S.Efficient := by
+  classical
+  obtain ⟨Fp, hFp, hep⟩ := phase_poly V k (!verifierFirst) hV
+  obtain ⟨Fv, hFv, hev⟩ := verdict_poly V k Q verifierFirst hV
+  have hQ := EncodingMachines.unaryPolyOf_poly Q
+    (EncodingMachines.unaryLength_poly GI.argX_poly)
+  have hk := EncodingMachines.unaryPolyOf_poly k
+    (EncodingMachines.unaryLength_poly GI.argX_poly)
+  let F : List Bool → List Bool := fun w =>
+    if GI.msgCount (GI.argM w) = Q.eval (GI.argX w).length * k.eval (GI.argX w).length
+    then Fv w else Fp w
+  have hF : PolyTimeComputable F := by
+    simpa only [decide_eq_true_eq] using polyTimeComputable_ite
+      (EncodingMachines.eqTest_poly GI.cnt_poly (EncodingMachines.unaryMul_poly hQ hk))
+      hFv hFp
+  apply GI.efficient_of_polyTime S hF
+  intro x z r hist
+  dsimp only [F]
+  rw [GI.argM_ilayout, GI.msgCount_encodeMsgs, GI.argX_ilayout, hep, hev, hnext]
+  cases verifierFirst <;> rfl
+
+end TCSlib.Cryptography.Composability.SeqEfficiency
diff --git a/TCSlib/Cryptography/Composability/SequentialZK/EndpointSampling.lean b/TCSlib/Cryptography/Composability/SequentialZK/EndpointSampling.lean
new file mode 100644
index 000000000..0d584c66c
--- /dev/null
+++ b/TCSlib/Cryptography/Composability/SequentialZK/EndpointSampling.lean
@@ -0,0 +1,286 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Asymptotic.CollectionsHelpers
+import TCSlib.Cryptography.Asymptotic.Sampling
+import TCSlib.Cryptography.Composability.SequentialZK.PaddedProverSpec
+import TCSlib.Cryptography.Composability.SequentialZK.PrefixLaws
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Uniform tape reindexing at sequential-simulation endpoints
+
+## Main definitions
+
+* `coinTableEquiv` reads a tape of known length as a table of equal-size coin blocks.
+* `coinBlocksEquiv` separates one verifier tape and a table of phase tapes.
+* `PaddedProverSpec.realCoinsEquiv` reindexes real execution coins as verifier and phase coins.
+
+## Main results
+
+* `statClose_reindex` transfers closeness along supplied endpoint equivalences and readers.
+* `PaddedProverSpec.realPrefix_eq_exec` identifies the real fold with the padded execution.
+* `PaddedProverSpec.viewV_eq_realPrefix` gives the actual encoded real-view endpoint.
+* `simulate_eq_simPrefix` identifies a simulator's tape-split endpoint with its typed fold.
+* `statClose_view_endpoints` transfers a joint prefix comparison to the actual encoded views.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  Theorem 175.1 (sequential repetition of zero knowledge).
+-/
+
+namespace TCSlib.Cryptography.SequentialZK
+
+open Complexity
+
+/-- For `hlen : m = q*c`, `coinTableEquiv hlen` reindexes `m` bits as `q` blocks of `c` bits,
+using the canonical finite-index cast and `FunFamily.blocks`. -/
+def coinTableEquiv {m q c : ℕ} (hlen : m = q * c) :
+    (Fin m → Bool) ≃ (Fin q → Fin c → Bool) :=
+  (Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)).trans (FunFamily.blocks q c)
+
+/-- `coinTableEquiv hlen` is the finite-length cast followed by `FunFamily.blocks q c`.
+`coinTableEquiv hlen = (Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)).trans (FunFamily.blocks
+q c)`. -/
+theorem coinTableEquiv_eq {m q c : ℕ} (hlen : m = q * c) :
+    coinTableEquiv hlen =
+      (Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)).trans (FunFamily.blocks q c) := rfl
+
+/-- Block `i` of `r` is the encoding of block `i` of `coinTableEquiv hlen r`.
+`coinBlock c i (List.ofFn r) = List.ofFn (coinTableEquiv hlen r i)`. -/
+theorem coinTableEquiv_block {m q c : ℕ} (hlen : m = q * c) (r : Fin m → Bool)
+    (i : Fin q) :
+    coinBlock c i (List.ofFn r) = List.ofFn (coinTableEquiv hlen r i) := by
+  let e := Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)
+  have hword : List.ofFn (e r) = List.ofFn r := (List.ofFn_congr hlen r).symm
+  have hblock := FunFamily.ofFn_blocks q c (e r) i
+  rw [hword] at hblock
+  exact (coinBlock_eq c i (List.ofFn r)).trans hblock.symm
+
+/-- For `hlen : m = v+q*c`, `coinBlocksEquiv v q c hlen` reads the first `v` bits as a
+verifier tape and the remaining `q*c` bits as the canonical table of `q` phase tapes. -/
+def coinBlocksEquiv {m : ℕ} (v q c : ℕ) (hlen : m = v + q * c) :
+    (Fin m → Bool) ≃ (Fin v → Bool) × (Fin q → Fin c → Bool) :=
+  (Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)).trans
+    ((splitCoins v (q * c)).trans
+      (Equiv.prodCongr (Equiv.refl _) (FunFamily.blocks q c)))
+
+/-- `coinBlocksEquiv v q c hlen` is the finite-length cast, then `splitCoins v (q*c)`,
+then the product of the identity on verifier coins and `FunFamily.blocks q c`.
+`coinBlocksEquiv v q c hlen = (Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)).trans
+((splitCoins v (q * c)).trans (Equiv.prodCongr (Equiv.refl _) (FunFamily.blocks q c)))`. -/
+theorem coinBlocksEquiv_eq {m : ℕ} (v q c : ℕ) (hlen : m = v + q * c) :
+    coinBlocksEquiv v q c hlen =
+      (Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)).trans
+        ((splitCoins v (q * c)).trans
+          (Equiv.prodCongr (Equiv.refl _) (FunFamily.blocks q c))) := rfl
+
+/-- The verifier component of `coinBlocksEquiv v q c hlen r` encodes `(List.ofFn r).take v`.
+`List.ofFn (coinBlocksEquiv v q c hlen r).1 = (List.ofFn r).take v`.
+-/
+theorem coinBlocksEquiv_fst_ofFn {m : ℕ} (v q c : ℕ) (hlen : m = v + q * c)
+    (r : Fin m → Bool) :
+    List.ofFn (coinBlocksEquiv v q c hlen r).1 = (List.ofFn r).take v := by
+  let e := Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)
+  have hword : List.ofFn (e r) = List.ofFn r := (List.ofFn_congr hlen r).symm
+  have hfirst := ofFn_splitCoins_fst v (q * c) (e r)
+  rw [hword] at hfirst
+  exact hfirst
+
+/-- Block `i` of the phase component of `coinBlocksEquiv v q c hlen r` encodes
+`coinBlock c i ((List.ofFn r).drop v)`.
+`coinBlock c i ((List.ofFn r).drop v) = List.ofFn ((coinBlocksEquiv v q c hlen r).2 i)`. -/
+theorem coinBlocksEquiv_block {m : ℕ} (v q c : ℕ) (hlen : m = v + q * c)
+    (r : Fin m → Bool) (i : Fin q) :
+    coinBlock c i ((List.ofFn r).drop v) =
+      List.ofFn ((coinBlocksEquiv v q c hlen r).2 i) := by
+  let e := Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)
+  have hword : List.ofFn (e r) = List.ofFn r := (List.ofFn_congr hlen r).symm
+  have hblock := FunFamily.ofFn_blocks q c (splitCoins v (q * c) (e r)).2 i
+  rw [ofFn_splitCoins_snd, hword] at hblock
+  exact (coinBlock_eq c i ((List.ofFn r).drop v)).trans hblock.symm
+
+/-- If `F,G` are `ε`-close, `eA : A' ≃ A` and `eB : B' ≃ B`, and the endpoint readers
+are `F' a = F (eA a)` and `G' b = G (eB b)`, then `F',G'` are `ε`-close. -/
+theorem statClose_reindex {A B A' B' O : Type*}
+    [Fintype A] [Fintype B] [Fintype A'] [Fintype B']
+    (F : A → O) (G : B → O) (F' : A' → O) (G' : B' → O)
+    (eA : A' ≃ A) (eB : B' ≃ B) (ε : ℝ) (h : StatClose F G ε)
+    (hF : ∀ a, F' a = F (eA a)) (hG : ∀ b, G' b = G (eB b)) :
+    StatClose F' G' ε := by
+  have hindexed := (h.comp_equiv_left eA).comp_equiv_right eB
+  have hleft : (fun a => F (eA a)) = F' := funext fun a => (hF a).symm
+  have hright : (fun b => G (eB b)) = G' := funext fun b => (hG b).symm
+  rw [hleft, hright] at hindexed
+  exact hindexed
+
+namespace PaddedProverSpec
+
+/-- For `h : PaddedProverSpec π ρ x q p`, `j≤q`, and raw prover tape `rP` whose first `j`
+blocks are the typed coins `coins`, the real prefix is exactly the repeated verifier's
+received history after `2*k*j` moves, where `k=π.rounds.eval |x|`.
+[PS10, Theorem 175.1, real endpoint].
+
+**Proof sketch.** Induct on `j`. The empty fold and zero-move execution both have empty
+histories. At a successor, the real-fold reader appends one original phase and empty
+fillers. The published padded-phase reader appends the same messages to the preceding
+execution history. The induction hypothesis identifies the earlier prefixes, and the
+supplied block equation identifies the last prover tape. -/
+theorem realPrefix_eq_exec {π ρ : Protocol} {x : List Bool} {q p : ℕ}
+    (h : PaddedProverSpec π ρ x q p) (V : Strategy) (y z rP rV : List Bool)
+    (j : ℕ) (hj : j ≤ q) (coins : Fin j → π.P.Coins x.length)
+    (hcoins : ∀ i : Fin j,
+      coinBlock (π.P.coinLen x.length) i rP = List.ofFn (coins i)) :
+    realPrefix π V x y z rV p j coins =
+      (exec ρ.P V π.verifierFirst x y z rP rV (2 * π.rounds.eval x.length * j)).2 := by
+  induction j with
+  | zero => rw [realPrefix_zero]; simp only [Nat.mul_zero, exec_zero]
+  | succ j ih =>
+    have hprevious := ih (Nat.le_trans (Nat.le_succ j) hj)
+      (fun i : Fin j => coins i.castSucc) (fun i => by
+        simpa only [Fin.coe_castSucc] using hcoins i.castSucc)
+    have hlast := hcoins (Fin.last j)
+    simp only [Fin.val_last] at hlast
+    have hphase := h.padded_phase V y z rP rV j (by omega)
+    rw [realPrefix_succ, realStep_eq, hprevious, hphase, hlast]
+
+/-- Reindex an actual `ρ.withV V` execution's coins as the verifier tape and the `q`
+original prover tapes. The prover split uses only `h.prover_coinLen`; the verifier part
+uses the published `withV_vCoinsEquiv`.
+`(ρ.withV V).ExecCoins (ρ.withV V).P x ≃ V.Coins x.length × (Fin q → π.P.Coins x.length)`. -/
+def realCoinsEquiv {π ρ : Protocol} {x : List Bool} {q p : ℕ}
+    (h : PaddedProverSpec π ρ x q p) (V : Strategy) :
+    (ρ.withV V).ExecCoins (ρ.withV V).P x ≃
+      V.Coins x.length × (Fin q → π.P.Coins x.length) :=
+  (Equiv.prodCongr
+    (coinTableEquiv (by rw [Protocol.withV_P]; exact h.prover_coinLen))
+    (ρ.withV_vCoinsEquiv V x.length)).trans (Equiv.prodComm _ _)
+
+/-- `h.realCoinsEquiv V` applies `coinTableEquiv` to the prover coins and
+`withV_vCoinsEquiv` to the verifier coins, then swaps the product coordinates.
+`h.realCoinsEquiv V = (Equiv.prodCongr (coinTableEquiv (by rw [Protocol.withV_P]; exact
+h.prover_coinLen)) (ρ.withV_vCoinsEquiv V x.length)).trans (Equiv.prodComm _ _)`. -/
+theorem realCoinsEquiv_eq {π ρ : Protocol} {x : List Bool} {q p : ℕ}
+    (h : PaddedProverSpec π ρ x q p) (V : Strategy) :
+    h.realCoinsEquiv V =
+      (Equiv.prodCongr
+        (coinTableEquiv (by rw [Protocol.withV_P]; exact h.prover_coinLen))
+        (ρ.withV_vCoinsEquiv V x.length)).trans (Equiv.prodComm _ _) := rfl
+
+/-- The verifier component of `h.realCoinsEquiv V r` encodes the original verifier tape.
+`List.ofFn (h.realCoinsEquiv V r).1 = List.ofFn r.2`. -/
+theorem realCoinsEquiv_fst_ofFn {π ρ : Protocol} {x : List Bool} {q p : ℕ}
+    (h : PaddedProverSpec π ρ x q p) (V : Strategy)
+    (r : (ρ.withV V).ExecCoins (ρ.withV V).P x) :
+    List.ofFn (h.realCoinsEquiv V r).1 = List.ofFn r.2 :=
+  ρ.withV_vCoinsEquiv_ofFn V x.length r.2
+
+/-- Block `i` of the repeated prover tape is block `i` of `h.realCoinsEquiv V r`.
+`coinBlock (π.P.coinLen x.length) i (List.ofFn r.1) = List.ofFn ((h.realCoinsEquiv V r).2 i)`. -/
+theorem realCoinsEquiv_block {π ρ : Protocol} {x : List Bool} {q p : ℕ}
+    (h : PaddedProverSpec π ρ x q p) (V : Strategy)
+    (r : (ρ.withV V).ExecCoins (ρ.withV V).P x) (i : Fin q) :
+    coinBlock (π.P.coinLen x.length) i (List.ofFn r.1) =
+      List.ofFn ((h.realCoinsEquiv V r).2 i) :=
+  coinTableEquiv_block (by rw [Protocol.withV_P]; exact h.prover_coinLen) r.1 i
+
+/-- The actual encoded verifier view in `ρ.withV V` is the canonical view of the jointly
+reindexed verifier tape and real prefix. [PS10, Theorem 175.1, real-view endpoint].
+`((ρ.withV V).viewV x y z r).encode = View.encode ⟨x, z, List.ofFn (h.realCoinsEquiv V r).1,
+realPrefix π V x y z (List.ofFn (h.realCoinsEquiv V r).1) p q (h.realCoinsEquiv V r).2⟩`. -/
+theorem viewV_eq_realPrefix {π ρ : Protocol} {x : List Bool} {q p : ℕ}
+    (h : PaddedProverSpec π ρ x q p) (V : Strategy) (y z : List Bool)
+    (r : (ρ.withV V).ExecCoins (ρ.withV V).P x) :
+    ((ρ.withV V).viewV x y z r).encode =
+      View.encode ⟨x, z, List.ofFn (h.realCoinsEquiv V r).1,
+        realPrefix π V x y z (List.ofFn (h.realCoinsEquiv V r).1) p q
+          (h.realCoinsEquiv V r).2⟩ := by
+  rw [h.realCoinsEquiv_fst_ofFn V r]
+  have hprefix := h.realPrefix_eq_exec V y z (List.ofFn r.1) (List.ofFn r.2) q le_rfl
+    (h.realCoinsEquiv V r).2 (fun i => h.realCoinsEquiv_block V r i)
+  rw [Protocol.viewV_withV, h.first, h.rounds_eval, hprefix]
+
+end PaddedProverSpec
+
+/-- Suppose `SQ`'s raw tape is split after `v` bits, and its published endpoint reader
+outputs the canonical view of `phasePrefix` on the remaining phase tape. Reindexing those
+coins by `coinBlocksEquiv` identifies that output with the canonical typed `simPrefix`.
+[PS10, Theorem 175.1, simulator endpoint].
+`SQ.simulate x z r = View.encode ⟨x, z, List.ofFn (coinBlocksEquiv v q (S.coinLen x.length) hlen
+r).1, simPrefix S x z (List.ofFn (coinBlocksEquiv v q (S.coinLen x.length) hlen r).1) (k.eval
+x.length) (B.eval x.length) (if verifierFirst …`. -/
+theorem simulate_eq_simPrefix (S SQ : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
+    (x z : List Bool) (q v : ℕ)
+    (hlen : SQ.coinLen x.length = v + q * S.coinLen x.length)
+    (hsim : ∀ r : SQ.Coins x.length, SQ.simulate x z r =
+      View.encode ⟨x, z, (List.ofFn r).take v,
+        phasePrefix S k B verifierFirst x z ((List.ofFn r).take v)
+          ((List.ofFn r).drop v) q⟩) (r : SQ.Coins x.length) :
+    SQ.simulate x z r =
+      View.encode ⟨x, z, List.ofFn (coinBlocksEquiv v q (S.coinLen x.length) hlen r).1,
+        simPrefix S x z (List.ofFn (coinBlocksEquiv v q (S.coinLen x.length) hlen r).1)
+          (k.eval x.length) (B.eval x.length)
+          (if verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2) q
+          (coinBlocksEquiv v q (S.coinLen x.length) hlen r).2⟩ := by
+  have hprefix := simPrefix_eq_phasePrefix S k B verifierFirst x z
+    ((List.ofFn r).take v) ((List.ofFn r).drop v) q
+    (coinBlocksEquiv v q (S.coinLen x.length) hlen r).2
+    (fun i => coinBlocksEquiv_block v q (S.coinLen x.length) hlen r i)
+  rw [hsim r, coinBlocksEquiv_fst_ofFn, hprefix]
+
+/-- Given the padded-prover contract and the raw split-tape reader for `SQ`, an
+`ε`-closeness bound between joint `(verifier tape, real/simulated prefix)` samplers yields
+`StatClose (fun r => ((ρ.withV V).viewV x y z r).encode) (SQ.simulate x z) ε`.
+The supplied `hp` identifies the numeric real-message count with the simulator's count.
+[PS10, Theorem 175.1, statistical endpoint transfer].
+
+**Proof sketch.** Post-process the joint prefix samplers by canonical view encoding.
+The padded-prover coin equivalence reindexes the real execution as its verifier tape and
+phase prover coins; its published view reader identifies the real endpoint. The canonical
+split/block equivalence reindexes `SQ`'s tape as its verifier and simulator phase coins;
+the typed simulator endpoint reader identifies the other endpoint. Uniform probability
+is invariant under both equivalences, so the original error is preserved exactly. -/
+theorem statClose_view_endpoints {π ρ : Protocol} {x : List Bool} {q p : ℕ}
+    (h : PaddedProverSpec π ρ x q p) (V : Strategy) (y z : List Bool)
+    (S SQ : NUPPT) (B : PolyExpr)
+    (hp : p = if π.verifierFirst then π.rounds.eval x.length / 2
+      else (π.rounds.eval x.length + 1) / 2)
+    (hlen : SQ.coinLen x.length = V.coinLen x.length + q * S.coinLen x.length)
+    (hsim : ∀ r : SQ.Coins x.length, SQ.simulate x z r =
+      View.encode ⟨x, z, (List.ofFn r).take (V.coinLen x.length),
+        phasePrefix S π.rounds B π.verifierFirst x z
+          ((List.ofFn r).take (V.coinLen x.length))
+          ((List.ofFn r).drop (V.coinLen x.length)) q⟩)
+    (ε : ℝ)
+    (hprefix : StatClose
+      (fun r : V.Coins x.length × (Fin q → π.P.Coins x.length) =>
+        (r.1, realPrefix π V x y z (List.ofFn r.1) p q r.2))
+      (fun r : V.Coins x.length × (Fin q → S.Coins x.length) =>
+        (r.1, simPrefix S x z (List.ofFn r.1) (π.rounds.eval x.length)
+          (B.eval x.length) p q r.2)) ε) :
+    StatClose (fun r => ((ρ.withV V).viewV x y z r).encode) (SQ.simulate x z) ε := by
+  let encodeState : V.Coins x.length × List (List Bool) → List Bool :=
+    fun state => View.encode ⟨x, z, List.ofFn state.1, state.2⟩
+  have hencoded : StatClose
+      (fun r : V.Coins x.length × (Fin q → π.P.Coins x.length) =>
+        View.encode ⟨x, z, List.ofFn r.1,
+          realPrefix π V x y z (List.ofFn r.1) p q r.2⟩)
+      (fun r : V.Coins x.length × (Fin q → S.Coins x.length) =>
+        View.encode ⟨x, z, List.ofFn r.1,
+          simPrefix S x z (List.ofFn r.1) (π.rounds.eval x.length)
+            (B.eval x.length) p q r.2⟩) ε :=
+    StatClose.map hprefix encodeState
+  apply statClose_reindex _ _ _ _ (h.realCoinsEquiv V)
+    (coinBlocksEquiv (V.coinLen x.length) q (S.coinLen x.length) hlen) ε hencoded
+  · exact fun r => h.viewV_eq_realPrefix V y z r
+  · intro r
+    simpa only [hp] using
+      simulate_eq_simPrefix S SQ π.rounds B π.verifierFirst x z q (V.coinLen x.length)
+        hlen hsim r
+
+end TCSlib.Cryptography.SequentialZK
diff --git a/TCSlib/Cryptography/Composability/SequentialZK/ErrSoundness.lean b/TCSlib/Cryptography/Composability/SequentialZK/ErrSoundness.lean
new file mode 100644
index 000000000..d6689bab9
--- /dev/null
+++ b/TCSlib/Cryptography/Composability/SequentialZK/ErrSoundness.lean
@@ -0,0 +1,87 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Composability.SequentialZK.Phases
+import TCSlib.Cryptography.ZeroKnowledge.InteractiveProofs
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Acceptance bounds from explicit soundness error
+
+## Main definitions
+
+This module introduces no definitions.
+
+## Main results
+
+* `InteractiveProofErr.uprob_accept_le`: acceptance on a no-instance has probability at
+  most the stated soundness error.
+* `InteractiveProofErr.sound_nonneg`: the stated error is nonnegative on a no-instance.
+* `Composability.prefixProver_accept_le`: a fixed earlier transcript and prover tape give
+  acceptance at most the stated error over a fresh original verifier tape alone.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §4.5 (interactive-proof soundness) and Theorem 175.1 (sequential repetition).
+-/
+
+namespace TCSlib.Cryptography
+
+/-- For `h : InteractiveProofErr π L s`, a no-instance `x ∉ L`, a prover `P'`, and verifier
+auxiliary input `z`, `Pr[π.outV P' x [] z = [true]] ≤ s |x|`.
+[PS10, §4.5, acceptance form of soundness]. -/
+theorem InteractiveProofErr.uprob_accept_le {π : Protocol} {L : Language Bool} {s : ℕ → ℝ}
+    (h : InteractiveProofErr π L s) (x : List Bool) (hx : x ∉ L)
+    (P' : Strategy) (z : List Bool) :
+    uprob (fun r : π.ExecCoins P' x => π.outV P' x [] z r = [true]) ≤ s x.length := by
+  have hle : uprob (fun r : π.ExecCoins P' x => π.outV P' x [] z r = [true]) ≤
+      uprob (fun r : π.ExecCoins P' x => ¬ π.outV P' x [] z r = [false]) :=
+    uprob_mono fun r hr => by rw [hr]; decide
+  rw [uprob_not] at hle
+  linarith [h.sound x hx P' z]
+
+/-- For `h : InteractiveProofErr π L s` and a no-instance `x ∉ L`, `0 ≤ s |x|`.
+[PS10, §4.5, a probability bound has nonnegative error]. -/
+theorem InteractiveProofErr.sound_nonneg {π : Protocol} {L : Language Bool} {s : ℕ → ℝ}
+    (h : InteractiveProofErr π L s) (x : List Bool) (hx : x ∉ L) : 0 ≤ s x.length :=
+  (sub_le_self_iff (1 : ℝ)).mp ((h.sound x hx π.P []).trans (uprob_le_one _))
+
+namespace Composability
+
+/-- For `h : InteractiveProofErr π L s`, a no-instance `x ∉ L`, a strategy `P`, its fixed
+auxiliary input `y`, tape `rP`, earlier received history `prior`, and verifier auxiliary
+input `z`, the probability over `rV : π.V.Coins |x|` that `π.V.next` accepts the execution
+of `prefixProver P y rP prior` on prover tape `[]` and verifier tape `List.ofFn rV` is at
+most `s |x|`. [PS10, Theorem 175.1, soundness with an earlier transcript fixed].
+`uprob (fun rV : π.V.Coins x.length => π.V.next x z (List.ofFn rV) (exec (prefixProver P y rP prior)
+π.V π.verifierFirst x [] z [] (List.ofFn rV) (π.rounds.eval x.length)).2 = [true]) ≤ s x.length`.
+
+**Proof sketch.** Apply the explicit-error acceptance bound to the prefix-hardwired prover.
+Its coin polynomial is zero, so every one of its coin strings is empty. Read the verifier
+output and transcript through their published equations and replace this prover coin
+string by `[]`. The acceptance event then depends only on the verifier's tape; the public
+uniform-product and constant-average laws remove the unused prover coins. -/
+theorem prefixProver_accept_le {π : Protocol} {L : Language Bool} {s : ℕ → ℝ}
+    (h : InteractiveProofErr π L s) (x : List Bool) (hx : x ∉ L)
+    (P : Strategy) (y rP : List Bool) (prior : List (List Bool)) (z : List Bool) :
+    uprob (fun rV : π.V.Coins x.length =>
+      π.V.next x z (List.ofFn rV)
+        (exec (prefixProver P y rP prior) π.V π.verifierFirst x [] z []
+          (List.ofFn rV) (π.rounds.eval x.length)).2 = [true]) ≤ s x.length := by
+  have hnil (r : (prefixProver P y rP prior).Coins x.length) : List.ofFn r = [] := by
+    apply List.eq_nil_of_length_eq_zero
+    rw [List.length_ofFn, Strategy.coinLen_eq, prefixProver_coins,
+      Complexity.PolyExpr.eval_const]
+  have hb := h.uprob_accept_le x hx (prefixProver P y rP prior) z
+  simp only [Protocol.outV_eq, Protocol.transcriptWith_eq, hnil] at hb
+  rw [uprob_prod] at hb
+  simpa only [HardcoreBit.uexp_const] using hb
+
+end Composability
+
+end TCSlib.Cryptography
diff --git a/TCSlib/Cryptography/Composability/SequentialZK/ExecutionBounds.lean b/TCSlib/Cryptography/Composability/SequentialZK/ExecutionBounds.lean
new file mode 100644
index 000000000..4729bcb36
--- /dev/null
+++ b/TCSlib/Cryptography/Composability/SequentialZK/ExecutionBounds.lean
@@ -0,0 +1,88 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Composability.SequentialZK.Normalization
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Bounded prover messages in executions
+
+The phase normalization for sequential composition [PS10, Theorem 175.1] fixes real phase
+views because every honest prover message satisfies the common bit bound. This file reads
+that fact from the public zero/successor execution equations, independently of the verifier's
+behavior or any property of its tape and auxiliary input.
+
+## Main definitions
+
+There are no new definitions.
+
+## Main results
+
+* `exec_snd_bounded`: a uniform bound on the prover's next message bounds every message the
+  verifier receives in any finite execution.
+* `exec_snd_slice_bounded`: the bound also holds after dropping and taking messages.
+* `length_encodeMsgs_exec_snd_le`: the public word-list bound applied to the execution.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §7.2.1, Theorem 175.1.
+-/
+
+namespace TCSlib.Cryptography.SequentialZK
+
+open Complexity
+
+/-- For `P,V,vFirst,x,y,z,rP,rV,B,g`, if every message `P.next x y rP hist` has length at most
+`B`, then every `m ∈ (exec P V vFirst x y z rP rV g).2` has length at most `B`.
+
+**Proof sketch.** Induct on the move count through the published execution equations. A
+verifier move leaves its received list unchanged. A prover move appends exactly one message,
+which satisfies the uniform next-message bound; all earlier messages satisfy the induction
+hypothesis. -/
+theorem exec_snd_bounded (P V : Strategy) (vFirst : Bool) (x y z rP rV : List Bool)
+    (B g : ℕ) (hP : ∀ hist, (P.next x y rP hist).length ≤ B) :
+    ∀ m ∈ (exec P V vFirst x y z rP rV g).2, m.length ≤ B := by
+  induction g with
+  | zero =>
+    intro m hm
+    rw [exec_zero] at hm
+    cases hm
+  | succ g ih =>
+    intro m hm
+    rw [exec_succ] at hm
+    by_cases hV : moverIsV vFirst g = true
+    · simp only [hV, if_true] at hm
+      exact ih m hm
+    · simp only [hV] at hm
+      rcases List.mem_append.mp hm with hm | hm
+      · exact ih m hm
+      · rw [List.mem_singleton.mp hm]
+        exact hP _
+
+/-- The same next-message bound controls a received-history slice: every
+`m ∈ ((exec P V vFirst x y z rP rV g).2.drop d).take t` has `m.length ≤ B` when
+`∀ hist, (P.next x y rP hist).length ≤ B`. -/
+theorem exec_snd_slice_bounded (P V : Strategy) (vFirst : Bool) (x y z rP rV : List Bool)
+    (B g d t : ℕ) (hP : ∀ hist, (P.next x y rP hist).length ≤ B) :
+    ∀ m ∈ ((exec P V vFirst x y z rP rV g).2.drop d).take t, m.length ≤ B := by
+  intro m hm
+  exact exec_snd_bounded P V vFirst x y z rP rV B g hP m
+    (List.mem_of_mem_drop (List.mem_of_mem_take hm))
+
+/-- If every prover message has at most `B` bits, its received-history encoding satisfies
+`(Strategy.encodeMsgs (exec P V vFirst x y z rP rV g).2).length ≤
+(exec P V vFirst x y z rP rV g).2.length * (2 * B + 2)`. -/
+theorem length_encodeMsgs_exec_snd_le (P V : Strategy) (vFirst : Bool)
+    (x y z rP rV : List Bool) (B g : ℕ)
+    (hP : ∀ hist, (P.next x y rP hist).length ≤ B) :
+    (Strategy.encodeMsgs (exec P V vFirst x y z rP rV g).2).length ≤
+      (exec P V vFirst x y z rP rV g).2.length * (2 * B + 2) := by
+  rw [encodeMsgs_eq_encWords]
+  exact BinArith.length_encWords_le _ B (exec_snd_bounded P V vFirst x y z rP rV B g hP)
+
+end TCSlib.Cryptography.SequentialZK
diff --git a/TCSlib/Cryptography/Composability/SequentialZK/HybridRecursion.lean b/TCSlib/Cryptography/Composability/SequentialZK/HybridRecursion.lean
new file mode 100644
index 000000000..4973f46d1
--- /dev/null
+++ b/TCSlib/Cryptography/Composability/SequentialZK/HybridRecursion.lean
@@ -0,0 +1,93 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Asymptotic.Sampling
+import Mathlib.Data.Fin.Tuple.Basic
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Hybrid bounds from conditional continuation gaps
+
+## Main definitions
+
+This module introduces no definitions.
+
+## Main results
+
+* `hybrid_recursion_gap_le` bounds the difference between the final real execution's
+  expected continuation potential and the initial potential by the number of phase updates
+  times their uniform conditional gap bound.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  Theorem 175.1 (sequential repetition of zero knowledge).
+-/
+
+namespace TCSlib.Cryptography.SequentialZK
+
+/-- Let `realFamily` start at `initial` and satisfy its displayed `Fin.snoc` equation for
+`realStep`. For a real-valued continuation potential `C`, suppose `0 ≤ ε` and each actual
+real prefix at `i<q` satisfies
+`|E_a[C (i+1) (realStep i (realFamily i r) a)] - C i (realFamily i r)| ≤ ε`.
+Then `|E_r[C q (realFamily q r)] - C 0 initial| ≤ q*ε`.
+The state type is arbitrary; no finite witness or state-space assumption is required.
+[PS10, Theorem 175.1, conditional hybrid argument].
+
+**Proof sketch.** For each phase count, average the continuation potential over the real
+prefix's independent coins. The snoc equivalence and uniform-product averaging identify
+the next average with the average of its conditional next-step expectations. Averaging
+the supplied local bounds therefore bounds each adjacent difference by `ε`. Apply the
+published telescoping hybrid inequality and bound its `q` summands by `ε`. -/
+theorem hybrid_recursion_gap_le {A State : Type*} [Fintype A] [Nonempty A]
+    (realFamily : (i : ℕ) → (Fin i → A) → State) (initial : State)
+    (realStep : ℕ → State → A → State)
+    (real_zero : ∀ r, realFamily 0 r = initial)
+    (real_snoc : ∀ i r a, realFamily (i + 1) (Fin.snoc r a) =
+      realStep i (realFamily i r) a)
+    (C : ℕ → State → ℝ) (q : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
+    (hlocal : ∀ i < q, ∀ r : Fin i → A,
+      |uexp (fun a => C (i + 1) (realStep i (realFamily i r) a)) -
+        C i (realFamily i r)| ≤ ε) :
+    |uexp (fun r : Fin q → A => C q (realFamily q r)) - C 0 initial| ≤
+      (q : ℝ) * ε := by
+  -- Average the continuation potential over each real prefix coin table.
+  let P : ℕ → ℝ := fun i => uexp (fun r : Fin i → A => C i (realFamily i r))
+  have hzero : P 0 = C 0 initial := by
+    simp only [P, real_zero, HardcoreBit.uexp_const]
+  -- Reindex the next table as a prefix and fresh coin, then average the local gap.
+  have hgap (i : ℕ) (hi : i < q) : |P i - P (i + 1)| ≤ ε := by
+    let e : (Fin (i + 1) → A) ≃ (Fin i → A) × A :=
+      (Fin.snocEquiv (fun _ : Fin (i + 1) => A)).symm.trans
+        (Equiv.prodComm A (Fin i → A))
+    have hfamily (r : Fin (i + 1) → A) :
+        realFamily (i + 1) r = realStep i (realFamily i (e r).1) (e r).2 := by
+      change realFamily (i + 1) r =
+        realStep i (realFamily i (Fin.init r)) (r (Fin.last i))
+      simpa only [Fin.snoc_init_self] using real_snoc i (Fin.init r) (r (Fin.last i))
+    have hnext : P (i + 1) = uexp (fun r : Fin i → A =>
+        uexp (fun a => C (i + 1) (realStep i (realFamily i r) a))) := by
+      have hpoint : (fun r : Fin (i + 1) → A => C (i + 1) (realFamily (i + 1) r)) =
+          (fun r => C (i + 1) (realStep i (realFamily i (e r).1) (e r).2)) :=
+        funext fun r => congrArg (C (i + 1)) (hfamily r)
+      change uexp (fun r : Fin (i + 1) → A => C (i + 1) (realFamily (i + 1) r)) = _
+      rw [hpoint, HardcoreBit.uexp_comp_equiv e
+        (fun z : (Fin i → A) × A => C (i + 1) (realStep i (realFamily i z.1) z.2)),
+        HardcoreBit.uexp_prod]
+    rw [hnext, abs_sub_comm]
+    exact abs_uexp_sub_le hε (fun r => hlocal i hi r)
+  -- Apply the published telescope and bound each adjacent gap by the same error.
+  have hsum : ∑ i ∈ Finset.range q, |P i - P (i + 1)| ≤ (q : ℝ) * ε := by
+    calc
+      _ ≤ ∑ _i ∈ Finset.range q, ε :=
+        Finset.sum_le_sum fun i hi => hgap i (Finset.mem_range.mp hi)
+      _ = (q : ℝ) * ε := by simp
+  have hbound := (abs_sub_le_sum_hybrids P q).trans hsum
+  rw [hzero, abs_sub_comm] at hbound
+  exact hbound
+
+end TCSlib.Cryptography.SequentialZK
diff --git a/TCSlib/Cryptography/Composability/SequentialZK/Normalization.lean b/TCSlib/Cryptography/Composability/SequentialZK/Normalization.lean
new file mode 100644
index 000000000..75e352170
--- /dev/null
+++ b/TCSlib/Cryptography/Composability/SequentialZK/Normalization.lean
@@ -0,0 +1,100 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.ZeroKnowledge.Interaction
+import TCSlib.Complexity.ClassP.BinaryArith.Words
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Bounded message slots for sequential zero-knowledge simulation
+
+A phase simulator can output an arbitrary word. The message-slot normalization reads that word
+as an encoded list, retains exactly the requested number of slots, truncates every message to
+the requested bit bound, and supplies empty messages for missing entries. This is the bounded
+message-list part of the normalization in [PS10, Theorem 175.1]. Validation of view metadata
+and the choice of a fallback view are separate operations.
+
+## Main definitions
+
+* `normalizeMsgs p B raw`: exactly `p` decoded message slots, each truncated to `B` bits.
+
+## Main results
+
+* `encodeMsgs_eq_encWords`: the interaction and generic word-list encodings agree.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §7.2.1, Theorem 175.1.
+-/
+
+namespace TCSlib.Cryptography.SequentialZK
+
+open Complexity Turing
+
+/-- The two message-list encodings agree: `Strategy.encodeMsgs h = BinArith.encWords h`. -/
+theorem encodeMsgs_eq_encWords (h : List (List Bool)) :
+    Strategy.encodeMsgs h = BinArith.encWords h := by
+  induction h with
+  | nil => rw [Strategy.encodeMsgs_nil, BinArith.encWords_nil]
+  | cons m h ih => rw [Strategy.encodeMsgs_cons, BinArith.encWords_cons, ih]
+
+/-- Bounded message slots: `normalizeMsgs p B raw` is the list of the first `p` words decoded
+from `raw`, with missing words replaced by `[]` and every word truncated to `B` bits.
+[PS10, Theorem 175.1, bounded phase-shape normalization].
+`normalizeMsgs p B raw = (List.range p).map (fun i => ((BinArith.decWords raw).getD i []).take
+B)`. -/
+def normalizeMsgs (p B : ℕ) (raw : List Bool) : List (List Bool) :=
+  (List.range p).map fun i => ((BinArith.decWords raw).getD i []).take B
+
+/-- The slot formula is
+`normalizeMsgs p B raw = (List.range p).map (fun i => ((decWords raw).getD i []).take B)`. -/
+theorem normalizeMsgs_eq (p B : ℕ) (raw : List Bool) :
+    normalizeMsgs p B raw =
+      (List.range p).map (fun i => ((BinArith.decWords raw).getD i []).take B) := rfl
+
+/-- Normalization always supplies exactly the requested number of slots:
+`(normalizeMsgs p B raw).length = p`. -/
+theorem length_normalizeMsgs (p B : ℕ) (raw : List Bool) :
+    (normalizeMsgs p B raw).length = p := by
+  rw [normalizeMsgs_eq, List.length_map, List.length_range]
+
+/-- Every normalized slot has at most `B` bits:
+`m ∈ normalizeMsgs p B raw → m.length ≤ B`. -/
+theorem length_le_of_mem_normalizeMsgs (p B : ℕ) (raw : List Bool) {m : List Bool}
+    (hm : m ∈ normalizeMsgs p B raw) : m.length ≤ B := by
+  rw [normalizeMsgs_eq] at hm
+  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hm
+  rw [List.length_take]
+  exact Nat.min_le_left _ _
+
+/-- Normalization fixes an encoded list with `p` slots and messages of at most `B` bits:
+`normalizeMsgs p B (Strategy.encodeMsgs h) = h` if `h.length = p` and
+`∀ m ∈ h, m.length ≤ B`. -/
+theorem normalizeMsgs_encodeMsgs (p B : ℕ) (h : List (List Bool))
+    (hp : h.length = p) (hB : ∀ m ∈ h, m.length ≤ B) :
+    normalizeMsgs p B (Strategy.encodeMsgs h) = h := by
+  rw [normalizeMsgs_eq, encodeMsgs_eq_encWords, BinArith.decWords_encWords]
+  apply List.ext_getElem
+  · rw [List.length_map, List.length_range, hp]
+  · intro i hi hi'
+    rw [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD,
+      List.getElem?_eq_getElem hi', Option.getD_some]
+    exact List.take_of_length_le (hB _ (List.getElem_mem hi'))
+
+/-- The encoding of the normalized slots has the bound
+`(Strategy.encodeMsgs (normalizeMsgs p B raw)).length ≤ p * (2 * B + 2)`. -/
+theorem length_encodeMsgs_normalizeMsgs_le (p B : ℕ) (raw : List Bool) :
+    (Strategy.encodeMsgs (normalizeMsgs p B raw)).length ≤ p * (2 * B + 2) := by
+  rw [encodeMsgs_eq_encWords]
+  calc
+    (BinArith.encWords (normalizeMsgs p B raw)).length ≤
+        (normalizeMsgs p B raw).length * (2 * B + 2) :=
+      BinArith.length_encWords_le _ B fun m hm => length_le_of_mem_normalizeMsgs p B raw hm
+    _ = p * (2 * B + 2) := by rw [length_normalizeMsgs]
+
+end TCSlib.Cryptography.SequentialZK
diff --git a/TCSlib/Cryptography/Composability/SequentialZK/NormalizationMachine.lean b/TCSlib/Cryptography/Composability/SequentialZK/NormalizationMachine.lean
new file mode 100644
index 000000000..e6e72ba6e
--- /dev/null
+++ b/TCSlib/Cryptography/Composability/SequentialZK/NormalizationMachine.lean
@@ -0,0 +1,100 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Composability.SequentialZK.Normalization
+import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Machines
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Polynomial-time bounded message-slot normalization
+
+The message-slot normalization of [PS10, Theorem 175.1] is computed through the public generic
+word-list map and lookup hosts, truncation, and the published counted emitter. No simulator
+output-shape premise is used: malformed words are read by the total word-list decoder.
+
+## Main definitions
+
+There are no new definitions. The input count and bit bound are arbitrary unary computable
+functions; the source word is an arbitrary polynomial-time function of the machine input.
+
+## Main results
+
+* `polyTimeComputable_encWords_decWords`: canonical reencoding is polynomial-time.
+* `polyTimeComputable_decWords_getD`: total decoded-word lookup is polynomial-time.
+* `polyTimeComputable_encode_normalizeMsgs`: bounded-slot normalization is polynomial-time.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §7.2.1, Theorem 175.1.
+-/
+
+namespace TCSlib.Cryptography.SequentialZK
+
+open Complexity Turing
+
+/-- Canonical reencoding is polynomial-time: if `raw` is polynomial-time, so is
+`w ↦ BinArith.encWords (BinArith.decWords (raw w))`.
+`PolyTimeComputable fun w => BinArith.encWords (BinArith.decWords (raw w))`. -/
+theorem polyTimeComputable_encWords_decWords {raw : List Bool → List Bool}
+    (hraw : PolyTimeComputable raw) :
+    PolyTimeComputable fun w => BinArith.encWords (BinArith.decWords (raw w)) := by
+  have hpre : PolyTimeComputable fun w => pairEncode [] (raw w) :=
+    (polyTimeComputable_const []).pairEncode hraw
+  refine ((BinArith.polyTimeComputable_mapW polyTimeComputable_pairSndD).comp hpre).congr ?_
+  intro w
+  simp only [Function.comp_apply, BinArith.mapW_pairEncode, pairSndD_pairEncode, List.map_id']
+
+/-- Total decoded-word lookup is polynomial-time: if `raw` and the unary index `i` are
+polynomial-time, so is `w ↦ (BinArith.decWords (raw w)).getD (i w) []`.
+`PolyTimeComputable fun w => (BinArith.decWords (raw w)).getD (i w) []`. -/
+theorem polyTimeComputable_decWords_getD {raw : List Bool → List Bool}
+    (hraw : PolyTimeComputable raw) {i : List Bool → ℕ}
+    (hi : PolyTimeComputable fun w => List.replicate (i w) true) :
+    PolyTimeComputable fun w => (BinArith.decWords (raw w)).getD (i w) [] := by
+  have hcanon := polyTimeComputable_encWords_decWords hraw
+  refine (BinArith.polyTimeComputable_getW.comp (hi.pairEncode hcanon)).congr ?_
+  intro w
+  simp only [Function.comp_apply, BinArith.getW_pairEncode, List.length_replicate]
+
+/-- Bounded-slot normalization is polynomial-time: if `p` and `B` are computable in unary
+and `raw` is polynomial-time, then so is
+`w ↦ Strategy.encodeMsgs (normalizeMsgs (p w) (B w) (raw w))`.
+[PS10, Theorem 175.1, bounded phase-shape normalization].
+`PolyTimeComputable fun w => Strategy.encodeMsgs (normalizeMsgs (p w) (B w) (raw w))`.
+
+**Proof sketch.** Canonically reencode the total decoder's result through the generic word
+map. The generic lookup host reads each requested slot, including empty defaults beyond the
+end. Truncate that slot to the unary bit bound and emit its self-delimiting pair. The published
+counted-emission host concatenates these chunks over the unary number of requested slots;
+the resulting word is precisely the normalized list's encoding. -/
+theorem polyTimeComputable_encode_normalizeMsgs {p B : List Bool → ℕ}
+    {raw : List Bool → List Bool}
+    (hp : PolyTimeComputable fun w => List.replicate (p w) true)
+    (hB : PolyTimeComputable fun w => List.replicate (B w) true)
+    (hraw : PolyTimeComputable raw) :
+    PolyTimeComputable fun w => Strategy.encodeMsgs (normalizeMsgs (p w) (B w) (raw w)) := by
+  -- Look up a total decoded slot at the emitter's unary counter.
+  have hidx : PolyTimeComputable fun w => List.replicate (pairFstD w).length true :=
+    EncodingMachines.unaryLength_poly polyTimeComputable_pairFstD
+  have hlookup := polyTimeComputable_decWords_getD
+    (hraw.comp polyTimeComputable_pairSndD) hidx
+  -- Cap the payload and emit its self-delimiting message encoding.
+  have hcap := EncodingMachines.truncate_poly hlookup (hB.comp polyTimeComputable_pairSndD)
+  have hchunk : PolyTimeComputable fun w => pairEncode
+      (((BinArith.decWords (raw (pairSndD w))).getD (pairFstD w).length []).take
+        (B (pairSndD w))) [] :=
+    hcap.pairEncode (polyTimeComputable_const [])
+  -- The published counted emitter supplies exactly p slots.
+  refine (ColMachines.polyTimeComputable_flatMap_range
+    (E := fun w i => pairEncode (((BinArith.decWords (raw w)).getD i []).take (B w)) [])
+    hchunk hp).congr ?_
+  intro w
+  simp only [normalizeMsgs_eq, encodeMsgs_eq_encWords, BinArith.encWords_def,
+    List.flatMap_map]
+
+end TCSlib.Cryptography.SequentialZK
diff --git a/TCSlib/Cryptography/Composability/SequentialZK/NormalizedStep.lean b/TCSlib/Cryptography/Composability/SequentialZK/NormalizedStep.lean
new file mode 100644
index 000000000..17c687308
--- /dev/null
+++ b/TCSlib/Cryptography/Composability/SequentialZK/NormalizedStep.lean
@@ -0,0 +1,126 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.ZeroKnowledge.Defs
+import TCSlib.Cryptography.Composability.SequentialZK.ExecutionBounds
+import TCSlib.Cryptography.Composability.SequentialZK.PhaseView
+import TCSlib.Cryptography.Composability.SequentialZK.StatisticalPostprocess
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Statistical comparison of a normalized phase update
+
+The fixed-tape verifier used in sequential zero-knowledge composition [PS10, Theorem 175.1]
+has no random bits of its own. Its real view has known metadata and bounded prover messages,
+so canonical normalization fixes the real phase exactly. Mapping a raw statistical comparison
+through the padded-prefix update therefore costs no additional error.
+
+## Main definitions
+
+There are no new definitions.
+
+## Main results
+
+* `normalizePhaseMsgs_viewV`: normalization fixes each bounded real zero-verifier view.
+* `statClose_normalized_step`: a raw one-phase comparison for a verifier with zero coins
+  remains valid after prefix extension, canonical bounded normalization, and empty padding.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §7.2.1, Theorem 175.1.
+-/
+
+namespace TCSlib.Cryptography.SequentialZK
+
+open Complexity
+
+/-- For protocol `ρ`, inputs `x,y,aux`, count `p`, cap `B`, zero verifier coin length,
+a uniform `B` bound on prover messages, real received count `p`, and seed `r`, normalization
+fixes the real received history:
+`normalizePhaseMsgs x aux p B (ρ.viewV x y aux r).encode =
+  (exec ρ.P ρ.V ρ.verifierFirst x y aux (List.ofFn r.1) [] (ρ.rounds.eval |x|)).2`.
+[PS10, Theorem 175.1, normalization of a real wrapped phase].
+
+**Proof sketch.** The verifier seed encodes an empty tape because its coin length is zero.
+Read the real view and transcript through their published equations. The supplied count
+and the public execution-message bound make this canonical real view a fixed point of the
+bounded-slot normalizer. No simulator or statistical comparison is needed. -/
+theorem normalizePhaseMsgs_viewV (ρ : Protocol) (x y aux : List Bool) (p B : ℕ)
+    (hcoins : ρ.V.coinLen x.length = 0)
+    (hP : ∀ r hist, (ρ.P.next x y r hist).length ≤ B)
+    (hcount : ∀ rP : List Bool,
+      (exec ρ.P ρ.V ρ.verifierFirst x y aux rP [] (ρ.rounds.eval x.length)).2.length = p)
+    (r : ρ.ExecCoins ρ.P x) :
+    normalizePhaseMsgs x aux p B (ρ.viewV x y aux r).encode =
+      (exec ρ.P ρ.V ρ.verifierFirst x y aux (List.ofFn r.1) []
+        (ρ.rounds.eval x.length)).2 := by
+  -- The wrapper's verifier tape has no bits.
+  have hrV : List.ofFn r.2 = [] :=
+    List.eq_nil_of_length_eq_zero (by rw [List.length_ofFn, hcoins])
+  rw [Protocol.viewV_eq, Protocol.transcriptWith_eq, hrV]
+  -- The real count and message cap give the canonical normalization fixed point.
+  exact normalizePhaseMsgs_of_encode x aux p B
+    (exec ρ.P ρ.V ρ.verifierFirst x y aux (List.ofFn r.1) [] (ρ.rounds.eval x.length)).2
+    (hcount (List.ofFn r.1))
+    (exec_snd_bounded ρ.P ρ.V ρ.verifierFirst x y aux (List.ofFn r.1) [] B
+      (ρ.rounds.eval x.length) (fun hist => hP (List.ofFn r.1) hist))
+
+/-- For protocol `ρ`, simulator `S`, inputs `x,y,aux`, prefix `pre`, count `p`, bit cap `B`, and
+error `δ`, suppose the verifier has zero coins, every prover message has at most `B` bits,
+and every real received history has length `p`. A raw `δ`-close real-view/simulator pair then
+gives `δ`-close prefix updates: the real update appends its received history and `k-p` empty
+messages, while the simulated update appends `normalizePhaseMsgs x aux p B` of the output and
+the same empty messages, where `k = ρ.rounds.eval |x|`. [PS10, Theorem 175.1].
+
+**Proof sketch.** The zero-coin verifier tape is empty on every real seed. The execution bound
+and supplied message count make each real view a fixed point of canonical normalization.
+Apply the generic published postprocessing law with the normalized padded-prefix update
+and this real fixed point. Its uniform first-projection reader removes the unused verifier
+coin factor without changing the statistical bound. No simulator efficiency or output-shape
+assumption is used. -/
+theorem statClose_normalized_step (ρ : Protocol) (S : NUPPT) (x y aux : List Bool)
+    (pre : List (List Bool)) (p B : ℕ) (δ : ℝ) (hcoins : ρ.V.coinLen x.length = 0)
+    (hP : ∀ r hist, (ρ.P.next x y r hist).length ≤ B)
+    (hcount : ∀ rP : List Bool,
+      (exec ρ.P ρ.V ρ.verifierFirst x y aux rP [] (ρ.rounds.eval x.length)).2.length = p)
+    (hclose : StatClose (fun r : ρ.ExecCoins ρ.P x => (ρ.viewV x y aux r).encode)
+      (S.simulate x aux) δ) :
+    StatClose
+      (fun rP : ρ.P.Coins x.length => pre ++
+        ((exec ρ.P ρ.V ρ.verifierFirst x y aux (List.ofFn rP) []
+          (ρ.rounds.eval x.length)).2 ++ List.replicate (ρ.rounds.eval x.length - p) []))
+      (fun rS : S.Coins x.length => pre ++
+        (normalizePhaseMsgs x aux p B (S.simulate x aux rS) ++
+          List.replicate (ρ.rounds.eval x.length - p) [])) δ := by
+  -- Each real view has the known metadata, empty tape, count and message-length bound.
+  have hfixed (r : ρ.ExecCoins ρ.P x) :
+      normalizePhaseMsgs x aux p B (ρ.viewV x y aux r).encode =
+        (exec ρ.P ρ.V ρ.verifierFirst x y aux (List.ofFn r.1) []
+          (ρ.rounds.eval x.length)).2 :=
+    normalizePhaseMsgs_viewV ρ x y aux p B hcoins hP hcount r
+  have hpoint (r : ρ.P.Coins x.length × ρ.V.Coins x.length) :
+      pre ++ (normalizePhaseMsgs x aux p B (ρ.viewV x y aux r).encode ++
+          List.replicate (ρ.rounds.eval x.length - p) []) =
+        pre ++ ((exec ρ.P ρ.V ρ.verifierFirst x y aux (List.ofFn r.1) []
+          (ρ.rounds.eval x.length)).2 ++ List.replicate (ρ.rounds.eval x.length - p) []) :=
+    congrArg (fun msgs : List (List Bool) =>
+      pre ++ (msgs ++ List.replicate (ρ.rounds.eval x.length - p) [])) (hfixed r)
+  -- Instantiate the opaque generic law with every seed type and function explicit.
+  with_reducible exact (TCSlib.Cryptography.Composability.statClose_map_fst
+    (α := ρ.P.Coins x.length) (β := ρ.V.Coins x.length) (τ := S.Coins x.length)
+    (γ := List Bool) (δ := List (List Bool))
+    (fun r : ρ.P.Coins x.length × ρ.V.Coins x.length => (ρ.viewV x y aux r).encode)
+    (S.simulate x aux : S.Coins x.length → List Bool)
+    (fun raw : List Bool => pre ++ (normalizePhaseMsgs x aux p B raw ++
+      List.replicate (ρ.rounds.eval x.length - p) []))
+    (fun rP : ρ.P.Coins x.length => pre ++
+      ((exec ρ.P ρ.V ρ.verifierFirst x y aux (List.ofFn rP) []
+        (ρ.rounds.eval x.length)).2 ++ List.replicate (ρ.rounds.eval x.length - p) []))
+    δ hclose hpoint)
+
+end TCSlib.Cryptography.SequentialZK
diff --git a/TCSlib/Cryptography/Composability/SequentialZK/PaddedProverSpec.lean b/TCSlib/Cryptography/Composability/SequentialZK/PaddedProverSpec.lean
new file mode 100644
index 000000000..2298c520b
--- /dev/null
+++ b/TCSlib/Cryptography/Composability/SequentialZK/PaddedProverSpec.lean
@@ -0,0 +1,142 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Composability.SequentialZK.RealPhases
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# The padded repeated-prover construction contract
+
+The construction contract packages only direct equations and move-count readers for an
+original protocol and an abstract padded repetition. Zero-knowledge proofs supply their
+relation and message bound separately. This keeps both statistical and computational
+composition proofs independent of the owned construction definitions.
+
+## Main definitions
+
+* `PaddedProverSpec π ρ x q p`: the repeated prover's equations and position readers at `x`.
+
+## Main results
+
+* `PaddedProverSpec.real_phase`: the real portion is an original wrapped-verifier execution.
+* `PaddedProverSpec.padded_phase`: the complete phase appends the real messages and fillers.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §7.2.1, Theorem 175.1.
+* [Gol01] O. Goldreich, *Foundations of Cryptography, Volume I: Basic Tools*, Cambridge
+  University Press, 2001, §4.3.4.
+-/
+
+namespace TCSlib.Cryptography.SequentialZK
+
+open Complexity Turing
+
+/-- For original protocol `π`, repeated protocol `ρ`, common input `x`, phase count `q` and
+real prover-message count `p`, `PaddedProverSpec π ρ x q p` asserts the displayed prover coin,
+round, mover, reply, index and history-count equations, with `k = π.rounds.eval |x|`.
+The contract is independent of any witness relation or message bound.
+[PS10, Theorem 175.1, the padded repeated-prover construction]. -/
+structure PaddedProverSpec (π ρ : Protocol) (x : List Bool) (q p : ℕ) : Prop where
+  /-- The prover coin length is `ρ.P.coinLen |x| = q * π.P.coinLen |x|`. -/
+  prover_coinLen : ρ.P.coinLen x.length = q * π.P.coinLen x.length
+  /-- The total move count is `ρ.rounds.eval |x| = 2 * π.rounds.eval |x| * q`. -/
+  rounds_eval : ρ.rounds.eval x.length = 2 * π.rounds.eval x.length * q
+  /-- The first-mover flag is `ρ.verifierFirst = π.verifierFirst`. -/
+  first : ρ.verifierFirst = π.verifierFirst
+  /-- For `y,r,hist`, `ρ.P.next x y r hist` uses index
+  `idx = if π.verifierFirst then 2|hist|-1 else 2|hist|`; it runs `π.P.next` on coin block
+  `idx/(2k)` and the history after `(idx/(2k))*k` slots when `idx%(2k)<k`, and returns `[]`
+  otherwise, where `k = π.rounds.eval |x|`. -/
+  next (y r : List Bool) (hist : List (List Bool)) :
+    ρ.P.next x y r hist =
+      let idx := if π.verifierFirst then 2 * hist.length - 1 else 2 * hist.length
+      if idx % (2 * π.rounds.eval x.length) < π.rounds.eval x.length then
+        π.P.next x y (coinBlock (π.P.coinLen x.length)
+          (idx / (2 * π.rounds.eval x.length)) r)
+          (hist.drop (idx / (2 * π.rounds.eval x.length) * π.rounds.eval x.length))
+      else []
+  /-- For `V,y,z,rP,rV,n`, at an active prover move, the index recovered from the source
+  prover's received-history length is `n`, for every natural move index. -/
+  prover_index (V : Strategy) (y z rP rV : List Bool) (n : ℕ)
+      (hm : moverIsV π.verifierFirst n = false) :
+    (if π.verifierFirst then
+      2 * (exec ρ.P V π.verifierFirst x y z rP rV n).1.length - 1
+    else 2 * (exec ρ.P V π.verifierFirst x y z rP rV n).1.length) = n
+  /-- For `V,y,z,rP,rV,j`, both received histories after `2*k*j` moves have length `j*k`,
+  for every natural `j`, with `k = π.rounds.eval |x|`. -/
+  boundary (V : Strategy) (y z rP rV : List Bool) (j : ℕ) :
+    (exec ρ.P V π.verifierFirst x y z rP rV (2 * π.rounds.eval x.length * j)).1.length =
+        j * π.rounds.eval x.length ∧
+    (exec ρ.P V π.verifierFirst x y z rP rV (2 * π.rounds.eval x.length * j)).2.length =
+        j * π.rounds.eval x.length
+  /-- For `V,y,z,rP,rV`, the original verifier receives exactly `p` messages in `k` moves:
+  `(exec π.P V π.verifierFirst x y z rP rV k).2.length = p`. -/
+  original_count (V : Strategy) (y z rP rV : List Bool) :
+    (exec π.P V π.verifierFirst x y z rP rV (π.rounds.eval x.length)).2.length = p
+  /-- The number of real prover messages satisfies `p ≤ π.rounds.eval |x|`. -/
+  real_le : p ≤ π.rounds.eval x.length
+  /-- For `j,t`, the mover pattern satisfies `moverIsV π.verifierFirst (2*k*j+t) =
+  moverIsV π.verifierFirst t`, with `k = π.rounds.eval |x|`. -/
+  period (j t : ℕ) :
+    moverIsV π.verifierFirst (2 * π.rounds.eval x.length * j + t) =
+      moverIsV π.verifierFirst t
+
+namespace PaddedProverSpec
+
+/-- For a construction specification `h`, verifier `V`, inputs `y,z`, tapes `rP,rV`, phase
+`j<q` and `t≤k`, the two source histories after `2*k*j+t` equal their phase-start histories
+followed by the original `π.P` execution on coin block `j` against `phaseVerifier V`.
+The wrapped auxiliary word is `phaseAux z rV j` of the earlier verifier history.
+[PS10, Theorem 175.1; Gol01, §4.3.4, real-phase endpoint]. -/
+theorem real_phase {π ρ : Protocol} {x : List Bool} {q p : ℕ}
+    (h : PaddedProverSpec π ρ x q p) (V : Strategy) (y z rP rV : List Bool)
+    (j : ℕ) (hj : j < q) {t : ℕ} (ht : t ≤ π.rounds.eval x.length) :
+    (exec ρ.P V π.verifierFirst x y z rP rV (2 * π.rounds.eval x.length * j + t)).1 =
+      (exec ρ.P V π.verifierFirst x y z rP rV (2 * π.rounds.eval x.length * j)).1 ++
+        (exec π.P (phaseVerifier V) π.verifierFirst x y
+          (phaseAux z rV j
+            (exec ρ.P V π.verifierFirst x y z rP rV (2 * π.rounds.eval x.length * j)).2)
+          (coinBlock (π.P.coinLen x.length) j rP) [] t).1 ∧
+    (exec ρ.P V π.verifierFirst x y z rP rV (2 * π.rounds.eval x.length * j + t)).2 =
+      (exec ρ.P V π.verifierFirst x y z rP rV (2 * π.rounds.eval x.length * j)).2 ++
+        (exec π.P (phaseVerifier V) π.verifierFirst x y
+          (phaseAux z rV j
+            (exec ρ.P V π.verifierFirst x y z rP rV (2 * π.rounds.eval x.length * j)).2)
+          (coinBlock (π.P.coinLen x.length) j rP) [] t).2 :=
+  exec_real_phase ρ.P π.P V π.verifierFirst x y z rP rV (π.rounds.eval x.length) q j hj
+    (h.next y rP) (fun n _ hm => h.prover_index V y z rP rV n hm)
+    (h.boundary V y z rP rV j).1 (fun u _ => h.period j u) ht
+
+/-- For a construction specification `h`, verifier `V`, inputs `y,z`, tapes `rP,rV` and
+phase `j<q`, the source verifier history after the complete padded phase is its earlier
+history followed by the wrapped original real-phase messages and `k-p` empty fillers.
+The verifier's filler replies are unrestricted. [PS10, Theorem 175.1; Gol01, §4.3.4]. -/
+theorem padded_phase {π ρ : Protocol} {x : List Bool} {q p : ℕ}
+    (h : PaddedProverSpec π ρ x q p) (V : Strategy) (y z rP rV : List Bool)
+    (j : ℕ) (hj : j < q) :
+    (exec ρ.P V π.verifierFirst x y z rP rV (2 * π.rounds.eval x.length * (j + 1))).2 =
+      (exec ρ.P V π.verifierFirst x y z rP rV (2 * π.rounds.eval x.length * j)).2 ++
+        ((exec π.P (phaseVerifier V) π.verifierFirst x y
+          (phaseAux z rV j
+            (exec ρ.P V π.verifierFirst x y z rP rV (2 * π.rounds.eval x.length * j)).2)
+          (coinBlock (π.P.coinLen x.length) j rP) [] (π.rounds.eval x.length)).2 ++
+            List.replicate (π.rounds.eval x.length - p) []) :=
+  exec_padded_real_phase ρ.P π.P V π.verifierFirst x y z rP rV (π.rounds.eval x.length)
+    q j p hj (h.next y rP) (fun n _ hm => h.prover_index V y z rP rV n hm)
+    (h.boundary V y z rP rV j).1 (h.boundary V y z rP rV j).2
+    (h.boundary V y z rP rV (j + 1)).2
+    (h.original_count (phaseVerifier V) y
+      (phaseAux z rV j
+        (exec ρ.P V π.verifierFirst x y z rP rV (2 * π.rounds.eval x.length * j)).2)
+      (coinBlock (π.P.coinLen x.length) j rP) [])
+    (fun u _ => h.period j u)
+
+end PaddedProverSpec
+
+end TCSlib.Cryptography.SequentialZK
diff --git a/TCSlib/Cryptography/Composability/SequentialZK/PhaseView.lean b/TCSlib/Cryptography/Composability/SequentialZK/PhaseView.lean
new file mode 100644
index 000000000..66e59d809
--- /dev/null
+++ b/TCSlib/Cryptography/Composability/SequentialZK/PhaseView.lean
@@ -0,0 +1,174 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Composability.SequentialZK.NormalizationMachine
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Canonical phase-view normalization
+
+A one-phase simulator outputs an arbitrary word. For sequential composition, validate its
+metadata, empty wrapper tape, and canonical message-list encoding before extracting its
+messages. A malformed view contributes empty slots. The bounded-slot normalization then
+supplies exactly the prescribed number of messages, each of bounded length, without any
+assumption on the simulator's output shape. [PS10, Theorem 175.1].
+
+## Main definitions
+
+* `phaseViewPayload x z raw`: the message encoding of a canonical view with fields `x,z,[]`,
+  or `[]` when `raw` fails validation.
+* `normalizePhaseMsgs x z p B raw`: the validated payload normalized to `p` slots of `B` bits.
+
+## Main results
+
+* `phaseViewPayload_of_encode`: validation fixes every canonical view with the known fields.
+* `normalizePhaseMsgs_of_encode`: normalization fixes canonical bounded real views.
+* `normalizePhaseMsgs_of_ne`: malformed phase views yield exactly the requested empty slots.
+* `length_normalizePhaseMsgs`, `length_le_of_mem_normalizePhaseMsgs`,
+  `length_encodeMsgs_normalizePhaseMsgs_le`: count, message-length and encoded-size bounds.
+* `polyTimeComputable_phaseViewPayload`, `polyTimeComputable_encode_normalizePhaseMsgs`:
+  canonical validation and encoded bounded normalization are polynomial-time.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §7.2.1, Theorem 175.1.
+-/
+
+namespace TCSlib.Cryptography.SequentialZK
+
+open Complexity Turing
+
+/-- The validated message payload is `pairSndD (pairSndD raw)` when `raw` is exactly the
+encoding of `⟨x,z,[],decWords (pairSndD (pairSndD raw))⟩`, and is `[]` otherwise. This checks
+the known common input, auxiliary input, empty wrapper tape, and canonical message encoding.
+[PS10, Theorem 175.1, canonical phase-view fallback].
+`phaseViewPayload x z raw = if raw = View.encode ⟨x, z, [], BinArith.decWords (pairSndD (pairSndD
+raw))⟩ then pairSndD (pairSndD raw) else []`. -/
+def phaseViewPayload (x z raw : List Bool) : List Bool :=
+  if raw = View.encode ⟨x, z, [], BinArith.decWords (pairSndD (pairSndD raw))⟩ then
+    pairSndD (pairSndD raw)
+  else []
+
+/-- The payload formula is `phaseViewPayload x z raw = if raw = View.encode
+⟨x,z,[],decWords (pairSndD (pairSndD raw))⟩ then pairSndD (pairSndD raw) else []`. -/
+theorem phaseViewPayload_eq (x z raw : List Bool) :
+    phaseViewPayload x z raw =
+      if raw = View.encode ⟨x, z, [], BinArith.decWords (pairSndD (pairSndD raw))⟩ then
+        pairSndD (pairSndD raw)
+      else [] := rfl
+
+/-- Canonical phase-view normalization validates `raw` for the known fields `x,z,[]`, then
+supplies exactly `p` slots, each truncated to `B` bits, with empty defaults. A malformed view
+therefore supplies `p` empty messages. [PS10, Theorem 175.1, phase-shape normalization].
+`normalizePhaseMsgs x z p B raw = normalizeMsgs p B (phaseViewPayload x z raw)`. -/
+def normalizePhaseMsgs (x z : List Bool) (p B : ℕ) (raw : List Bool) : List (List Bool) :=
+  normalizeMsgs p B (phaseViewPayload x z raw)
+
+/-- `normalizePhaseMsgs x z p B raw = normalizeMsgs p B (phaseViewPayload x z raw)`. -/
+theorem normalizePhaseMsgs_eq (x z : List Bool) (p B : ℕ) (raw : List Bool) :
+    normalizePhaseMsgs x z p B raw = normalizeMsgs p B (phaseViewPayload x z raw) := rfl
+
+/-- Validation fixes every canonical view with the prescribed fields:
+`phaseViewPayload x z (View.encode ⟨x,z,[],h⟩) = Strategy.encodeMsgs h`. -/
+theorem phaseViewPayload_of_encode (x z : List Bool) (h : List (List Bool)) :
+    phaseViewPayload x z (View.encode ⟨x, z, [], h⟩) = Strategy.encodeMsgs h := by
+  simp only [phaseViewPayload_eq, View.encode_mk, pairSndD_pairEncode,
+    encodeMsgs_eq_encWords, BinArith.decWords_encWords, if_true]
+
+/-- Failed validation produces an empty payload: if `raw` differs from the canonical view
+`⟨x,z,[],decWords (pairSndD (pairSndD raw))⟩`, then `phaseViewPayload x z raw = []`. -/
+theorem phaseViewPayload_of_ne (x z raw : List Bool)
+    (hraw : raw ≠ View.encode ⟨x, z, [], BinArith.decWords (pairSndD (pairSndD raw))⟩) :
+    phaseViewPayload x z raw = [] := by
+  rw [phaseViewPayload_eq, if_neg hraw]
+
+/-- Phase-view normalization fixes a canonical bounded real view:
+`normalizePhaseMsgs x z p B (View.encode ⟨x,z,[],h⟩) = h` if `h.length = p` and
+`∀ m ∈ h, m.length ≤ B`. -/
+theorem normalizePhaseMsgs_of_encode (x z : List Bool) (p B : ℕ) (h : List (List Bool))
+    (hp : h.length = p) (hB : ∀ m ∈ h, m.length ≤ B) :
+    normalizePhaseMsgs x z p B (View.encode ⟨x, z, [], h⟩) = h := by
+  rw [normalizePhaseMsgs_eq, phaseViewPayload_of_encode]
+  exact normalizeMsgs_encodeMsgs p B h hp hB
+
+/-- Every phase-view normalization has exactly `p` slots:
+`(normalizePhaseMsgs x z p B raw).length = p`. -/
+theorem length_normalizePhaseMsgs (x z : List Bool) (p B : ℕ) (raw : List Bool) :
+    (normalizePhaseMsgs x z p B raw).length = p := by
+  rw [normalizePhaseMsgs_eq]
+  exact length_normalizeMsgs p B _
+
+/-- Each normalized phase message has at most `B` bits:
+`m ∈ normalizePhaseMsgs x z p B raw → m.length ≤ B`. -/
+theorem length_le_of_mem_normalizePhaseMsgs (x z : List Bool) (p B : ℕ) (raw : List Bool)
+    {m : List Bool} (hm : m ∈ normalizePhaseMsgs x z p B raw) : m.length ≤ B := by
+  rw [normalizePhaseMsgs_eq] at hm
+  exact length_le_of_mem_normalizeMsgs p B _ hm
+
+/-- The normalized phase message encoding is bounded by
+`(Strategy.encodeMsgs (normalizePhaseMsgs x z p B raw)).length ≤ p * (2 * B + 2)`. -/
+theorem length_encodeMsgs_normalizePhaseMsgs_le (x z : List Bool) (p B : ℕ) (raw : List Bool) :
+    (Strategy.encodeMsgs (normalizePhaseMsgs x z p B raw)).length ≤ p * (2 * B + 2) := by
+  rw [normalizePhaseMsgs_eq]
+  exact length_encodeMsgs_normalizeMsgs_le p B _
+
+/-- A malformed phase view yields exactly `p` empty messages:
+`normalizePhaseMsgs x z p B raw = List.replicate p []` when validation fails. -/
+theorem normalizePhaseMsgs_of_ne (x z : List Bool) (p B : ℕ) (raw : List Bool)
+    (hraw : raw ≠ View.encode ⟨x, z, [], BinArith.decWords (pairSndD (pairSndD raw))⟩) :
+    normalizePhaseMsgs x z p B raw = List.replicate p [] := by
+  rw [normalizePhaseMsgs_eq, phaseViewPayload_of_ne x z raw hraw, normalizeMsgs_eq,
+    BinArith.decWords_nil]
+  simp only [List.getD_eq_getElem?_getD, List.getElem?_nil, Option.getD_none,
+    List.take_nil, List.map_const', List.length_range]
+
+/-- Canonical phase-view validation is polynomial-time: polynomial-time `x`, `z` and `raw`
+give a polynomial-time map `w ↦ phaseViewPayload (x w) (z w) (raw w)`.
+`PolyTimeComputable fun w => phaseViewPayload (x w) (z w) (raw w)`.
+
+**Proof sketch.** Extract the candidate message word through two pair projections, and
+canonically reencode its total decoding through the word-map host. Pair this encoding with
+the known common input, auxiliary input, and empty wrapper tape. The public word-equality
+machine checks whether that reconstructed view equals the original word; a conditional
+machine returns the extracted payload on success and the empty word on failure. -/
+theorem polyTimeComputable_phaseViewPayload {x z raw : List Bool → List Bool}
+    (hx : PolyTimeComputable x) (hz : PolyTimeComputable z) (hraw : PolyTimeComputable raw) :
+    PolyTimeComputable fun w => phaseViewPayload (x w) (z w) (raw w) := by
+  -- Reconstruct the canonical candidate with the prescribed metadata and tape.
+  have hpayload : PolyTimeComputable fun w => pairSndD (pairSndD (raw w)) :=
+    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp hraw)
+  have hcanonical := polyTimeComputable_encWords_decWords hpayload
+  have hview : PolyTimeComputable fun w => pairEncode (pairEncode (x w) (z w))
+      (pairEncode [] (BinArith.encWords (BinArith.decWords (pairSndD (pairSndD (raw w)))))) :=
+    (hx.pairEncode hz).pairEncode ((polyTimeComputable_const []).pairEncode hcanonical)
+  -- Compare the candidate with the original and select the validated payload.
+  have htest := BinArith.polyTimeComputable_eqW.comp (hraw.pairEncode hview)
+  refine (polyTimeComputable_ite htest hpayload (polyTimeComputable_const [])).congr ?_
+  intro w
+  simp only [phaseViewPayload_eq, BinArith.eqW_pairEncode,
+    decide_eq_true_eq, View.encode_mk, encodeMsgs_eq_encWords]
+
+/-- Canonical bounded phase-view normalization is polynomial-time: polynomial-time `x`, `z`
+and `raw`, and unary-computable `p` and `B`, give a polynomial-time map
+`w ↦ Strategy.encodeMsgs (normalizePhaseMsgs (x w) (z w) (p w) (B w) (raw w))`.
+[PS10, Theorem 175.1, bounded canonical phase-view normalization].
+`PolyTimeComputable fun w => Strategy.encodeMsgs (normalizePhaseMsgs (x w) (z w) (p w) (B w) (raw
+w))`. -/
+theorem polyTimeComputable_encode_normalizePhaseMsgs {x z raw : List Bool → List Bool}
+    {p B : List Bool → ℕ}
+    (hx : PolyTimeComputable x) (hz : PolyTimeComputable z) (hraw : PolyTimeComputable raw)
+    (hp : PolyTimeComputable fun w => List.replicate (p w) true)
+    (hB : PolyTimeComputable fun w => List.replicate (B w) true) :
+    PolyTimeComputable fun w =>
+      Strategy.encodeMsgs (normalizePhaseMsgs (x w) (z w) (p w) (B w) (raw w)) := by
+  have hpayload := polyTimeComputable_phaseViewPayload hx hz hraw
+  refine (polyTimeComputable_encode_normalizeMsgs hp hB hpayload).congr ?_
+  intro w
+  rw [normalizePhaseMsgs_eq]
+
+end TCSlib.Cryptography.SequentialZK
diff --git a/TCSlib/Cryptography/Composability/SequentialZK/Phases.lean b/TCSlib/Cryptography/Composability/SequentialZK/Phases.lean
new file mode 100644
index 000000000..c8abf4048
--- /dev/null
+++ b/TCSlib/Cryptography/Composability/SequentialZK/Phases.lean
@@ -0,0 +1,142 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Composability.SequentialZK.Soundness
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# A prover with a fixed earlier transcript
+
+## Main definitions
+
+* `Composability.prefixProver`: a prover with its original auxiliary input, tape, and
+  previously received messages fixed in advance.
+
+## Main results
+
+* `Composability.exec_phase_of_moves`: source replies matching arbitrary local strategies
+  give a phase coupling with the fixed earlier histories.
+* `Composability.exec_phase`: an execution after a fixed move offset is its earlier
+  transcript followed by an execution of the prefix-hardwired prover, whenever the
+  verifier's real-phase replies and the mover pattern agree.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §4.4 (interactive executions) and Theorem 175.1 (sequential composition).
+-/
+
+namespace TCSlib.Cryptography.Composability
+
+/-- For a strategy `P`, auxiliary input `y`, fixed tape `rP`, and earlier received messages
+`prior`, `prefixProver P y rP prior` has zero coins and sends
+`P.next x y rP (prior ++ hist)` on `x`, any auxiliary input, any tape, and history `hist`.
+[PS10, Theorem 175.1, the prover induced by a fixed earlier transcript]. -/
+@[simps (config := { isSimp := false }) coins next]
+def prefixProver (P : Strategy) (y rP : List Bool)
+    (prior : List (List Bool)) : Strategy where
+  next x _ _ hist := P.next x y rP (prior ++ hist)
+  coins := .const 0
+
+/-- For source strategies `P`, `V`, local strategies `P0`, `V0`, mover flag `vFirst`,
+common input `x`, source auxiliary inputs `y`, `z` and tapes `rP`, `rV`, local auxiliary
+inputs `y0`, `z0` and tapes `rP0`, `rV0`, offset `g`, and budget `k`, suppose the mover
+patterns agree and each active source reply before `k` equals the local party's reply on
+the source history with its pre-`g` prefix dropped. For `t ≤ k`, both source histories at
+`g+t` equal their pre-`g` histories followed by the corresponding components of
+`exec P0 V0 vFirst x y0 z0 rP0 rV0 t`. [PS10, Theorem 175.1, phase coupling].
+
+**Proof sketch.** Induct on `t`. Both local histories are empty at zero. At a later move,
+the induction equalities identify each full source history with its fixed earlier prefix
+followed by the local history. Dropping this prefix gives the local party's received
+history. The supplied active-move equation therefore gives a common next message, and
+append associativity preserves both transcript decompositions. -/
+theorem exec_phase_of_moves (P V P0 V0 : Strategy) (vFirst : Bool)
+    (x y z rP rV y0 z0 rP0 rV0 : List Bool) (g k : ℕ)
+    (hturn : ∀ t < k, moverIsV vFirst (g + t) = moverIsV vFirst t)
+    (hP : ∀ t < k, moverIsV vFirst t = false →
+      P.next x y rP (exec P V vFirst x y z rP rV (g + t)).1 =
+        P0.next x y0 rP0
+          ((exec P V vFirst x y z rP rV (g + t)).1.drop
+            (exec P V vFirst x y z rP rV g).1.length))
+    (hV : ∀ t < k, moverIsV vFirst t = true →
+      V.next x z rV (exec P V vFirst x y z rP rV (g + t)).2 =
+        V0.next x z0 rV0
+          ((exec P V vFirst x y z rP rV (g + t)).2.drop
+            (exec P V vFirst x y z rP rV g).2.length))
+    {t : ℕ} (ht : t ≤ k) :
+    (exec P V vFirst x y z rP rV (g + t)).1 =
+        (exec P V vFirst x y z rP rV g).1 ++
+          (exec P0 V0 vFirst x y0 z0 rP0 rV0 t).1 ∧
+      (exec P V vFirst x y z rP rV (g + t)).2 =
+        (exec P V vFirst x y z rP rV g).2 ++
+          (exec P0 V0 vFirst x y0 z0 rP0 rV0 t).2 := by
+  revert ht
+  induction t with
+  | zero =>
+    intro _
+    rw [Nat.add_zero, exec_zero]
+    simp only [List.append_nil, and_self]
+  | succ t ih =>
+    intro ht
+    have htk : t < k := by omega
+    obtain ⟨ihP, ihV⟩ := ih (by omega)
+    -- The source and local executions make the same kind of move.
+    rw [Nat.add_succ, exec_succ, exec_succ, hturn t htk]
+    by_cases hm : moverIsV vFirst t = true
+    · simp only [hm, if_true]
+      have hnext := hV t htk hm
+      rw [ihV, List.drop_left] at hnext
+      constructor
+      · rw [ihP, ihV, hnext, List.append_assoc]
+      · exact ihV
+    · simp only [Bool.not_eq_true] at hm
+      simp only [hm, Bool.false_eq_true, if_false]
+      have hnext := hP t htk hm
+      rw [ihP, List.drop_left] at hnext
+      constructor
+      · exact ihP
+      · rw [ihV, ihP, hnext, List.append_assoc]
+
+/-- For strategies `P`, `V`, `W`, mover flag `vFirst`, input `x`, auxiliary inputs `y`, `z`,
+tapes `rP`, `rV`, `rW`, offset `g`, and budget `k`, suppose the mover at `g+t` equals the
+mover at `t`, and at every verifier move before `k`, `V` on the full history equals `W` on
+that history with the messages preceding `g` dropped. For `t ≤ k`, each received history
+after `g+t` moves equals its history after `g` followed by the corresponding history of
+`prefixProver P y rP (exec P V vFirst x y z rP rV g).1` against `W` for `t` moves.
+[PS10, Theorem 175.1, a phase with the earlier transcript fixed].
+
+**Proof sketch.** Apply the generic phase-coupling theorem. The supplied verifier equation
+is its verifier-move premise. For the prover premise, the earlier received history is a
+prefix of the current one, so prepending it to the dropped suffix recovers the full
+history. The hardwired prover's published message equation gives the required reply. -/
+theorem exec_phase (P V W : Strategy) (vFirst : Bool)
+    (x y z rP rV rW : List Bool) (g k : ℕ)
+    (hturn : ∀ t < k, moverIsV vFirst (g + t) = moverIsV vFirst t)
+    (hV : ∀ t < k, moverIsV vFirst t = true →
+      V.next x z rV (exec P V vFirst x y z rP rV (g + t)).2 =
+        W.next x z rW
+          ((exec P V vFirst x y z rP rV (g + t)).2.drop
+            (exec P V vFirst x y z rP rV g).2.length))
+    {t : ℕ} (ht : t ≤ k) :
+    (exec P V vFirst x y z rP rV (g + t)).1 =
+        (exec P V vFirst x y z rP rV g).1 ++
+          (exec (prefixProver P y rP (exec P V vFirst x y z rP rV g).1)
+            W vFirst x [] z [] rW t).1 ∧
+      (exec P V vFirst x y z rP rV (g + t)).2 =
+        (exec P V vFirst x y z rP rV g).2 ++
+          (exec (prefixProver P y rP (exec P V vFirst x y z rP rV g).1)
+            W vFirst x [] z [] rW t).2 := by
+  apply exec_phase_of_moves P V
+    (prefixProver P y rP (exec P V vFirst x y z rP rV g).1) W vFirst
+    x y z rP rV [] z [] rW g k hturn ?_ hV ht
+  intro t _ _
+  rw [prefixProver_next]
+  have hp := (exec_prefix P V vFirst x y z rP rV g t).1
+  rw [List.prefix_iff_eq_append.mp hp]
+
+end TCSlib.Cryptography.Composability
diff --git a/TCSlib/Cryptography/Composability/SequentialZK/PrefixFolds.lean b/TCSlib/Cryptography/Composability/SequentialZK/PrefixFolds.lean
new file mode 100644
index 000000000..577c31b48
--- /dev/null
+++ b/TCSlib/Cryptography/Composability/SequentialZK/PrefixFolds.lean
@@ -0,0 +1,114 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Composability.SequentialZK.WrappedVerifier
+import TCSlib.Cryptography.Composability.SequentialZK.PhaseView
+import TCSlib.Cryptography.ZeroKnowledge.Defs
+import Mathlib.Data.Fin.Tuple.Basic
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Real and normalized phase-prefix folds
+
+## Main definitions
+
+* `realStep`, `simStep`: append a real or normalized phase and its empty prover fillers.
+* `realPrefix`, `simPrefix`: semantic folds on independent typed phase coins.
+
+These definitions directly use the public core `Fin.foldl` combinator. They specify finite
+samplers; they introduce no machine or control host. The strict-PPT simulator is supplied by
+`SimulatorMachine`, using the previously published counted-loop host.
+
+## Main results
+
+* The `_eq` readers publish each step and fold formula.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  Theorem 175.1 (sequential composition).
+* [Gol01] O. Goldreich, *Foundations of Cryptography, Volume I: Basic Tools*, Cambridge
+  University Press, 2001, §4.3.4 (sequential composition).
+-/
+
+namespace TCSlib.Cryptography.SequentialZK
+
+open Complexity
+
+/-- For `π,V,x,y,z,rV,p,i,pre,rP`, append to `pre` the real verifier-received messages of
+`π.P` against `phaseVerifier V` at `phaseAux z rV i pre` on tapes `List.ofFn rP, []`, then
+`π.rounds.eval |x| - p` empty prover fillers. [PS10, Theorem 175.1].
+`realStep π V x y z rV p i pre rP = pre ++ ((exec π.P (phaseVerifier V) π.verifierFirst x y
+(phaseAux z rV i pre) (List.ofFn rP) [] (π.rounds.eval x.length)).2 ++ List.replicate (π.rounds.eval
+x.length - p) [])`. -/
+def realStep (π : Protocol) (V : Strategy) (x y z rV : List Bool) (p i : ℕ)
+    (pre : List (List Bool)) (rP : π.P.Coins x.length) : List (List Bool) :=
+  pre ++ ((exec π.P (phaseVerifier V) π.verifierFirst x y (phaseAux z rV i pre)
+    (List.ofFn rP) [] (π.rounds.eval x.length)).2 ++
+      List.replicate (π.rounds.eval x.length - p) [])
+
+/-- `realStep π V x y z rV p i pre rP` is `pre` followed by the original real phase's
+received messages on `(List.ofFn rP, [])`, then `k-p` empty fillers, for `k=π.rounds.eval |x|`.
+-/
+theorem realStep_eq (π : Protocol) (V : Strategy) (x y z rV : List Bool) (p i : ℕ)
+    (pre : List (List Bool)) (rP : π.P.Coins x.length) :
+    realStep π V x y z rV p i pre rP =
+      pre ++ ((exec π.P (phaseVerifier V) π.verifierFirst x y (phaseAux z rV i pre)
+        (List.ofFn rP) [] (π.rounds.eval x.length)).2 ++
+          List.replicate (π.rounds.eval x.length - p) []) := rfl
+
+/-- For `S,x,z,rV,k,B,p,i,pre,rS`, append the `p` normalized `B`-bounded messages decoded
+from `S.simulate x (phaseAux z rV i pre) rS`, followed by `k-p` empty fillers.
+[PS10, Theorem 175.1; Gol01, §4.3.4].
+`simStep S x z rV k B p i pre rS = pre ++ (normalizePhaseMsgs x (phaseAux z rV i pre) p B
+(S.simulate x (phaseAux z rV i pre) rS) ++ List.replicate (k - p) [])`. -/
+def simStep (S : NUPPT) (x z rV : List Bool) (k B p i : ℕ)
+    (pre : List (List Bool)) (rS : S.Coins x.length) : List (List Bool) :=
+  pre ++ (normalizePhaseMsgs x (phaseAux z rV i pre) p B
+    (S.simulate x (phaseAux z rV i pre) rS) ++ List.replicate (k - p) [])
+
+/-- `simStep S x z rV k B p i pre rS` appends the normalized phase result and `k-p` empty
+fillers to `pre`, using auxiliary word `phaseAux z rV i pre`.
+`simStep S x z rV k B p i pre rS = pre ++ (normalizePhaseMsgs x (phaseAux z rV i pre) p B
+(S.simulate x (phaseAux z rV i pre) rS) ++ List.replicate (k - p) [])`. -/
+theorem simStep_eq (S : NUPPT) (x z rV : List Bool) (k B p i : ℕ)
+    (pre : List (List Bool)) (rS : S.Coins x.length) :
+    simStep S x z rV k B p i pre rS =
+      pre ++ (normalizePhaseMsgs x (phaseAux z rV i pre) p B
+        (S.simulate x (phaseAux z rV i pre) rS) ++ List.replicate (k - p) []) := rfl
+
+/-- `realPrefix π V x y z rV p q r` folds the `q` real phase steps, starting with `[]` and
+using `r i` in phase `i`. [PS10, Theorem 175.1].
+`realPrefix π V x y z rV p q r = Fin.foldl q (fun pre i => realStep π V x y z rV p i pre (r i))
+[]`. -/
+def realPrefix (π : Protocol) (V : Strategy) (x y z rV : List Bool) (p q : ℕ)
+    (r : Fin q → π.P.Coins x.length) : List (List Bool) :=
+  Fin.foldl q (fun pre i => realStep π V x y z rV p i pre (r i)) []
+
+/-- `realPrefix π V x y z rV p q r = Fin.foldl q (fun pre i => realStep … i pre (r i)) []`.
+-/
+theorem realPrefix_eq (π : Protocol) (V : Strategy) (x y z rV : List Bool) (p q : ℕ)
+    (r : Fin q → π.P.Coins x.length) :
+    realPrefix π V x y z rV p q r =
+      Fin.foldl q (fun pre i => realStep π V x y z rV p i pre (r i)) [] := rfl
+
+/-- `simPrefix S x z rV k B p q r` folds the `q` normalized phase steps from `[]`, using
+`r i` in phase `i`. [PS10, Theorem 175.1; Gol01, §4.3.4].
+`simPrefix S x z rV k B p q r = Fin.foldl q (fun pre i => simStep S x z rV k B p i pre (r i))
+[]`. -/
+def simPrefix (S : NUPPT) (x z rV : List Bool) (k B p q : ℕ)
+    (r : Fin q → S.Coins x.length) : List (List Bool) :=
+  Fin.foldl q (fun pre i => simStep S x z rV k B p i pre (r i)) []
+
+/-- `simPrefix S x z rV k B p q r = Fin.foldl q (fun pre i => simStep … i pre (r i)) []`.
+-/
+theorem simPrefix_eq (S : NUPPT) (x z rV : List Bool) (k B p q : ℕ)
+    (r : Fin q → S.Coins x.length) :
+    simPrefix S x z rV k B p q r =
+      Fin.foldl q (fun pre i => simStep S x z rV k B p i pre (r i)) [] := rfl
+
+end TCSlib.Cryptography.SequentialZK
diff --git a/TCSlib/Cryptography/Composability/SequentialZK/PrefixLaws.lean b/TCSlib/Cryptography/Composability/SequentialZK/PrefixLaws.lean
new file mode 100644
index 000000000..a71eb94c9
--- /dev/null
+++ b/TCSlib/Cryptography/Composability/SequentialZK/PrefixLaws.lean
@@ -0,0 +1,126 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Composability.SequentialZK.PrefixFolds
+import TCSlib.Cryptography.Composability.SequentialZK.SimulatorMachine
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Phase-fold equations and simulator endpoint
+
+## Main definitions
+
+This module introduces no definitions.
+
+## Main results
+
+* `realPrefix_zero`, `simPrefix_zero`: no phases give the empty history.
+* `realPrefix_succ`, `simPrefix_succ`: the last coin extends the earlier prefix by one step.
+* `realPrefix_snoc`, `simPrefix_snoc`: the corresponding independent-table snoc equations.
+
+The fold equations directly reuse core `Fin.foldl_zero` and `Fin.foldl_succ_last`.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  Theorem 175.1 (sequential composition).
+* [Gol01] O. Goldreich, *Foundations of Cryptography, Volume I: Basic Tools*, Cambridge
+  University Press, 2001, §4.3.4 (sequential composition).
+-/
+
+namespace TCSlib.Cryptography.SequentialZK
+
+open Complexity
+
+/-- For `π,V,x,y,z,rV,p,r`, `realPrefix π V x y z rV p 0 r = []`. -/
+theorem realPrefix_zero (π : Protocol) (V : Strategy) (x y z rV : List Bool) (p : ℕ)
+    (r : Fin 0 → π.P.Coins x.length) : realPrefix π V x y z rV p 0 r = [] := by
+  rw [realPrefix_eq, Fin.foldl_zero]
+
+/-- For `π,V,x,y,z,rV,p,q,r`, the prefix on `q+1` coins equals `realStep` at index `q`
+applied to the prefix on the first `q` coins and to the last coin `r (Fin.last q)`.
+`realPrefix π V x y z rV p (q + 1) r = realStep π V x y z rV p q (realPrefix π V x y z rV p q (fun i
+=> r i.castSucc)) (r (Fin.last q))`. -/
+theorem realPrefix_succ (π : Protocol) (V : Strategy) (x y z rV : List Bool) (p q : ℕ)
+    (r : Fin (q + 1) → π.P.Coins x.length) :
+    realPrefix π V x y z rV p (q + 1) r =
+      realStep π V x y z rV p q
+        (realPrefix π V x y z rV p q (fun i => r i.castSucc)) (r (Fin.last q)) := by
+  rw [realPrefix_eq, Fin.foldl_succ_last, realPrefix_eq]
+  rfl
+
+/-- For `π,V,x,y,z,rV,p,q,r,coin`, appending `coin` to `r` extends its real prefix by
+`realStep π V x y z rV p q` on that coin.
+`realPrefix π V x y z rV p (q + 1) (Fin.snoc r coin) = realStep π V x y z rV p q (realPrefix π V x y
+z rV p q r) coin`. -/
+theorem realPrefix_snoc (π : Protocol) (V : Strategy) (x y z rV : List Bool) (p q : ℕ)
+    (r : Fin q → π.P.Coins x.length) (coin : π.P.Coins x.length) :
+    realPrefix π V x y z rV p (q + 1) (Fin.snoc r coin) =
+      realStep π V x y z rV p q (realPrefix π V x y z rV p q r) coin := by
+  rw [realPrefix_succ]
+  simp only [Fin.snoc_castSucc, Fin.snoc_last]
+
+/-- For `S,x,z,rV,k,B,p,r`, `simPrefix S x z rV k B p 0 r = []`. -/
+theorem simPrefix_zero (S : NUPPT) (x z rV : List Bool) (k B p : ℕ)
+    (r : Fin 0 → S.Coins x.length) : simPrefix S x z rV k B p 0 r = [] := by
+  rw [simPrefix_eq, Fin.foldl_zero]
+
+/-- For `S,x,z,rV,k,B,p,q,r`, the prefix on `q+1` coins equals `simStep` at index `q`
+applied to the prefix on the first `q` coins and to the last coin `r (Fin.last q)`.
+`simPrefix S x z rV k B p (q + 1) r = simStep S x z rV k B p q (simPrefix S x z rV k B p q (fun i =>
+r i.castSucc)) (r (Fin.last q))`. -/
+theorem simPrefix_succ (S : NUPPT) (x z rV : List Bool) (k B p q : ℕ)
+    (r : Fin (q + 1) → S.Coins x.length) :
+    simPrefix S x z rV k B p (q + 1) r =
+      simStep S x z rV k B p q
+        (simPrefix S x z rV k B p q (fun i => r i.castSucc)) (r (Fin.last q)) := by
+  rw [simPrefix_eq, Fin.foldl_succ_last, simPrefix_eq]
+  rfl
+
+/-- For `S,x,z,rV,k,B,p,q,r,coin`, appending `coin` to `r` extends its normalized prefix by
+`simStep S x z rV k B p q` on that coin.
+`simPrefix S x z rV k B p (q + 1) (Fin.snoc r coin) = simStep S x z rV k B p q (simPrefix S x z rV k
+B p q r) coin`. -/
+theorem simPrefix_snoc (S : NUPPT) (x z rV : List Bool) (k B p q : ℕ)
+    (r : Fin q → S.Coins x.length) (coin : S.Coins x.length) :
+    simPrefix S x z rV k B p (q + 1) (Fin.snoc r coin) =
+      simStep S x z rV k B p q (simPrefix S x z rV k B p q r) coin := by
+  rw [simPrefix_succ]
+  simp only [Fin.snoc_castSucc, Fin.snoc_last]
+
+/-- For `S,k,B,verifierFirst,x,z,rV,rS,q,coins`, if every block `i<q` of `rS` is
+`List.ofFn (coins i)`, the typed normalized fold equals the simulator prefix:
+`simPrefix … q coins = phasePrefix S k B verifierFirst x z rV rS q`, using the numeric real
+message count `if verifierFirst then k(|x|)/2 else (k(|x|)+1)/2`.
+[PS10, Theorem 175.1; Gol01, §4.3.4].
+
+**Proof sketch.** Induct on the phase count. Remove the last typed coin from the fold and
+use the simulator's published phase reader on the corresponding raw coin block. The
+induction hypothesis identifies the earlier prefixes; both final steps then normalize the
+same simulator call and append the same empty fillers. -/
+theorem simPrefix_eq_phasePrefix (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
+    (x z rV rS : List Bool) (q : ℕ) (coins : Fin q → S.Coins x.length)
+    (hcoins : ∀ i : Fin q, coinBlock (S.coinLen x.length) i rS = List.ofFn (coins i)) :
+    simPrefix S x z rV (k.eval x.length) (B.eval x.length)
+      (if verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2) q coins =
+        phasePrefix S k B verifierFirst x z rV rS q := by
+  induction q with
+  | zero => rw [simPrefix_zero, phasePrefix_zero]
+  | succ q ih =>
+    -- Restrict the typed table to its earlier coordinates.
+    have hpre := ih (fun i : Fin q => coins i.castSucc) (fun i => by
+      simpa only [Fin.coe_castSucc] using hcoins i.castSucc)
+    have hlast : coinBlock (S.coinLen x.length) q rS =
+        List.ofFn (coins (Fin.last q)) := by
+      simpa only [Fin.val_last] using hcoins (Fin.last q)
+    -- Both endpoint readers append the same last normalized phase.
+    rw [simPrefix_succ, phasePrefix_succ_simulate S k B verifierFirst x z rV rS q
+      (coins (Fin.last q)) hlast]
+    dsimp only
+    rw [hpre, simStep_eq]
+
+end TCSlib.Cryptography.SequentialZK
diff --git a/TCSlib/Cryptography/Composability/SequentialZK/ProofTransfers.lean b/TCSlib/Cryptography/Composability/SequentialZK/ProofTransfers.lean
new file mode 100644
index 000000000..f7f6b19f6
--- /dev/null
+++ b/TCSlib/Cryptography/Composability/SequentialZK/ProofTransfers.lean
@@ -0,0 +1,75 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Composability.SequentialZK.PaddedProverSpec
+import TCSlib.Cryptography.ZeroKnowledge.InteractiveProofs
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Completeness transfer through a padded-prover contract
+
+## Main definitions
+
+This module introduces no definitions.
+
+## Main results
+
+* `PaddedProverSpec.next_length_le`: repeated replies keep an original message-length bound.
+* `PaddedProverSpec.complete`: pointwise acceptance transfer preserves the bounded
+  completeness clause, using the published witness-completeness constructor.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  Theorem 175.1 (sequential repetition of interactive proofs).
+-/
+
+namespace TCSlib.Cryptography.SequentialZK.PaddedProverSpec
+
+open Complexity
+
+/-- For `d : PaddedProverSpec π ρ x q p`, auxiliary input `y`, bound `B`, and an original
+reply bound `∀ r hist, |π.P.next x y r hist| ≤ B`, every repeated reply has length at most
+`B`: `∀ r hist, |ρ.P.next x y r hist| ≤ B`. [PS10, Theorem 175.1]. -/
+theorem next_length_le {π ρ : Protocol} {x : List Bool} {q p : ℕ}
+    (d : PaddedProverSpec π ρ x q p) (y : List Bool) (B : ℕ)
+    (hB : ∀ r hist, (π.P.next x y r hist).length ≤ B) :
+    ∀ r hist, (ρ.P.next x y r hist).length ≤ B := by
+  intro r hist
+  rw [d.next]
+  dsimp only
+  split_ifs <;> first | exact hB _ _ | exact Nat.zero_le _
+
+/-- For pointwise construction contracts `d`, if acceptance on every `x,y,z` transfers
+from `π` to `ρ`, then a bounded completeness witness for each `x ∈ L` in `π` is also one
+in `ρ`, with the same polynomial bound. [PS10, Theorem 175.1].
+
+**Proof sketch.** Use the original reply bound and perfect acceptance together as a witness
+relation. The padded next-message reader preserves that bound. The published bounded-witness
+completeness constructor then uses the transferred acceptance on every such witness. -/
+theorem complete {π ρ : Protocol} {L : Language Bool} {q p : List Bool → ℕ}
+    (d : ∀ x, PaddedProverSpec π ρ x (q x) (p x))
+    (haccept : ∀ x y z, (uprob (fun r : π.ExecCoins π.P x =>
+      π.outV π.P x y z r = [true]) = 1) →
+        uprob (fun r : ρ.ExecCoins ρ.P x => ρ.outV ρ.P x y z r = [true]) = 1)
+    (hc : ∃ B : PolyExpr, ∀ x ∈ L, ∃ y : List Bool,
+      (∀ r hist, (π.P.next x y r hist).length ≤ B.eval x.length) ∧
+        ∀ z, uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1) :
+    ∃ B : PolyExpr, ∀ x ∈ L, ∃ y : List Bool,
+      (∀ r hist, (ρ.P.next x y r hist).length ≤ B.eval x.length) ∧
+        ∀ z, uprob (fun r : ρ.ExecCoins ρ.P x => ρ.outV ρ.P x y z r = [true]) = 1 := by
+  obtain ⟨B, hcomplete⟩ := hc
+  let R : List Bool → List Bool → Prop := fun x y =>
+    (∀ r hist, (π.P.next x y r hist).length ≤ B.eval x.length) ∧
+      ∀ z, uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1
+  have hbounded : ρ.ProverBounded R B := by
+    rw [Protocol.proverBounded_iff]
+    intro x y r hist hR
+    exact (d x).next_length_le y (B.eval x.length) hR.1 r hist
+  exact hbounded.exists_complete hcomplete (fun x y hR z => haccept x y z (hR.2 z))
+
+end TCSlib.Cryptography.SequentialZK.PaddedProverSpec
diff --git a/TCSlib/Cryptography/Composability/SequentialZK/RealPhases.lean b/TCSlib/Cryptography/Composability/SequentialZK/RealPhases.lean
new file mode 100644
index 000000000..4ce56e67a
--- /dev/null
+++ b/TCSlib/Cryptography/Composability/SequentialZK/RealPhases.lean
@@ -0,0 +1,209 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Composability.SequentialZK.Phases
+import TCSlib.Cryptography.Composability.SequentialZK.WrappedVerifier
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Real phases against an arbitrary verifier
+
+The real portion of a padded sequential phase is an original execution against the
+fixed-tape phase verifier. The honest repeated prover's remaining replies are empty, while
+the other party's filler replies are unrestricted. The phase coupling reuses the published
+`Composability.exec_phase_of_moves` reader; this file does not repeat its execution induction.
+
+## Main definitions
+
+There are no new definitions.
+
+## Main results
+
+* `exec_snd_empty`: a suffix of empty prover replies appends only empty received messages.
+* `exec_real_phase`: a real phase is coupled to the original prover and phase verifier.
+* `exec_padded_real_phase`: the full padded phase appends the real messages and empty fillers.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §7.2.1, Theorem 175.1.
+* [Gol01] O. Goldreich, *Foundations of Cryptography, Volume I: Basic Tools*, Cambridge
+  University Press, 2001, §4.3.4.
+-/
+
+namespace TCSlib.Cryptography.SequentialZK
+
+open Complexity Turing Composability
+
+/-- For strategies `P,V`, orientation `vFirst`, fixed inputs/tapes `x,y,z,rP,rV`, and an
+interval of `t` moves after `g`, if every active prover reply is empty, the verifier's
+received history appends exactly as many empty messages as its length increases.
+[PS10, Theorem 175.1, honest-prover fillers].
+`(exec P V vFirst x y z rP rV (g + t)).2 = (exec P V vFirst x y z rP rV g).2 ++ List.replicate
+((exec P V vFirst x y z rP rV (g + t)).2.length - (exec P V vFirst x y z rP rV g).2.length) []`.
+
+**Proof sketch.** Induct on the interval length to express the new received history as the
+old history followed by some number of empty messages. Verifier moves keep it fixed and
+prover moves append one empty message. Taking lengths determines that number exactly.
+The verifier's own replies are unrestricted throughout. -/
+theorem exec_snd_empty (P V : Strategy) (vFirst : Bool) (x y z rP rV : List Bool) (g t : ℕ)
+    (hEmpty : ∀ i < t, moverIsV vFirst (g + i) = false →
+      P.next x y rP (exec P V vFirst x y z rP rV (g + i)).1 = []) :
+    (exec P V vFirst x y z rP rV (g + t)).2 =
+      (exec P V vFirst x y z rP rV g).2 ++ List.replicate
+        ((exec P V vFirst x y z rP rV (g + t)).2.length -
+          (exec P V vFirst x y z rP rV g).2.length) [] := by
+  -- Each active prover move contributes one further empty slot.
+  have hex : ∀ u, u ≤ t → ∃ a,
+      (exec P V vFirst x y z rP rV (g + u)).2 =
+        (exec P V vFirst x y z rP rV g).2 ++ List.replicate a [] := by
+    intro u
+    induction u with
+    | zero =>
+      intro _
+      exact ⟨0, by rw [Nat.add_zero, List.replicate_zero, List.append_nil]⟩
+    | succ u ih =>
+      intro hu
+      obtain ⟨a, ha⟩ := ih (by omega)
+      rw [Nat.add_succ, exec_succ]
+      by_cases hm : moverIsV vFirst (g + u) = true
+      · simp only [hm, if_true]
+        exact ⟨a, ha⟩
+      · have hmf : moverIsV vFirst (g + u) = false := by simpa only [Bool.not_eq_true] using hm
+        have he := hEmpty u (by omega) hmf
+        simp only [hmf, Bool.false_eq_true, if_false]
+        refine ⟨a + 1, ?_⟩
+        rw [he, ha, List.replicate_add, List.replicate_one, List.append_assoc]
+  -- The exact length difference identifies the number of appended slots.
+  obtain ⟨a, ha⟩ := hex t le_rfl
+  have hlen : (exec P V vFirst x y z rP rV (g + t)).2.length =
+      (exec P V vFirst x y z rP rV g).2.length + a := by
+    rw [ha, List.length_append, List.length_replicate]
+  rw [hlen, Nat.add_sub_cancel_left]
+  exact ha
+
+/-- For a repeated prover `Pseq`, original prover `P`, arbitrary verifier `V`, fixed
+inputs/tapes, and phase `j<q`, assume the padded next-message equation, recovery of the
+global prover-move index, the phase-start prover-history length `j*k`, and the supplied
+mover-period equation. For `t≤k`, the source histories at `2*k*j+t` are their phase-start
+histories followed by the original execution of `P` on coin block `j` against
+`phaseVerifier V` with `phaseAux z rV j` of the earlier verifier history.
+[PS10, Theorem 175.1; Gol01, §4.3.4, real-phase coupling].
+
+**Proof sketch.** Apply the published coupling theorem for active moves. Index recovery
+gives phase `j` and position `t<k`, so the repeated prover uses exactly the original prover's
+coin block and dropped phase history. The wrapped verifier prepends the earlier verifier
+history; that history is a prefix of the reached source history by `exec_snd_take`. Its
+reply is therefore exactly the source verifier's reply. The existing coupling theorem supplies
+both transcript decompositions, without another induction over the real phase. -/
+theorem exec_real_phase (Pseq P V : Strategy) (vFirst : Bool)
+    (x y z rP rV : List Bool) (k q j : ℕ) (hj : j < q)
+    (hPseq : ∀ hist : List (List Bool), Pseq.next x y rP hist =
+      let idx := if vFirst then 2 * hist.length - 1 else 2 * hist.length
+      if idx % (2 * k) < k then
+        P.next x y (coinBlock (P.coinLen x.length) (idx / (2 * k)) rP)
+          (hist.drop (idx / (2 * k) * k))
+      else [])
+    (hidx : ∀ n < 2 * k * q, moverIsV vFirst n = false →
+      (if vFirst then 2 * (exec Pseq V vFirst x y z rP rV n).1.length - 1
+        else 2 * (exec Pseq V vFirst x y z rP rV n).1.length) = n)
+    (hstartP : (exec Pseq V vFirst x y z rP rV (2 * k * j)).1.length = j * k)
+    (hturn : ∀ u < k, moverIsV vFirst (2 * k * j + u) = moverIsV vFirst u)
+    {t : ℕ} (ht : t ≤ k) :
+    (exec Pseq V vFirst x y z rP rV (2 * k * j + t)).1 =
+      (exec Pseq V vFirst x y z rP rV (2 * k * j)).1 ++
+        (exec P (phaseVerifier V) vFirst x y
+          (phaseAux z rV j (exec Pseq V vFirst x y z rP rV (2 * k * j)).2)
+          (coinBlock (P.coinLen x.length) j rP) [] t).1 ∧
+    (exec Pseq V vFirst x y z rP rV (2 * k * j + t)).2 =
+      (exec Pseq V vFirst x y z rP rV (2 * k * j)).2 ++
+        (exec P (phaseVerifier V) vFirst x y
+          (phaseAux z rV j (exec Pseq V vFirst x y z rP rV (2 * k * j)).2)
+          (coinBlock (P.coinLen x.length) j rP) [] t).2 := by
+  apply exec_phase_of_moves Pseq V P (phaseVerifier V) vFirst x y z rP rV y
+    (phaseAux z rV j (exec Pseq V vFirst x y z rP rV (2 * k * j)).2)
+    (coinBlock (P.coinLen x.length) j rP) [] (2 * k * j) k hturn ?_ ?_ ht
+  · intro u hu hm
+    have hbound : 2 * k * j + 2 * k ≤ 2 * k * q := by
+      simpa only [Nat.mul_succ] using Nat.mul_le_mul_left (2 * k) (Nat.succ_le_of_lt hj)
+    have hrec := hidx (2 * k * j + u) (by omega) ((hturn u hu).trans hm)
+    have hmod : (2 * k * j + u) % (2 * k) = u := by
+      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
+    have hdiv : (2 * k * j + u) / (2 * k) = j := by
+      rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega),
+        Nat.zero_add]
+    rw [hPseq]
+    dsimp only
+    rw [hrec, hmod, if_pos hu, hdiv, hstartP]
+  · intro u _ _
+    rw [phaseVerifier_next_phaseAux]
+    apply congrArg (V.next x z rV)
+    have htake := exec_snd_take Pseq V vFirst x y z rP rV (2 * k * j) u
+    exact ((congrArg (fun h => h ++
+      (exec Pseq V vFirst x y z rP rV (2 * k * j + u)).2.drop
+        (exec Pseq V vFirst x y z rP rV (2 * k * j)).2.length) htake.symm).trans
+          (List.take_append_drop _ _)).symm
+
+/-- Under the repeated-prover shape/index/period hypotheses, suppose phase `j<q` starts
+with both received histories of length `j*k`, ends with verifier history length `(j+1)*k`,
+and the original wrapped real phase has `p` prover messages. Then its entire padded phase
+appends those real messages followed by exactly `k-p` empty messages to the verifier's
+earlier history. No condition is placed on the arbitrary verifier's filler replies.
+[PS10, Theorem 175.1; Gol01, §4.3.4, the real padded-phase endpoint].
+
+**Proof sketch.** The real phase is the original wrapped execution by `exec_real_phase`.
+During each remaining move, index recovery puts every prover reply in the filler interval,
+so the padded next-message reader returns `[]`. Apply `exec_snd_empty` to that suffix.
+The supplied start, real-phase and end lengths show that exactly `k-p` further messages
+were received. Combining the two prefix equalities gives the complete padded endpoint. -/
+theorem exec_padded_real_phase (Pseq P V : Strategy) (vFirst : Bool)
+    (x y z rP rV : List Bool) (k q j p : ℕ) (hj : j < q)
+    (hPseq : ∀ hist : List (List Bool), Pseq.next x y rP hist =
+      let idx := if vFirst then 2 * hist.length - 1 else 2 * hist.length
+      if idx % (2 * k) < k then
+        P.next x y (coinBlock (P.coinLen x.length) (idx / (2 * k)) rP)
+          (hist.drop (idx / (2 * k) * k))
+      else [])
+    (hidx : ∀ n < 2 * k * q, moverIsV vFirst n = false →
+      (if vFirst then 2 * (exec Pseq V vFirst x y z rP rV n).1.length - 1
+        else 2 * (exec Pseq V vFirst x y z rP rV n).1.length) = n)
+    (hstartP : (exec Pseq V vFirst x y z rP rV (2 * k * j)).1.length = j * k)
+    (hstartV : (exec Pseq V vFirst x y z rP rV (2 * k * j)).2.length = j * k)
+    (hendV : (exec Pseq V vFirst x y z rP rV (2 * k * (j + 1))).2.length = (j + 1) * k)
+    (hlocal : (exec P (phaseVerifier V) vFirst x y
+      (phaseAux z rV j (exec Pseq V vFirst x y z rP rV (2 * k * j)).2)
+      (coinBlock (P.coinLen x.length) j rP) [] k).2.length = p)
+    (hturn : ∀ u < k, moverIsV vFirst (2 * k * j + u) = moverIsV vFirst u) :
+    (exec Pseq V vFirst x y z rP rV (2 * k * (j + 1))).2 =
+      (exec Pseq V vFirst x y z rP rV (2 * k * j)).2 ++
+        ((exec P (phaseVerifier V) vFirst x y
+          (phaseAux z rV j (exec Pseq V vFirst x y z rP rV (2 * k * j)).2)
+          (coinBlock (P.coinLen x.length) j rP) [] k).2 ++ List.replicate (k - p) []) := by
+  have hreal := (exec_real_phase Pseq P V vFirst x y z rP rV k q j hj hPseq hidx
+    hstartP hturn (t := k) le_rfl).2
+  -- The recovered position is a filler position at every later prover move.
+  have hfill := exec_snd_empty Pseq V vFirst x y z rP rV (2 * k * j + k) k
+    (fun u hu hm => by
+      have hbound : 2 * k * j + 2 * k ≤ 2 * k * q := by
+        simpa only [Nat.mul_succ] using Nat.mul_le_mul_left (2 * k) (Nat.succ_le_of_lt hj)
+      have hrec := hidx (2 * k * j + k + u) (by omega) hm
+      have hmod : (2 * k * j + k + u) % (2 * k) = k + u := by
+        rw [show 2 * k * j + k + u = (k + u) + (2 * k) * j by ring,
+          Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
+      rw [hPseq]
+      dsimp only
+      rw [hrec, hmod, if_neg (by omega)])
+  -- Slot counts identify the empty suffix without restricting verifier filler replies.
+  have hend : (2 * k * j + k) + k = 2 * k * (j + 1) := by ring
+  rw [hend, hreal, List.length_append, hstartV, hlocal, hendV] at hfill
+  have hcount : (j + 1) * k - (j * k + p) = k - p := by
+    rw [Nat.add_mul, Nat.one_mul]
+    omega
+  rw [hcount] at hfill
+  simpa only [List.append_assoc] using hfill
+
+end TCSlib.Cryptography.SequentialZK
diff --git a/TCSlib/Cryptography/Composability/SequentialZK/RealPrefixBounds.lean b/TCSlib/Cryptography/Composability/SequentialZK/RealPrefixBounds.lean
new file mode 100644
index 000000000..9b732c32b
--- /dev/null
+++ b/TCSlib/Cryptography/Composability/SequentialZK/RealPrefixBounds.lean
@@ -0,0 +1,101 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Composability.SequentialZK.EndpointSampling
+import TCSlib.Cryptography.Composability.SequentialZK.ExecutionBounds
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Bounds for actual real phase prefixes
+
+The endpoint reader identifies a typed real-prefix fold with an execution of the padded
+prover. The construction specification then gives its exact message count, while the
+original prover's uniform message bound also bounds every padded-prover reply. Existing
+execution and word-encoding bounds finish the advice-size estimate. [PS10, Theorem 175.1].
+
+## Main definitions
+
+There are no new definitions.
+
+## Main results
+
+* `PaddedProverSpec.realPrefix_bounds`: exact count, bounded messages, and encoded-size bound.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §7.2.1, Theorem 175.1.
+* [Gol01] O. Goldreich, *Foundations of Cryptography, Volume I: Basic Tools*, Cambridge
+  University Press, 2001, §4.3.4.
+-/
+
+namespace TCSlib.Cryptography.SequentialZK.PaddedProverSpec
+
+open Complexity
+
+/-- For `d : PaddedProverSpec π ρ x q p`, verifier `V`, inputs `y,z`, tape `rV`, index
+`j≤q`, message cap `B`, uniform original-prover bound `hbound`, and independent phase coins
+`coins`, put `pre = realPrefix π V x y z rV p j coins` and `k = π.rounds.eval |x|`. Then
+`pre.length = j*k`, every `m ∈ pre` has `m.length ≤ B`, and
+`(Strategy.encodeMsgs pre).length ≤ (j*k)*(2*B+2)`.
+[PS10, Theorem 175.1; Gol01, §4.3.4, bounded real-prefix reduction advice].
+
+**Proof sketch.** The public coin-table equivalence supplies a raw tape with exactly the
+requested independent phase blocks. The real-prefix endpoint reader identifies the fold
+with the repeated execution on that tape. Its boundary reader gives exactly `j*k` received
+messages. Each repeated-prover reply is either an original bounded message or an empty
+filler, by the specification's public reply equation. The public execution-message bound
+therefore controls every received message. Finally reuse the execution encoding bound,
+which already invokes the generic public encoded-word length theorem. -/
+theorem realPrefix_bounds {π ρ : Protocol} {x : List Bool} {q p : ℕ}
+    (d : PaddedProverSpec π ρ x q p) (V : Strategy) (y z rV : List Bool)
+    (j : ℕ) (hj : j ≤ q) (B : ℕ)
+    (hbound : ∀ r hist, (π.P.next x y r hist).length ≤ B)
+    (coins : Fin j → π.P.Coins x.length) :
+    (realPrefix π V x y z rV p j coins).length = j * π.rounds.eval x.length ∧
+    (∀ m ∈ realPrefix π V x y z rV p j coins, m.length ≤ B) ∧
+    (Strategy.encodeMsgs (realPrefix π V x y z rV p j coins)).length ≤
+      (j * π.rounds.eval x.length) * (2 * B + 2) := by
+  -- Reconstruct one raw tape whose blocks are the supplied typed phase coins.
+  let e : (Fin (j * π.P.coinLen x.length) → Bool) ≃ (Fin j → π.P.Coins x.length) :=
+    coinTableEquiv rfl
+  let tape := List.ofFn (e.symm coins)
+  have hblocks (i : Fin j) :
+      coinBlock (π.P.coinLen x.length) i tape = List.ofFn (coins i) := by
+    have hblock := coinTableEquiv_block (m := j * π.P.coinLen x.length)
+      (q := j) (c := π.P.coinLen x.length) rfl (e.symm coins) i
+    have hinverse := congrArg (fun table : Fin j → π.P.Coins x.length =>
+      List.ofFn (table i)) (e.apply_symm_apply coins)
+    exact hblock.trans hinverse
+  have hend : realPrefix π V x y z rV p j coins =
+      (exec ρ.P V π.verifierFirst x y z tape rV
+        (2 * π.rounds.eval x.length * j)).2 :=
+    d.realPrefix_eq_exec V y z tape rV j hj coins hblocks
+  have hcount : (realPrefix π V x y z rV p j coins).length =
+      j * π.rounds.eval x.length := by
+    rw [hend]
+    exact (d.boundary V y z tape rV j).2
+  -- Empty fillers satisfy the same cap as the original real replies.
+  have hsource (hist : List (List Bool)) : (ρ.P.next x y tape hist).length ≤ B := by
+    rw [d.next y tape hist]
+    dsimp only
+    split_ifs <;> first | exact hbound _ _ | exact Nat.zero_le B
+  have hmessages : ∀ m ∈ realPrefix π V x y z rV p j coins, m.length ≤ B := by
+    rw [hend]
+    exact exec_snd_bounded ρ.P V π.verifierFirst x y z tape rV B
+      (2 * π.rounds.eval x.length * j) hsource
+  -- Reuse the existing execution-specific encoded-history estimate.
+  have hencoding : (Strategy.encodeMsgs (realPrefix π V x y z rV p j coins)).length ≤
+      (j * π.rounds.eval x.length) * (2 * B + 2) := by
+    rw [hend]
+    have hencoded := length_encodeMsgs_exec_snd_le ρ.P V π.verifierFirst x y z tape rV B
+      (2 * π.rounds.eval x.length * j) hsource
+    rw [(d.boundary V y z tape rV j).2] at hencoded
+    exact hencoded
+  exact ⟨hcount, hmessages, hencoding⟩
+
+end TCSlib.Cryptography.SequentialZK.PaddedProverSpec
diff --git a/TCSlib/Cryptography/Composability/SequentialZK/ReductionAdvantage.lean b/TCSlib/Cryptography/Composability/SequentialZK/ReductionAdvantage.lean
new file mode 100644
index 000000000..0c96e2d3e
--- /dev/null
+++ b/TCSlib/Cryptography/Composability/SequentialZK/ReductionAdvantage.lean
@@ -0,0 +1,111 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Composability.SequentialZK.ComputationalReduction
+import TCSlib.Cryptography.Asymptotic.EnsemblesLemmas
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Typed advantage of the one-phase reduction
+
+## Main definitions
+
+This module introduces no definitions or computational hosts.
+
+## Main results
+
+* `distAdv_phaseReduction`: the reduction's exact raw activation equation identifies its
+  advantage with the typed independent phase-table and final-distinguisher coin experiment.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  Theorem 175.1.
+-/
+
+namespace TCSlib.Cryptography.SequentialZK
+
+open Complexity
+
+/-- For fixed machines `S,D,Red`, phase polynomials `k,B,Q`, orientation `verifierFirst`,
+parameter `n`, and metadata `x,z,rV,j,pre`, suppose `Red` has coins `Q*S.coins+D.coins` and
+its raw activation normalizes the candidate, simulates the suffix, and then invokes `D`.
+For any raw-output samplers `X,Y`, its distinguishing advantage equals that of the typed
+experiment with independent coins `(Fin (Q.eval n) → S.Coins n) × D.Coins n`, flattened by
+`FunFamily.blocks.symm` for the suffix. No metadata validity or witness premise is needed.
+[PS10, Theorem 175.1, one-phase computational hybrid reduction].
+
+**Proof sketch.**
+First read the reduction's exact coin polynomial at the fixed parameter.
+Its numerical coin length is the sum of the simulator-table and distinguisher lengths.
+The canonical block equivalence flattens the independent simulator table.
+The published `coinsEquiv` then concatenates it with the distinguisher coins.
+Their composition is a bijection from the typed independent coins to `Red.Coins n`.
+The published take reader identifies the entire simulator-table tape.
+The published drop reader identifies the independent final-distinguisher tape.
+These equations require no positivity of either coin length or the number of phases.
+Read both machine distinguishers through their published verdict equations.
+Read their typed activations through the public `runAt_eq` equation.
+Apply the assumed exact raw activation equation to every candidate word and tape.
+The two tape readers identify that verdict with the claimed typed local experiment.
+Reindex acceptance probabilities along the constructed bijection for sampler `X`.
+Do the same independently for sampler `Y`.
+Finally read the absolute acceptance gap through `distAdv_def` and substitute both
+probability equalities. The sample spaces may differ and need only be finite. -/
+theorem distAdv_phaseReduction {σ τ : Type*} [Fintype σ] [Fintype τ]
+    (S D Red : NUPPT) (k B Q : PolyExpr) (verifierFirst : Bool) (n : ℕ)
+    (x z rV : List Bool) (j : ℕ) (pre : List (List Bool))
+    (hcoins : Red.coins = .add (.mul Q S.coins) D.coins)
+    (hrun : ∀ raw r, Red.runAtL n raw r = D.runAtL n
+      (phaseContinuation S k B Q verifierFirst x z rV j pre raw
+        (r.take ((PolyExpr.mul Q S.coins).eval n)))
+      (r.drop ((PolyExpr.mul Q S.coins).eval n)))
+    (X : σ → List Bool) (Y : τ → List Bool) :
+    distAdv X Y (Red.distinguisherL n) =
+      distAdv X Y (fun raw (c : (Fin (Q.eval n) → S.Coins n) × D.Coins n) =>
+        D.distinguisherL n
+          (phaseContinuation S k B Q verifierFirst x z rV j pre raw
+            (List.ofFn ((FunFamily.blocks (Q.eval n) (S.coinLen n)).symm c.1))) c.2) := by
+  -- The published coin readers identify the canonical independent product space.
+  have hlen : Red.coinLen n = Q.eval n * S.coinLen n + D.coinLen n := by
+    rw [NUPPT.coinLen_eq, hcoins, PolyExpr.eval_add, PolyExpr.eval_mul,
+      NUPPT.coinLen_eq, NUPPT.coinLen_eq]
+  let e : ((Fin (Q.eval n) → S.Coins n) × D.Coins n) ≃ Red.Coins n :=
+    ((FunFamily.blocks (Q.eval n) (S.coinLen n)).symm.prodCongr
+      (Equiv.refl (D.Coins n))).trans (EnsembleLemmas.coinsEquiv hlen)
+  -- Expand the local equivalence before evaluating the scalar coin cut.
+  have he (c : (Fin (Q.eval n) → S.Coins n) × D.Coins n) :
+      e c = EnsembleLemmas.coinsEquiv hlen
+        (((FunFamily.blocks (Q.eval n) (S.coinLen n)).symm c.1), c.2) := by
+    rcases c with ⟨cS, cD⟩
+    simp only [e, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply]
+  have hcut : (PolyExpr.mul Q S.coins).eval n = Q.eval n * S.coinLen n := by
+    rw [PolyExpr.eval_mul, NUPPT.coinLen_eq]
+  have htake (c : (Fin (Q.eval n) → S.Coins n) × D.Coins n) :
+      (List.ofFn (e c)).take ((PolyExpr.mul Q S.coins).eval n) =
+        List.ofFn ((FunFamily.blocks (Q.eval n) (S.coinLen n)).symm c.1) := by
+    rw [he, hcut]
+    exact EnsembleLemmas.take_ofFn_coinsEquiv hlen
+      (((FunFamily.blocks (Q.eval n) (S.coinLen n)).symm c.1), c.2)
+  have hdrop (c : (Fin (Q.eval n) → S.Coins n) × D.Coins n) :
+      (List.ofFn (e c)).drop ((PolyExpr.mul Q S.coins).eval n) = List.ofFn c.2 := by
+    rw [he, hcut]
+    exact EnsembleLemmas.drop_ofFn_coinsEquiv hlen
+      (((FunFamily.blocks (Q.eval n) (S.coinLen n)).symm c.1), c.2)
+  -- Compare the exact verdicts, then reindex each acceptance probability.
+  have key (raw : List Bool) (c : (Fin (Q.eval n) → S.Coins n) × D.Coins n) :
+      Red.distinguisherL n raw (e c) = D.distinguisherL n
+        (phaseContinuation S k B Q verifierFirst x z rV j pre raw
+          (List.ofFn ((FunFamily.blocks (Q.eval n) (S.coinLen n)).symm c.1))) c.2 := by
+    rw [NUPPT.distinguisherL_eq, NUPPT.distinguisherL_eq, NUPPT.runAt_eq,
+      NUPPT.runAt_eq, hrun, htake, hdrop]
+  have hX := EnsembleLemmas.acceptProb_coins_equiv e X (Red.distinguisherL n)
+  have hY := EnsembleLemmas.acceptProb_coins_equiv e Y (Red.distinguisherL n)
+  simp only [key] at hX hY
+  rw [distAdv_def, distAdv_def, ← hX, ← hY]
+
+end TCSlib.Cryptography.SequentialZK
diff --git a/TCSlib/Cryptography/Composability/SequentialZK/RepeatedSoundness.lean b/TCSlib/Cryptography/Composability/SequentialZK/RepeatedSoundness.lean
new file mode 100644
index 000000000..82eceaccf
--- /dev/null
+++ b/TCSlib/Cryptography/Composability/SequentialZK/RepeatedSoundness.lean
@@ -0,0 +1,218 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Composability.SequentialZK.RepeatedVerifier
+import TCSlib.Cryptography.Composability.SequentialZK.ErrSoundness
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Explicit soundness error under abstract sequential repetition
+
+## Main definitions
+
+Private tape and phase-test functions express conditioning on earlier verifier blocks.
+
+## Main results
+
+* `Composability.PaddedVerifierSpec.outV_eq`: the repeated output is its terminal verdict.
+* `Composability.PaddedVerifierSpec.accept_le`: aggregate acceptance is at most `s(|x|)^q`.
+* `Composability.PaddedVerifierSpec.sound`: aggregate rejection is at least `1-s(|x|)^q`.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  Theorem 175.1 (sequential repetition).
+-/
+
+namespace TCSlib.Cryptography.Composability
+
+/-- `phaseTape q c F` is the string of the `q` consecutive `c`-bit blocks of `F`. -/
+private def phaseTape (q c : ℕ) (F : Fin q → Fin c → Bool) : List Bool :=
+  List.ofFn ((FunFamily.blocks q c).symm F)
+
+/-- Block `i` of `phaseTape q c F` is `List.ofFn (F i)`. -/
+private theorem phaseTape_block (q c : ℕ) (F : Fin q → Fin c → Bool) (i : Fin q) :
+    coinBlock c i (phaseTape q c F) = List.ofFn (F i) := by
+  have he := FunFamily.ofFn_blocks q c ((FunFamily.blocks q c).symm F) i
+  rw [Equiv.apply_symm_apply] at he
+  exact (coinBlock_eq c i (phaseTape q c F)).trans he.symm
+
+/-- `zeroTail q c i pre` has block `pre j` below `i` and the all-false block afterwards. -/
+private def zeroTail (q c i : ℕ) (pre : Fin i → Fin c → Bool) : Fin q → Fin c → Bool :=
+  fun j => if h : (j : ℕ) < i then pre ⟨j, h⟩ else fun _ => false
+
+/-- `phaseGood π ρ P x z rP q i pre fresh` is acceptance of `π.V` on `fresh` against the
+prover whose tape is `rP` and whose earlier received messages come from `ρ` on the tape
+formed from `pre` and an all-false suffix. -/
+private def phaseGood (π ρ : Protocol) (P : Strategy) (x z rP : List Bool) (q i : ℕ)
+    (pre : Fin i → π.V.Coins x.length) (fresh : π.V.Coins x.length) : Prop :=
+  π.V.next x z (List.ofFn fresh)
+    (exec (prefixProver P [] rP
+      (exec P ρ.V π.verifierFirst x [] z rP
+        (phaseTape q (π.V.coinLen x.length) (zeroTail q (π.V.coinLen x.length) i pre))
+        (2 * π.rounds.eval x.length * i)).1)
+      π.V π.verifierFirst x [] z [] (List.ofFn fresh) (π.rounds.eval x.length)).2 = [true]
+
+/-- Each fixed-prefix phase test has acceptance at most the original soundness error. -/
+private theorem phaseGood_section {π ρ : Protocol} {L : Language Bool} {s : ℕ → ℝ}
+    (h : InteractiveProofErr π L s) (x : List Bool) (hx : x ∉ L) (P : Strategy)
+    (z rP : List Bool) (q i : ℕ) (pre : Fin i → π.V.Coins x.length) :
+    uprob (phaseGood π ρ P x z rP q i pre) ≤ s x.length :=
+  prefixProver_accept_le h x hx P [] rP
+    (exec P ρ.V π.verifierFirst x [] z rP
+      (phaseTape q (π.V.coinLen x.length) (zeroTail q (π.V.coinLen x.length) i pre))
+      (2 * π.rounds.eval x.length * i)).1 z
+
+/-- An accepting aggregate phase test is the corresponding conditional `phaseGood` test.
+
+**Proof sketch.** Replace every block at and after the phase by zeros. The verifier-prefix
+reader shows this leaves the earlier transcript fixed. The phase-history reader then
+identifies the aggregate test with the original verifier against the induced fixed-prefix
+prover. Reading the actual phase block supplies the fresh local verifier tape. -/
+private theorem phaseGood_of_test {π ρ : Protocol} {x : List Bool} {q p : ℕ}
+    {terminal : List Bool → List Bool → List (List Bool) → List Bool}
+    (d : PaddedVerifierSpec π ρ x q p terminal) (P : Strategy) (z rP : List Bool)
+    (F : Fin q → π.V.Coins x.length) (i : Fin q)
+    (htest : π.V.next x z
+      (coinBlock (π.V.coinLen x.length) i (phaseTape q (π.V.coinLen x.length) F))
+      (((exec P ρ.V π.verifierFirst x [] z rP (phaseTape q (π.V.coinLen x.length) F)
+        (2 * π.rounds.eval x.length * q)).2.drop (i * π.rounds.eval x.length)).take p) =
+        [true]) :
+    phaseGood π ρ P x z rP q i (fun j => F (Fin.castLE i.isLt.le j)) (F i) := by
+  let c := π.V.coinLen x.length
+  let k := π.rounds.eval x.length
+  let pre : Fin i → π.V.Coins x.length := fun j => F (Fin.castLE i.isLt.le j)
+  let F0 : Fin q → π.V.Coins x.length := zeroTail q c i pre
+  have hblocks : ∀ l < (i : ℕ), coinBlock c l (phaseTape q c F) =
+      coinBlock c l (phaseTape q c F0) := by
+    intro l hl
+    have hlq : l < q := lt_trans hl i.isLt
+    rw [phaseTape_block q c F ⟨l, hlq⟩, phaseTape_block q c F0 ⟨l, hlq⟩]
+    apply congrArg List.ofFn
+    funext b
+    change F ⟨l, hlq⟩ b =
+      (if h : l < (i : ℕ) then pre ⟨l, h⟩ else fun _ => false) b
+    rw [dif_pos hl]
+    rfl
+  -- Earlier received histories ignore every block at or beyond the current phase.
+  have he := exec_eq_of_verifier_blocks P ρ.V π.V π.verifierFirst x [] z rP
+    (phaseTape q c F) (phaseTape q c F0) k q c i (terminal z)
+    (d.next_eq z) i.isLt
+    (fun t _ hm => d.index_eq P [] z rP (phaseTape q c F) t hm) hblocks
+  have hprior := congrArg Prod.fst he
+  -- Read the real phase and its fresh block from the original full table.
+  rw [d.phase_take P [] z rP (phaseTape q c F) i i.isLt] at htest
+  change π.V.next x z (coinBlock c i (phaseTape q c F))
+    (exec (prefixProver P [] rP
+      (exec P ρ.V π.verifierFirst x [] z rP (phaseTape q c F) (2 * k * i)).1)
+      π.V π.verifierFirst x [] z [] (coinBlock c i (phaseTape q c F)) k).2 = [true] at htest
+  simp only [phaseTape_block q c F i] at htest
+  change π.V.next x z (List.ofFn (F i))
+    (exec (prefixProver P [] rP
+      (exec P ρ.V π.verifierFirst x [] z rP (phaseTape q c F0) (2 * k * i)).1)
+      π.V π.verifierFirst x [] z [] (List.ofFn (F i)) k).2 = [true]
+  rw [← hprior]
+  exact htest
+
+/-- For specification `d`, prover `P`, auxiliary inputs `y`, `z`, and joint coins `r`,
+`ρ.outV P x y z r` equals `terminal z (List.ofFn r.2) hist`, where `hist` is the verifier
+component of `exec P ρ.V π.verifierFirst x y z (List.ofFn r.1) (List.ofFn r.2) (2*k*q)`
+and `k=π.rounds.eval |x|`. [PS10, Theorem 175.1, the aggregate verdict]. -/
+theorem PaddedVerifierSpec.outV_eq {π ρ : Protocol} {x : List Bool} {q p : ℕ}
+    {terminal : List Bool → List Bool → List (List Bool) → List Bool}
+    (d : PaddedVerifierSpec π ρ x q p terminal) (P : Strategy) (y z : List Bool)
+    (r : ρ.ExecCoins P x) :
+    ρ.outV P x y z r = terminal z (List.ofFn r.2)
+      (exec P ρ.V π.verifierFirst x y z (List.ofFn r.1) (List.ofFn r.2)
+        (2 * π.rounds.eval x.length * q)).2 := by
+  rw [Protocol.outV_eq, Protocol.transcriptWith_eq, d.rounds_eq, d.first_eq]
+  rw [d.next_eq, if_pos (d.boundary_lengths P y z (List.ofFn r.1)
+    (List.ofFn r.2) q le_rfl).2]
+
+/-- For specification `d : PaddedVerifierSpec π ρ x q p terminal`, original soundness
+`h : InteractiveProofErr π L s`, a no-instance `x ∉ L`, prover `P`, and verifier auxiliary
+input `z`, `Pr[ρ.outV P x [] z = [true]] ≤ s |x| ^ q`.
+[PS10, Theorem 175.1, multiplication of sequential soundness error].
+
+**Proof sketch.** Zero phases give the bound one. Otherwise fix prover coins maximizing
+acceptance and read the verifier tape as independent original coin blocks. Define the
+phase test by fixing the earlier coin blocks and replacing future blocks by zeros. Earlier
+transcripts are unaffected by that replacement, so every aggregate phase test is this
+conditional test on the current fresh block. Each section accepts with probability at
+most the original error. The adaptive product theorem bounds all phase tests by its
+`q`-th power; averaging over the fixed prover coins only decreases acceptance. -/
+theorem PaddedVerifierSpec.accept_le {π ρ : Protocol} {x : List Bool} {q p : ℕ}
+    {terminal : List Bool → List Bool → List (List Bool) → List Bool}
+    (d : PaddedVerifierSpec π ρ x q p terminal) {L : Language Bool} {s : ℕ → ℝ}
+    (h : InteractiveProofErr π L s) (hx : x ∉ L) (P : Strategy) (z : List Bool) :
+    uprob (fun r : ρ.ExecCoins P x => ρ.outV P x [] z r = [true]) ≤ s x.length ^ q := by
+  by_cases hq : q = 0
+  · subst q
+    simpa only [pow_zero] using
+      (uprob_le_one (fun r : ρ.ExecCoins P x => ρ.outV P x [] z r = [true]))
+  · -- Fix a prover tape at least as successful as its uniform average.
+    obtain ⟨rP, hrP⟩ := ρ.exists_proverCoins_le P x [] z (fun out => out = [true])
+    refine hrP.trans ?_
+    let c := π.V.coinLen x.length
+    let e : (Fin q → π.V.Coins x.length) ≃ ρ.V.Coins x.length :=
+      (FunFamily.blocks q c).symm.trans
+        (Equiv.arrowCongr (finCongr d.coinLen_eq.symm) (Equiv.refl Bool))
+    have htape (F : Fin q → π.V.Coins x.length) :
+        List.ofFn (e F) = phaseTape q c F :=
+      ofFn_arrowCongr_finCongr d.coinLen_eq.symm ((FunFamily.blocks q c).symm F)
+    -- On every full table, aggregate acceptance implies all fixed-prefix phase tests.
+    have hmono :
+        uprob (fun F : Fin q → π.V.Coins x.length =>
+          ρ.outV P x [] z (rP, e F) = [true]) ≤
+        uprob (fun F : Fin q → π.V.Coins x.length => ∀ i : Fin q,
+          phaseGood π ρ P x z (List.ofFn rP) q i
+            (fun j => F (Fin.castLE i.isLt.le j)) (F i)) := by
+      apply uprob_mono
+      intro F hacc i
+      rw [d.outV_eq, htape F, d.terminal_eq] at hacc
+      split_ifs at hacc with hall
+      · have hitest := List.all_eq_true.mp hall i (List.mem_range.mpr i.isLt)
+        exact phaseGood_of_test d P z (List.ofFn rP) F i (of_decide_eq_true hitest)
+      · cases hacc
+    -- Apply the section bound on every earlier prefix, then the adaptive product bound.
+    have hadapt :
+        uprob (fun F : Fin q → π.V.Coins x.length => ∀ i : Fin q,
+          phaseGood π ρ P x z (List.ofFn rP) q i
+            (fun j => F (Fin.castLE i.isLt.le j)) (F i)) ≤ s x.length ^ q :=
+      uprob_adaptive_all_le q (s x.length) (h.sound_nonneg x hx)
+        (fun i => phaseGood π ρ P x z (List.ofFn rP) q i)
+        (fun i _ pre => phaseGood_section h x hx P z (List.ofFn rP) q i pre)
+    have htable := hmono.trans hadapt
+    rw [uprob_comp_equiv e (fun rV => ρ.outV P x [] z (rP, rV) = [true])] at htable
+    exact htable
+
+/-- For specification `d : PaddedVerifierSpec π ρ x q p terminal`, original soundness
+`h : InteractiveProofErr π L s`, a no-instance `x ∉ L`, prover `P`, and verifier auxiliary
+input `z`, `1-s |x| ^ q ≤ Pr[ρ.outV P x [] z = [false]]`.
+[PS10, Theorem 175.1, sequential soundness error `s^q`].
+
+**Proof sketch.** Zero phases require only nonnegativity of a probability. Otherwise the
+aggregate verdict is binary, so rejection is exactly the complement of acceptance.
+Subtract the acceptance upper bound from one. -/
+theorem PaddedVerifierSpec.sound {π ρ : Protocol} {x : List Bool} {q p : ℕ}
+    {terminal : List Bool → List Bool → List (List Bool) → List Bool}
+    (d : PaddedVerifierSpec π ρ x q p terminal) {L : Language Bool} {s : ℕ → ℝ}
+    (h : InteractiveProofErr π L s) (hx : x ∉ L) (P : Strategy) (z : List Bool) :
+    1 - s x.length ^ q ≤
+      uprob (fun r : ρ.ExecCoins P x => ρ.outV P x [] z r = [false]) := by
+  by_cases hq : q = 0
+  · subst q
+    simpa only [pow_zero, sub_self] using
+      (uprob_nonneg (fun r : ρ.ExecCoins P x => ρ.outV P x [] z r = [false]))
+  · have hiff (r : ρ.ExecCoins P x) :
+        ρ.outV P x [] z r = [false] ↔ ¬ ρ.outV P x [] z r = [true] := by
+      rw [d.outV_eq, d.terminal_eq]
+      split_ifs <;> decide
+    rw [OneWay.uprob_congr hiff, uprob_not]
+    exact sub_le_sub_left (d.accept_le h hx P z) 1
+
+end TCSlib.Cryptography.Composability
diff --git a/TCSlib/Cryptography/Composability/SequentialZK/RepeatedVerifier.lean b/TCSlib/Cryptography/Composability/SequentialZK/RepeatedVerifier.lean
new file mode 100644
index 000000000..cbce72f94
--- /dev/null
+++ b/TCSlib/Cryptography/Composability/SequentialZK/RepeatedVerifier.lean
@@ -0,0 +1,196 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Composability.SequentialZK.Phases
+import TCSlib.Cryptography.Composability.SequentialZK.VerifierPrefix
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Abstract padded verifiers and their real phases
+
+## Main definitions
+
+* `Composability.PaddedVerifierSpec`: the published equations and position readers needed
+  to compare an abstract repeated verifier with its original verifier.
+
+## Main results
+
+* `Composability.PaddedVerifierSpec.phase_exec`: each real phase against any prover is
+  an original-verifier execution with the earlier received history hardwired.
+* `Composability.PaddedVerifierSpec.phase_take`: each final aggregate phase history is
+  that original verifier history.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  Theorem 175.1 (sequential repetition).
+-/
+
+namespace TCSlib.Cryptography.Composability
+
+/-- For original protocol `π`, abstract repeated protocol `ρ`, common input `x`, phase count
+`q`, real prover-message count `p`, and terminal reply function `terminal z r hist`,
+`PaddedVerifierSpec π ρ x q p terminal` collects the coin, move, reply, verdict, and history
+length equations displayed below. Here a real phase has `π.rounds.eval |x|` moves and is
+padded to twice that length. [PS10, Theorem 175.1].
+Its first three fields state `ρ.V.coinLen x.length = q * π.V.coinLen x.length`, `ρ.rounds.eval
+x.length = 2 * π.rounds.eval x.length * q` and `ρ.verifierFirst = π.verifierFirst`. -/
+structure PaddedVerifierSpec (π ρ : Protocol) (x : List Bool) (q p : ℕ)
+    (terminal : List Bool → List Bool → List (List Bool) → List Bool) : Prop where
+  /-- The verifier coin length is `ρ.V.coinLen |x| = q * π.V.coinLen |x|`. -/
+  coinLen_eq : ρ.V.coinLen x.length = q * π.V.coinLen x.length
+  /-- The repeated move count is `ρ.rounds.eval |x| = 2 * π.rounds.eval |x| * q`. -/
+  rounds_eq : ρ.rounds.eval x.length = 2 * π.rounds.eval x.length * q
+  /-- The first-mover flag is `ρ.verifierFirst = π.verifierFirst`. -/
+  first_eq : ρ.verifierFirst = π.verifierFirst
+  /-- For `z`, `r`, `hist`, `ρ.V.next x z r hist` is `terminal z r hist` at history length
+  `q*k`; otherwise its real-phase reply is `π.V.next` on block `idx/(2*k)` and the suffix
+  after `(idx/(2*k))*k` received slots, and its filler reply is `[]`, with `k=π.rounds |x|`
+  and `idx=if π.verifierFirst then 2*|hist| else 2*|hist|-1`. -/
+  next_eq (z r : List Bool) (hist : List (List Bool)) :
+    ρ.V.next x z r hist =
+      if hist.length = q * π.rounds.eval x.length then terminal z r hist
+      else
+        let idx := if π.verifierFirst then 2 * hist.length else 2 * hist.length - 1
+        if idx % (2 * π.rounds.eval x.length) < π.rounds.eval x.length then
+          π.V.next x z (coinBlock (π.V.coinLen x.length)
+            (idx / (2 * π.rounds.eval x.length)) r)
+            (hist.drop (idx / (2 * π.rounds.eval x.length) * π.rounds.eval x.length))
+        else []
+  /-- For `z`, `r`, `hist`, `terminal z r hist = [true]` exactly when each phase `j<q`
+  satisfies `π.V.next x z (coinBlock c j r) ((hist.drop (j*k)).take p)=[true]`;
+  the other terminal output is `[false]`, with `k=π.rounds |x|`, `c=π.V.coinLen |x|`. -/
+  terminal_eq (z r : List Bool) (hist : List (List Bool)) :
+    terminal z r hist =
+      if (List.range q).all (fun j => decide
+        (π.V.next x z (coinBlock (π.V.coinLen x.length) j r)
+          ((hist.drop (j * π.rounds.eval x.length)).take p) = [true]))
+      then [true] else [false]
+  /-- For `P`, `y`, `z`, `rP`, `rV`, and a verifier move `t`, the index computed from its
+  source received-history length is `t`: `if π.verifierFirst then 2*|hist| else 2*|hist|-1=t`.
+  Here `hist=(exec P ρ.V π.verifierFirst x y z rP rV t).2`. -/
+  index_eq (P : Strategy) (y z rP rV : List Bool) (t : ℕ)
+      (hm : moverIsV π.verifierFirst t = true) :
+    (if π.verifierFirst then 2 * (exec P ρ.V π.verifierFirst x y z rP rV t).2.length
+      else 2 * (exec P ρ.V π.verifierFirst x y z rP rV t).2.length - 1) = t
+  /-- For `P`, `y`, `z`, `rP`, `rV`, `j≤q`, both histories after `2*k*j` moves have
+  length `j*k`, where `k=π.rounds.eval |x|`. -/
+  boundary_lengths (P : Strategy) (y z rP rV : List Bool) (j : ℕ) (hj : j ≤ q) :
+    (exec P ρ.V π.verifierFirst x y z rP rV (2 * π.rounds.eval x.length * j)).1.length =
+        j * π.rounds.eval x.length ∧
+      (exec P ρ.V π.verifierFirst x y z rP rV (2 * π.rounds.eval x.length * j)).2.length =
+        j * π.rounds.eval x.length
+  /-- For `P`, `y`, `z`, `rP`, `rV`, the original verifier receives `p` messages:
+  `(exec P π.V π.verifierFirst x y z rP rV (π.rounds.eval |x|)).2.length=p`. -/
+  local_length (P : Strategy) (y z rP rV : List Bool) :
+    (exec P π.V π.verifierFirst x y z rP rV (π.rounds.eval x.length)).2.length = p
+  /-- For `j`, `t`, `moverIsV π.verifierFirst (2*k*j+t)=moverIsV π.verifierFirst t`,
+  where `k=π.rounds.eval |x|`. -/
+  period (j t : ℕ) :
+    moverIsV π.verifierFirst (2 * π.rounds.eval x.length * j + t) =
+      moverIsV π.verifierFirst t
+
+/-- For a padded-verifier specification `d`, prover `P`, inputs `y`, `z`, tapes `rP`, `rV`,
+phase `j<q`, and local move count `t≤k`, both source histories after `2*k*j+t` equal their
+histories after `2*k*j` followed by the corresponding original-verifier histories against
+`prefixProver P y rP priorP` on verifier block `j`. Here `k=π.rounds.eval |x|` and `priorP`
+is the source prover-received history after `2*k*j`. [PS10, Theorem 175.1].
+
+**Proof sketch.** Apply the generic fixed-prefix phase theorem. At a verifier move of the
+real phase, its recovered index is `2*k*j+t`; this excludes the terminal-history branch.
+Its quotient and residue modulo `2*k` are `j` and `t`, so the padded reply is the original
+verifier's reply on coin block `j`. The boundary reader identifies the dropped prefix
+length as `j*k`. The generic theorem supplies both transcript decompositions, including
+zero-round phases through its empty local execution. -/
+theorem PaddedVerifierSpec.phase_exec {π ρ : Protocol} {x : List Bool} {q p : ℕ}
+    {terminal : List Bool → List Bool → List (List Bool) → List Bool}
+    (d : PaddedVerifierSpec π ρ x q p terminal) (P : Strategy)
+    (y z rP rV : List Bool) (j : ℕ) (hj : j < q) {t : ℕ}
+    (ht : t ≤ π.rounds.eval x.length) :
+    (exec P ρ.V π.verifierFirst x y z rP rV
+      (2 * π.rounds.eval x.length * j + t)).1 =
+        (exec P ρ.V π.verifierFirst x y z rP rV
+          (2 * π.rounds.eval x.length * j)).1 ++
+          (exec (prefixProver P y rP (exec P ρ.V π.verifierFirst x y z rP rV
+            (2 * π.rounds.eval x.length * j)).1) π.V π.verifierFirst x [] z []
+              (coinBlock (π.V.coinLen x.length) j rV) t).1 ∧
+      (exec P ρ.V π.verifierFirst x y z rP rV
+        (2 * π.rounds.eval x.length * j + t)).2 =
+        (exec P ρ.V π.verifierFirst x y z rP rV
+          (2 * π.rounds.eval x.length * j)).2 ++
+          (exec (prefixProver P y rP (exec P ρ.V π.verifierFirst x y z rP rV
+            (2 * π.rounds.eval x.length * j)).1) π.V π.verifierFirst x [] z []
+              (coinBlock (π.V.coinLen x.length) j rV) t).2 := by
+  let k := π.rounds.eval x.length
+  have hb := (d.boundary_lengths P y z rP rV j hj.le).2
+  apply exec_phase P ρ.V π.V π.verifierFirst x y z rP rV
+    (coinBlock (π.V.coinLen x.length) j rV) (2 * k * j) k
+    (fun t _ => d.period j t) ?_ ht
+  intro t ht hm
+  have hmv : moverIsV π.verifierFirst (2 * k * j + t) = true := by
+    rw [d.period j t]
+    exact hm
+  have hi := d.index_eq P y z rP rV (2 * k * j + t) hmv
+  -- The terminal branch cannot occur at a real move of phase j.
+  have hlen : 2 * (exec P ρ.V π.verifierFirst x y z rP rV
+      (2 * k * j + t)).2.length ≤ 2 * k * j + t + 1 := by
+    by_cases hv : π.verifierFirst = true
+    · rw [if_pos hv] at hi
+      omega
+    · rw [if_neg hv] at hi
+      omega
+  have hne : (exec P ρ.V π.verifierFirst x y z rP rV
+      (2 * k * j + t)).2.length ≠ q * k := by
+    intro heq
+    rw [heq] at hlen
+    have hjk := Nat.mul_le_mul_right k hj
+    nlinarith
+  have hmod : (2 * k * j + t) % (2 * k) = t := by
+    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
+  have hdiv : (2 * k * j + t) / (2 * k) = j := by
+    rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega),
+      Nat.zero_add]
+  -- Read the real reply and the fixed old verifier-history length.
+  rw [d.next_eq, if_neg hne]
+  dsimp only
+  rw [hi, hmod, if_pos ht, hdiv, hb]
+
+/-- For specification `d`, prover `P`, inputs `y`, `z`, tapes `rP`, `rV`, and `j<q`,
+the final verifier history restricted to `(drop (j*k)).take p` is the original verifier's
+history against the prefix-hardwired prover on block `j`, where `k=π.rounds.eval |x|`.
+[PS10, Theorem 175.1, the phase test in the aggregate verdict].
+
+**Proof sketch.** A zero-round phase has empty histories on both sides. Otherwise the
+real-phase coupling identifies its ending history with the old `j*k` messages followed
+by the original verifier's `p` received messages. This ending history is a prefix of the
+final transcript. Take that prefix, then drop its old messages, to recover the original
+verifier history used by the aggregate phase test. -/
+theorem PaddedVerifierSpec.phase_take {π ρ : Protocol} {x : List Bool} {q p : ℕ}
+    {terminal : List Bool → List Bool → List (List Bool) → List Bool}
+    (d : PaddedVerifierSpec π ρ x q p terminal) (P : Strategy)
+    (y z rP rV : List Bool) (j : ℕ) (hj : j < q) :
+    ((exec P ρ.V π.verifierFirst x y z rP rV
+      (2 * π.rounds.eval x.length * q)).2.drop (j * π.rounds.eval x.length)).take p =
+      (exec (prefixProver P y rP (exec P ρ.V π.verifierFirst x y z rP rV
+        (2 * π.rounds.eval x.length * j)).1) π.V π.verifierFirst x [] z []
+          (coinBlock (π.V.coinLen x.length) j rV) (π.rounds.eval x.length)).2 := by
+  by_cases hk0 : π.rounds.eval x.length = 0
+  · simp only [hk0, Nat.mul_zero, Nat.zero_mul, exec_zero, List.drop_nil, List.take_nil]
+  · let k := π.rounds.eval x.length
+    have hb := (d.boundary_lengths P y z rP rV j hj.le).2
+    have hphase := (d.phase_exec P y z rP rV j hj (t := k) le_rfl).2
+    have hl : (exec P ρ.V π.verifierFirst x y z rP rV (2 * k * j + k)).2.length =
+        j * k + p := by
+      rw [hphase, List.length_append, hb, d.local_length]
+    have hjk := Nat.mul_le_mul_right k hj
+    have hle : 2 * k * j + k ≤ 2 * k * q := by nlinarith
+    have hp := exec_snd_take P ρ.V π.verifierFirst x y z rP rV
+      (2 * k * j + k) (2 * k * q - (2 * k * j + k))
+    rw [Nat.add_sub_of_le hle, hl] at hp
+    rw [List.take_drop, hp, hphase, ← hb, List.drop_left]
+
+end TCSlib.Cryptography.Composability
diff --git a/TCSlib/Cryptography/Composability/SequentialZK/SimulatorMachine.lean b/TCSlib/Cryptography/Composability/SequentialZK/SimulatorMachine.lean
new file mode 100644
index 000000000..c36b622a9
--- /dev/null
+++ b/TCSlib/Cryptography/Composability/SequentialZK/SimulatorMachine.lean
@@ -0,0 +1,365 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Composability.SequentialZK.PhaseView
+import TCSlib.Cryptography.Composability.SequentialZK.WrappedVerifier
+import TCSlib.Cryptography.ZeroKnowledge.Defs
+import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.EfficiencyRep
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# The strict polynomial-time sequential phase simulator
+
+A single verifier tape and independent blocks of the phase simulator's tape drive a sequence
+of canonical bounded phase normalizations. The semantic recursion `phasePrefix` specifies
+that sequence. Its machine implementation instantiates the published counted-loop host
+`ColMachines.polyTimeComputable_loopState'`; it introduces no new control host or machine.
+
+## Main definitions
+
+* `phasePrefix`: the normalized received-prover prefix after a specified number of phases.
+
+## Main results
+
+* `phasePrefix_eq`, `phasePrefix_zero`, `phasePrefix_succ`: exact semantic readers.
+* `length_phasePrefix`, `length_le_of_mem_phasePrefix`, `length_encodeMsgs_phasePrefix_le`:
+  exact slot count and uniform message/encoding bounds.
+* `phasePrefix_poly`: polynomial-time assembly of the entire normalized prefix.
+* `exists_phaseSimulator`: a uniform simulator with one verifier tape and fresh phase tapes.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §7.2.1, Theorem 175.1.
+* [Gol01] O. Goldreich, *Foundations of Cryptography, Volume I: Basic Tools*, Cambridge
+  University Press, 2001, §4.3.4.
+-/
+
+namespace TCSlib.Cryptography.SequentialZK
+
+open Complexity Turing
+
+/-- The normalized prefix after `i` phases uses simulator `S`, round/bit bounds `k,B`,
+orientation `verifierFirst`, input/auxiliary words `x,z`, one verifier tape `rV`, and phase-tape
+source `rS`. Each phase calls `S` on `phaseAux z rV i pre`, retains exactly
+`p = if verifierFirst then k(|x|)/2 else (k(|x|)+1)/2` bounded real messages, and appends
+`k(|x|)-p` empty fillers. [PS10, Theorem 175.1, the sequential simulator].
+
+This recursion is the public mathematical specification; its polynomial-time realization
+below is an instance of the existing counted-loop host, rather than a new control host. -/
+def phasePrefix (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
+    (x z rV rS : List Bool) : ℕ → List (List Bool)
+  | 0 => []
+  | i + 1 =>
+    let pre := phasePrefix S k B verifierFirst x z rV rS i
+    let aux := phaseAux z rV i pre
+    let p := if verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2
+    pre ++ (normalizePhaseMsgs x aux p (B.eval x.length)
+      (S.runAtL x.length (pairEncode x aux) (coinBlock (S.coinLen x.length) i rS)) ++
+        List.replicate (k.eval x.length - p) [])
+
+/-- Before any phase, `phasePrefix S k B verifierFirst x z rV rS 0 = []`. -/
+theorem phasePrefix_zero (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
+    (x z rV rS : List Bool) : phasePrefix S k B verifierFirst x z rV rS 0 = [] := rfl
+
+/-- Phase `i+1` extends `pre = phasePrefix S k B verifierFirst x z rV rS i` with the normalized
+output of `S.runAtL |x| (pairEncode x (phaseAux z rV i pre))` on coin block `i`, then the
+`k(|x|)-p` empty fillers, for `p = if verifierFirst then k(|x|)/2 else (k(|x|)+1)/2`. -/
+theorem phasePrefix_succ (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
+    (x z rV rS : List Bool) (i : ℕ) :
+    phasePrefix S k B verifierFirst x z rV rS (i + 1) =
+      let pre := phasePrefix S k B verifierFirst x z rV rS i
+      let aux := phaseAux z rV i pre
+      let p := if verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2
+      pre ++ (normalizePhaseMsgs x aux p (B.eval x.length)
+        (S.runAtL x.length (pairEncode x aux) (coinBlock (S.coinLen x.length) i rS)) ++
+          List.replicate (k.eval x.length - p) []) := rfl
+
+/-- The exhaustive equation for `phasePrefix … i` is `[]` at zero; at `j+1`, with
+`pre = phasePrefix … j`, it appends the canonical normalized `S.runAtL` output at
+`phaseAux z rV j pre` on coin block `j`, followed by the `k(|x|)-p` empty fillers. -/
+theorem phasePrefix_eq (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
+    (x z rV rS : List Bool) (i : ℕ) :
+    phasePrefix S k B verifierFirst x z rV rS i =
+      match i with
+      | 0 => []
+      | j + 1 =>
+        let pre := phasePrefix S k B verifierFirst x z rV rS j
+        let aux := phaseAux z rV j pre
+        let p := if verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2
+        pre ++ (normalizePhaseMsgs x aux p (B.eval x.length)
+          (S.runAtL x.length (pairEncode x aux) (coinBlock (S.coinLen x.length) j rS)) ++
+            List.replicate (k.eval x.length - p) []) :=
+  match i with
+  | 0 => phasePrefix_zero S k B verifierFirst x z rV rS
+  | j + 1 => phasePrefix_succ S k B verifierFirst x z rV rS j
+
+/-- If phase coin block `i` equals `List.ofFn r`, phase `i+1` calls precisely
+`S.simulate x (phaseAux z rV i pre) r`, with `pre` the earlier phase prefix.
+`phasePrefix S k B verifierFirst x z rV rS (i + 1) = let pre := phasePrefix S k B verifierFirst x z
+rV rS i; let aux := phaseAux z rV i pre; let p := if verifierFirst then k.eval x.length / 2 else
+(k.eval x.length + 1) / 2; pre ++ (normalizePhaseMsgs x aux p (B.eval x.length) (S.simulate x aux r)
+++ List.replicate (k.eval x.length - p) [])`. -/
+theorem phasePrefix_succ_simulate (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
+    (x z rV rS : List Bool) (i : ℕ) (r : S.Coins x.length)
+    (hcoins : coinBlock (S.coinLen x.length) i rS = List.ofFn r) :
+    phasePrefix S k B verifierFirst x z rV rS (i + 1) =
+      let pre := phasePrefix S k B verifierFirst x z rV rS i
+      let aux := phaseAux z rV i pre
+      let p := if verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2
+      pre ++ (normalizePhaseMsgs x aux p (B.eval x.length) (S.simulate x aux r) ++
+        List.replicate (k.eval x.length - p) []) := by
+  rw [phasePrefix_succ]
+  dsimp only
+  rw [hcoins, ← NUPPT.runAt_eq, ← NUPPT.simulate_eq]
+
+/-- After `i` phases the normalized prefix has exactly `i * k(|x|)` messages:
+`(phasePrefix S k B verifierFirst x z rV rS i).length = i * k.eval x.length`. -/
+theorem length_phasePrefix (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
+    (x z rV rS : List Bool) (i : ℕ) :
+    (phasePrefix S k B verifierFirst x z rV rS i).length = i * k.eval x.length := by
+  induction i with
+  | zero => rw [phasePrefix_zero, List.length_nil, Nat.zero_mul]
+  | succ i ih =>
+    rw [phasePrefix_succ]
+    dsimp only
+    rw [List.length_append, List.length_append, length_normalizePhaseMsgs,
+      List.length_replicate, ih, Nat.succ_mul]
+    have hp : (if verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2) ≤
+        k.eval x.length := by cases verifierFirst <;> simp only [Bool.false_eq_true,
+          if_false, if_true] <;> omega
+    omega
+
+/-- Every message in `phasePrefix S k B verifierFirst x z rV rS i` has at most `B(|x|)` bits.
+`m.length ≤ B.eval x.length`.
+
+**Proof sketch.** Induct on the number of phases. Earlier messages satisfy the induction
+hypothesis, normalized real messages satisfy the published bit bound, and every filler is
+empty. These are exactly the three portions of the next prefix. -/
+theorem length_le_of_mem_phasePrefix (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
+    (x z rV rS : List Bool) (i : ℕ) {m : List Bool}
+    (hm : m ∈ phasePrefix S k B verifierFirst x z rV rS i) : m.length ≤ B.eval x.length := by
+  induction i generalizing m with
+  | zero =>
+    rw [phasePrefix_zero] at hm
+    exact False.elim (List.not_mem_nil hm)
+  | succ i ih =>
+    rw [phasePrefix_succ] at hm
+    dsimp only at hm
+    rcases List.mem_append.mp hm with hm | hm
+    · exact ih hm
+    · rcases List.mem_append.mp hm with hm | hm
+      · exact length_le_of_mem_normalizePhaseMsgs _ _ _ _ _ hm
+      · have he := (List.mem_replicate.mp hm).2
+        subst m
+        exact Nat.zero_le _
+
+/-- The encoded prefix after `i` phases has length at most
+`i * k(|x|) * (2 * B(|x|) + 2)`, uniformly over every simulator output and tape.
+`(Strategy.encodeMsgs (phasePrefix S k B verifierFirst x z rV rS i)).length ≤ i * k.eval x.length *
+(2 * B.eval x.length + 2)`. -/
+theorem length_encodeMsgs_phasePrefix_le (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
+    (x z rV rS : List Bool) (i : ℕ) :
+    (Strategy.encodeMsgs (phasePrefix S k B verifierFirst x z rV rS i)).length ≤
+      i * k.eval x.length * (2 * B.eval x.length + 2) := by
+  have h := CommitmentLemmas.length_encodeMsgs_le
+    (phasePrefix S k B verifierFirst x z rV rS i) (B.eval x.length)
+    (fun m hm => length_le_of_mem_phasePrefix S k B verifierFirst x z rV rS i hm)
+  simpa only [length_phasePrefix] using h
+
+/-- If `N` is polynomial-time in unary, the encoding of `N w` empty messages is
+polynomial-time: `w ↦ Strategy.encodeMsgs (List.replicate (N w) [])`.
+`PolyTimeComputable fun w => Strategy.encodeMsgs (List.replicate (N w) [])`. -/
+theorem encode_emptyMsgs_poly {N : List Bool → ℕ}
+    (hN : PolyTimeComputable fun w => List.replicate (N w) true) :
+    PolyTimeComputable fun w => Strategy.encodeMsgs (List.replicate (N w) []) := by
+  have h := ColMachines.polyTimeComputable_flatMap_range
+    (E := fun _ _ => pairEncode ([] : List Bool) [])
+    (polyTimeComputable_const (pairEncode ([] : List Bool) [])) hN
+  refine h.congr fun w => ?_
+  have he : List.replicate (N w) ([] : List Bool) =
+      (List.range (N w)).map (fun _ => []) := by
+    rw [List.map_const', List.length_range]
+  rw [ColMachines.encodeMsgs_eq_flatMap, he, List.flatMap_map]
+
+/-- For a uniform `S`, fixed polynomials `k,B,Q`, orientation `verifierFirst`, and
+polynomial-time words `X,Z,RV,RS`, the entire encoded prefix is polynomial-time:
+`w ↦ encodeMsgs (phasePrefix S k B verifierFirst (X w) (Z w) (RV w) (RS w)
+(Q.eval (X w).length))`. [PS10, Theorem 175.1, strict-PPT sequential simulation].
+`PolyTimeComputable fun w => Strategy.encodeMsgs (phasePrefix S k B verifierFirst (X w) (Z w) (RV w)
+(RS w) (Q.eval (X w).length))`.
+
+**Proof sketch.** Instantiate the published counted-loop host with the encoded prefix as
+state and its existing unary counter as phase index. The step decodes the prior state,
+assembles the phase auxiliary input, runs `S` on the selected fresh coin block, canonically
+normalizes its output, and appends that phase's real-message encoding and empty fillers.
+The state is exactly the encoding of the semantic prefix, by induction using the published
+loop equations. Its encoding bound, together with a polynomial bound on `|X w|`, bounds every
+genuine orbit state. The existing orbit-bounded counted-loop theorem then gives strict
+polynomial time, with no newly constructed host. -/
+theorem phasePrefix_poly (S : NUPPT) (hS : S.Uniform) (k B Q : PolyExpr)
+    (verifierFirst : Bool) {X Z RV RS : List Bool → List Bool}
+    (hX : PolyTimeComputable X) (hZ : PolyTimeComputable Z)
+    (hRV : PolyTimeComputable RV) (hRS : PolyTimeComputable RS) :
+    PolyTimeComputable fun w => Strategy.encodeMsgs
+      (phasePrefix S k B verifierFirst (X w) (Z w) (RV w) (RS w) (Q.eval (X w).length)) := by
+  let upd : List Bool → List Bool := fun w =>
+    let t := pairFstD w
+    let i := (pairFstD (pairSndD w)).length
+    let pre := BinArith.decWords (pairSndD (pairSndD w))
+    let aux := phaseAux (Z t) (RV t) i pre
+    let p := if verifierFirst then k.eval (X t).length / 2 else (k.eval (X t).length + 1) / 2
+    pairSndD (pairSndD w) ++
+      (Strategy.encodeMsgs (normalizePhaseMsgs (X t) aux p (B.eval (X t).length)
+        (S.runAtL (X t).length (pairEncode (X t) aux)
+          (coinBlock (S.coinLen (X t).length) i (RS t)))) ++
+        Strategy.encodeMsgs (List.replicate (k.eval (X t).length - p) []))
+  -- Every component of one update is assembled from published polynomial-time machines.
+  have hXt : PolyTimeComputable fun w => X (pairFstD w) := hX.comp polyTimeComputable_pairFstD
+  have hZt : PolyTimeComputable fun w => Z (pairFstD w) := hZ.comp polyTimeComputable_pairFstD
+  have hRVt : PolyTimeComputable fun w => RV (pairFstD w) := hRV.comp polyTimeComputable_pairFstD
+  have hRSt : PolyTimeComputable fun w => RS (pairFstD w) := hRS.comp polyTimeComputable_pairFstD
+  have hIword := polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
+  have hI := EncodingMachines.unaryLength_poly hIword
+  have hstate := polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
+  have hcanonical := polyTimeComputable_encWords_decWords hstate
+  have hpre : PolyTimeComputable fun w =>
+      Strategy.encodeMsgs (BinArith.decWords (pairSndD (pairSndD w))) :=
+    hcanonical.congr fun w => (encodeMsgs_eq_encWords _).symm
+  have haux := phaseAux_poly hZt hRVt hI hpre
+  have hcoins : PolyTimeComputable fun w =>
+      coinBlock (S.coinLen (X (pairFstD w)).length) (pairFstD (pairSndD w)).length
+        (RS (pairFstD w)) := by
+    simpa only [NUPPT.coinLen_eq] using GI.coinSlice_poly S.coins hXt hIword hRSt
+  have hlay := NUPPT.polyTimeComputable_layout (EncodingMachines.unaryLength_poly hXt)
+    (hXt.pairEncode haux) (polyTimeComputable_const []) hcoins
+  have hsim : PolyTimeComputable fun w =>
+      S.runAtL (X (pairFstD w)).length
+        (pairEncode (X (pairFstD w)) (phaseAux (Z (pairFstD w)) (RV (pairFstD w))
+          (pairFstD (pairSndD w)).length (BinArith.decWords (pairSndD (pairSndD w)))))
+        (coinBlock (S.coinLen (X (pairFstD w)).length) (pairFstD (pairSndD w)).length
+          (RS (pairFstD w))) := by
+    refine (S.polyTimeComputable_output.comp hlay).congr fun w => ?_
+    rw [Function.comp_apply, NUPPT.runAtL_eq_output_layout, hS.advice_eq]
+    simp only [Function.comp_apply]
+  have hK := EncodingMachines.unaryPolyOf_poly k (EncodingMachines.unaryLength_poly hXt)
+  have hP : PolyTimeComputable fun w => List.replicate
+      (if verifierFirst then k.eval (X (pairFstD w)).length / 2
+        else (k.eval (X (pairFstD w)).length + 1) / 2) true := by
+    cases verifierFirst
+    · simpa only [EncodingMachines.divNum_eq] using EncodingMachines.divNum_poly
+        (EncodingMachines.unaryAdd_poly hK (EncodingMachines.unaryConst_poly 1))
+        (EncodingMachines.unaryConst_poly 2)
+    · simpa only [EncodingMachines.divNum_eq] using
+        EncodingMachines.divNum_poly hK (EncodingMachines.unaryConst_poly 2)
+  have hbits := EncodingMachines.unaryPolyOf_poly B (EncodingMachines.unaryLength_poly hXt)
+  have hnorm := polyTimeComputable_encode_normalizePhaseMsgs hXt haux hsim hP hbits
+  have hfill := encode_emptyMsgs_poly (EncodingMachines.unarySub_poly hK hP)
+  have hupd : PolyTimeComputable upd := hstate.append (hnorm.append hfill)
+  -- The machine state is exactly the public semantic prefix on the genuine orbit.
+  have hclosed : ∀ w i, EncodingMachines.loopState upd (fun _ => []) w i =
+      Strategy.encodeMsgs (phasePrefix S k B verifierFirst (X w) (Z w) (RV w) (RS w) i) := by
+    intro w i
+    induction i with
+    | zero => rw [EncodingMachines.loopState_zero, phasePrefix_zero, Strategy.encodeMsgs_nil]
+    | succ i ih =>
+      rw [EncodingMachines.loopState_succ]
+      dsimp only [upd]
+      simp only [pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]
+      rw [ih]
+      have hdec : BinArith.decWords (Strategy.encodeMsgs
+          (phasePrefix S k B verifierFirst (X w) (Z w) (RV w) (RS w) i)) =
+          phasePrefix S k B verifierFirst (X w) (Z w) (RV w) (RS w) i :=
+        (congrArg BinArith.decWords (encodeMsgs_eq_encWords _)).trans
+          (BinArith.decWords_encWords _)
+      rw [hdec, phasePrefix_succ, CommitmentLemmas.encodeMsgs_append,
+        CommitmentLemmas.encodeMsgs_append]
+  -- The phase-independent normalized-message bound supplies the loop's polynomial envelope.
+  obtain ⟨C, c, hC⟩ := hX.output_length_le
+  let XP : PolyExpr := .normal C c
+  let bound : PolyExpr := .mul (.mul (Q.subst XP) (k.subst XP))
+    (.add (.mul (.const 2) (B.subst XP)) (.const 2))
+  have hN := EncodingMachines.unaryPolyOf_poly Q (EncodingMachines.unaryLength_poly hX)
+  have hloop := ColMachines.polyTimeComputable_loopState' hupd (polyTimeComputable_const [])
+    hN bound (fun w i hi => by
+      rw [hclosed]
+      have hx : (X w).length ≤ XP.eval w.length := by
+        simpa only [XP, PolyExpr.eval_normal] using hC w
+      have hq := Q.eval_mono hx
+      have hk := k.eval_mono hx
+      have hb := B.eval_mono hx
+      simp only [bound, PolyExpr.eval_mul, PolyExpr.eval_add, PolyExpr.eval_const,
+        PolyExpr.eval_subst]
+      calc
+        _ ≤ i * k.eval (X w).length * (2 * B.eval (X w).length + 2) :=
+          length_encodeMsgs_phasePrefix_le S k B verifierFirst (X w) (Z w) (RV w) (RS w) i
+        _ ≤ Q.eval (X w).length * k.eval (X w).length *
+            (2 * B.eval (X w).length + 2) :=
+          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hi)
+        _ ≤ Q.eval (XP.eval w.length) * k.eval (XP.eval w.length) *
+            (2 * B.eval (XP.eval w.length) + 2) :=
+          Nat.mul_le_mul (Nat.mul_le_mul hq hk) (by omega))
+  exact hloop.congr fun w => hclosed w _
+
+/-- For uniform phase simulator `S`, polynomials `k,B,Q,CV`, and orientation `verifierFirst`,
+there is a uniform simulator `SQ` with coin polynomial `CV + Q*S.coins`. On `(x,z)` it samples
+one verifier tape from the first `CV(|x|)` coins, uses the remaining coins for the `Q(|x|)`
+phase calls, and outputs the canonical view with their normalized prefix.
+[PS10, Theorem 175.1; Gol01, §4.3.4, strict-PPT sequential simulation].
+`∃ SQ : NUPPT, SQ.Uniform ∧ SQ.coins = .add CV (.mul Q S.coins) ∧ ∀ x z (r : SQ.Coins x.length),
+SQ.simulate x z r = let rV := (List.ofFn r).take (CV.eval x.length); let rS := (List.ofFn r).drop
+(CV.eval x.length); View.encode ⟨x, z, rV, phasePrefix S k B verifierFirst x z rV rS (Q.eval
+x.length)⟩`.
+
+**Proof sketch.** Apply `phasePrefix_poly` to the common-input and auxiliary-input projections
+of the simulator layout, the first verifier-tape coin slice and the remaining phase tape.
+Pair these fields with the encoded prefix to produce the canonical view. The published
+`NUPPT.ofPolyTimeUniform` construction uses exactly the stated coin polynomial. Its activation
+and simulator readers, followed by the layout projection equations, give the exact formula.
+This includes empty prefixes when the phase count or round count is zero. -/
+theorem exists_phaseSimulator (S : NUPPT) (hS : S.Uniform) (k B Q CV : PolyExpr)
+    (verifierFirst : Bool) :
+    ∃ SQ : NUPPT, SQ.Uniform ∧ SQ.coins = .add CV (.mul Q S.coins) ∧
+      ∀ x z (r : SQ.Coins x.length), SQ.simulate x z r =
+        let rV := (List.ofFn r).take (CV.eval x.length)
+        let rS := (List.ofFn r).drop (CV.eval x.length)
+        View.encode ⟨x, z, rV, phasePrefix S k B verifierFirst x z rV rS (Q.eval x.length)⟩ := by
+  -- Decode both inputs and split the verifier and phase tapes through public PT readers.
+  let X : List Bool → List Bool := fun w => pairFstD (NUPPT.inArg w)
+  let Z : List Bool → List Bool := fun w => pairSndD (NUPPT.inArg w)
+  let RV : List Bool → List Bool := fun w => (NUPPT.inCoins w).take (CV.eval (X w).length)
+  let RS : List Bool → List Bool := fun w => (NUPPT.inCoins w).drop (CV.eval (X w).length)
+  have hX : PolyTimeComputable X :=
+    polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg
+  have hZ : PolyTimeComputable Z :=
+    polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg
+  have hcut := hX.pairEncode NUPPT.polyTimeComputable_inCoins
+  have hRV : PolyTimeComputable RV := by
+    refine ((polyTimeComputable_pairTakePoly CV).comp hcut).congr fun w => ?_
+    rw [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
+  have hRS : PolyTimeComputable RS := by
+    refine ((polyTimeComputable_pairDropPoly CV).comp hcut).congr fun w => ?_
+    rw [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
+  -- Assemble the normalized repeated prefix and encode the complete canonical view.
+  have hpre := phasePrefix_poly S hS k B Q verifierFirst hX hZ hRV hRS
+  let F : List Bool → List Bool := fun w =>
+    View.encode ⟨X w, Z w, RV w,
+      phasePrefix S k B verifierFirst (X w) (Z w) (RV w) (RS w) (Q.eval (X w).length)⟩
+  have hF : PolyTimeComputable F := by
+    refine ((hX.pairEncode hZ).pairEncode (hRV.pairEncode hpre)).congr fun w => ?_
+    dsimp only [F]
+    rw [View.encode_mk]
+  -- The uniform constructor and activation/layout readers identify every output field.
+  refine ⟨NUPPT.ofPolyTimeUniform hF (.add CV (.mul Q S.coins)),
+    NUPPT.ofPolyTimeUniform_uniform hF _, NUPPT.coins_ofPolyTimeUniform hF _, ?_⟩
+  intro x z r
+  rw [NUPPT.simulate_eq, NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform,
+    NUPPT.advInput_eq, ← NUPPT.layout_eq]
+  dsimp only [F, X, Z, RV, RS]
+  rw [NUPPT.inArg_layout, NUPPT.inCoins_layout, pairFstD_pairEncode, pairSndD_pairEncode]
+
+end TCSlib.Cryptography.SequentialZK
diff --git a/TCSlib/Cryptography/Composability/SequentialZK/Soundness.lean b/TCSlib/Cryptography/Composability/SequentialZK/Soundness.lean
new file mode 100644
index 000000000..b596d17b9
--- /dev/null
+++ b/TCSlib/Cryptography/Composability/SequentialZK/Soundness.lean
@@ -0,0 +1,169 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.ZeroKnowledge.Interaction
+import TCSlib.Cryptography.OneWayFunctions.Basic
+import Mathlib.Data.Fin.Tuple.Basic
+import Mathlib.Tactic.Ring
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Execution prefixes for sequential soundness
+
+## Main definitions
+
+This module introduces no definitions.
+
+## Main results
+
+* `Composability.exec_prefix`: each received history after `g` moves is a prefix of its
+  history after `g + t` moves.
+* `Composability.exec_fst_take`, `Composability.exec_snd_take`: taking the old history length
+  from the later history recovers the old history.
+* `Composability.uprob_adaptive_all_le`: phase success at most `s` after each prefix gives
+  total success at most `s ^ q`.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §4.4 (interactive executions) and Theorem 175.1 (sequential composition).
+-/
+
+namespace TCSlib.Cryptography.Composability
+
+/-- For strategies `P`, `V`, first-mover flag `vFirst`, common input `x`, auxiliary inputs
+`zP`, `zV`, tapes `rP`, `rV`, and move counts `g`, `t`, both components of
+`exec P V vFirst x zP zV rP rV g` are prefixes of the corresponding components after `g + t`
+moves. [PS10, §4.4].
+`(exec P V vFirst x zP zV rP rV g).1 <+: (exec P V vFirst x zP zV rP rV (g + t)).1 ∧ (exec P V
+vFirst x zP zV rP rV g).2 <+: (exec P V vFirst x zP zV rP rV (g + t)).2`.
+
+**Proof sketch.** Induct on the additional moves. Each move appends one message to exactly
+one received history, so prefix transitivity preserves both earlier histories. -/
+theorem exec_prefix (P V : Strategy) (vFirst : Bool) (x zP zV rP rV : List Bool)
+    (g t : ℕ) :
+    (exec P V vFirst x zP zV rP rV g).1 <+:
+        (exec P V vFirst x zP zV rP rV (g + t)).1 ∧
+      (exec P V vFirst x zP zV rP rV g).2 <+:
+        (exec P V vFirst x zP zV rP rV (g + t)).2 := by
+  induction t with
+  | zero => simp only [Nat.add_zero, List.prefix_rfl, and_self]
+  | succ t ih =>
+    rw [Nat.add_succ, exec_succ]
+    by_cases hm : moverIsV vFirst (g + t) = true
+    · simp only [hm, if_true]
+      exact ⟨List.prefix_append_of_prefix ih.1, ih.2⟩
+    · simp only [hm]
+      exact ⟨ih.1, List.prefix_append_of_prefix ih.2⟩
+
+/-- For `P`, `V`, `vFirst`, `x`, `zP`, `zV`, `rP`, `rV`, `g`, `t`, taking the length of
+`(exec P V vFirst x zP zV rP rV g).1` from the first component after `g + t` moves gives
+`(exec P V vFirst x zP zV rP rV g).1`.
+`(exec P V vFirst x zP zV rP rV (g + t)).1.take (exec P V vFirst x zP zV rP rV g).1.length = (exec P
+V vFirst x zP zV rP rV g).1`. -/
+theorem exec_fst_take (P V : Strategy) (vFirst : Bool) (x zP zV rP rV : List Bool)
+    (g t : ℕ) :
+    (exec P V vFirst x zP zV rP rV (g + t)).1.take
+        (exec P V vFirst x zP zV rP rV g).1.length =
+      (exec P V vFirst x zP zV rP rV g).1 :=
+  (List.prefix_iff_eq_take.mp (exec_prefix P V vFirst x zP zV rP rV g t).1).symm
+
+/-- For `P`, `V`, `vFirst`, `x`, `zP`, `zV`, `rP`, `rV`, `g`, `t`, taking the length of
+`(exec P V vFirst x zP zV rP rV g).2` from the second component after `g + t` moves gives
+`(exec P V vFirst x zP zV rP rV g).2`.
+`(exec P V vFirst x zP zV rP rV (g + t)).2.take (exec P V vFirst x zP zV rP rV g).2.length = (exec P
+V vFirst x zP zV rP rV g).2`. -/
+theorem exec_snd_take (P V : Strategy) (vFirst : Bool) (x zP zV rP rV : List Bool)
+    (g t : ℕ) :
+    (exec P V vFirst x zP zV rP rV (g + t)).2.take
+        (exec P V vFirst x zP zV rP rV g).2.length =
+      (exec P V vFirst x zP zV rP rV g).2 :=
+  (List.prefix_iff_eq_take.mp (exec_prefix P V vFirst x zP zV rP rV g t).2).symm
+
+/-- For `q` phases, a nonnegative bound `s`, and tests `Good i prefix fresh`, if
+`Pr[fresh, Good i prefix fresh] ≤ s` for every `i < q` and every earlier prefix, then
+`Pr[coins : Fin q → α, ∀ i, Good i (coins restricted below i) (coins i)] ≤ s ^ q`.
+[PS10, Theorem 175.1, sequential soundness].
+
+**Proof sketch.** Induct on the phase count, splitting the uniform tuple into its strict
+prefix and last coordinate with `Fin.snocEquiv`. The event for all phases implies success
+of the prefix together with the last phase. Conditional on a fixed prefix, the last phase
+succeeds with probability at most `s`. The published product bound therefore multiplies
+the prefix probability by `s`, and the induction hypothesis supplies the remaining power. -/
+theorem uprob_adaptive_all_le {α : Type*} [Fintype α] (q : ℕ) (s : ℝ) (hs : 0 ≤ s)
+    (Good : (i : ℕ) → (Fin i → α) → α → Prop)
+    (hGood : ∀ i < q, ∀ pre, uprob (Good i pre) ≤ s) :
+    uprob (fun coins : Fin q → α => ∀ i : Fin q,
+      Good i (fun j => coins (Fin.castLE i.isLt.le j)) (coins i)) ≤ s ^ q := by
+  revert hGood
+  induction q with
+  | zero =>
+    intro _
+    simpa only [pow_zero] using (uprob_le_one
+      (fun coins : Fin 0 → α => ∀ i : Fin 0,
+        Good i (fun j => coins (Fin.castLE i.isLt.le j)) (coins i)))
+  | succ q ih =>
+    intro hGood
+    -- Split the final fresh coordinate from the earlier uniform tuple.
+    let e : (Fin q → α) × α ≃ (Fin (q + 1) → α) :=
+      (Equiv.prodComm _ _).trans (Fin.snocEquiv (fun _ => α))
+    have he (a : (Fin q → α) × α) : e a = Fin.snoc a.1 a.2 := rfl
+    rw [← uprob_comp_equiv e]
+    have hmono :
+        uprob (fun a : (Fin q → α) × α => ∀ i : Fin (q + 1),
+          Good i (fun j => (e a) (Fin.castLE i.isLt.le j)) ((e a) i)) ≤
+        uprob (fun a : (Fin q → α) × α =>
+          (∀ i : Fin q, Good i (fun j => a.1 (Fin.castLE i.isLt.le j)) (a.1 i)) ∧
+            Good q a.1 a.2) := by
+      apply uprob_mono
+      intro a ha
+      rw [he] at ha
+      constructor
+      · intro i
+        have hi := ha (Fin.castSucc i)
+        have hpre :
+            (fun j : Fin i => (Fin.snoc a.1 a.2 : Fin (q + 1) → α)
+              (Fin.castLE (Fin.castSucc i).isLt.le j)) =
+            (fun j => a.1 (Fin.castLE i.isLt.le j)) := by
+          funext j
+          have hj : (Fin.castLE (Fin.castSucc i).isLt.le j : Fin (q + 1)) =
+              Fin.castSucc (Fin.castLE i.isLt.le j) := Fin.ext rfl
+          rw [hj, Fin.snoc_castSucc]
+        have hi' : Good i
+            (fun j : Fin i => (Fin.snoc a.1 a.2 : Fin (q + 1) → α)
+              (Fin.castLE (Fin.castSucc i).isLt.le j))
+            ((Fin.snoc a.1 a.2 : Fin (q + 1) → α) (Fin.castSucc i)) := hi
+        rw [hpre, Fin.snoc_castSucc] at hi'
+        exact hi'
+      · have hi := ha (Fin.last q)
+        have hpre :
+            (fun j : Fin q => (Fin.snoc a.1 a.2 : Fin (q + 1) → α)
+              (Fin.castLE (Fin.last q).isLt.le j)) =
+            a.1 := by
+          funext j
+          have hj : (Fin.castLE (Fin.last q).isLt.le j : Fin (q + 1)) =
+              Fin.castSucc j := Fin.ext rfl
+          rw [hj, Fin.snoc_castSucc]
+        have hi' : Good q
+            (fun j : Fin q => (Fin.snoc a.1 a.2 : Fin (q + 1) → α)
+              (Fin.castLE (Fin.last q).isLt.le j))
+            ((Fin.snoc a.1 a.2 : Fin (q + 1) → α) (Fin.last q)) := hi
+        rw [hpre, Fin.snoc_last] at hi'
+        exact hi'
+    -- Bound the last conditional success, then apply the prefix induction hypothesis.
+    have hbound := OneWay.uprob_and_le_mul
+      (fun pre : Fin q → α => ∀ i : Fin q,
+        Good i (fun j => pre (Fin.castLE i.isLt.le j)) (pre i))
+      (fun a : (Fin q → α) × α => Good q a.1 a.2)
+      (fun pre _ => hGood q (Nat.lt_succ_self q) pre)
+    have hih := ih (fun i hi pre => hGood i (by omega) pre)
+    calc _ ≤ _ := hmono
+         _ ≤ _ := hbound
+         _ ≤ s * s ^ q := mul_le_mul_of_nonneg_left hih hs
+         _ = s ^ (q + 1) := by rw [pow_succ]; ring
+
+end TCSlib.Cryptography.Composability
diff --git a/TCSlib/Cryptography/Composability/SequentialZK/Statistical.lean b/TCSlib/Cryptography/Composability/SequentialZK/Statistical.lean
new file mode 100644
index 000000000..568787422
--- /dev/null
+++ b/TCSlib/Cryptography/Composability/SequentialZK/Statistical.lean
@@ -0,0 +1,73 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Asymptotic.Sampling
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Averaging statistical phase comparisons over a shared prefix
+
+The hybrid proof of sequential zero-knowledge composition [PS10, Theorem 175.1] conditions
+on a common earlier prefix. A pointwise statistical bound survives averaging over the seed
+that determines that prefix. The nonnegative error premise also covers an empty prefix seed
+space, where the pointwise hypothesis is vacuous.
+
+## Main definitions
+
+There are no new definitions.
+
+## Main results
+
+* `statClose_average`: a common nonnegative pointwise bound remains valid after averaging
+  both samplers over the same independent prefix seed.
+* `statClose_chain`: `q` consecutive comparisons of error `δ` give error `q * δ`.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §7.2.1, Theorem 175.1.
+-/
+
+namespace TCSlib.Cryptography.SequentialZK
+
+/-- Averaging over a shared seed preserves a nonnegative statistical bound: for `0 ≤ δ` and
+`∀ a, StatClose (F a) (G a) δ`, the samplers `(a,b) ↦ F a b` and `(a,c) ↦ G a c` are
+`δ`-close. No seed type is required to be nonempty.
+
+**Proof sketch.** Express each test probability as an average over the shared seed. Each
+conditional difference is bounded by `δ`, so the public bound on differences of averages
+applies. -/
+theorem statClose_average {α β γ O : Type*} [Fintype α] [Fintype β] [Fintype γ]
+    {F : α → β → O} {G : α → γ → O} {δ : ℝ} (hδ : 0 ≤ δ)
+    (h : ∀ a, StatClose (F a) (G a) δ) :
+    StatClose (fun r : α × β => F r.1 r.2) (fun r : α × γ => G r.1 r.2) δ := by
+  refine (statClose_iff _ _ _).2 ?_
+  intro T
+  rw [uprob_prod, uprob_prod]
+  exact abs_uexp_sub_le hδ fun a => (h a).abs_uprob_sub_le T
+
+/-- A chain of `q` statistical comparisons adds the errors: if
+`∀ i < q, StatClose (f i) (f (i + 1)) δ`, then
+`StatClose (f 0) (f q) ((q : ℝ) * δ)`. The case `q = 0` needs no sign premise on `δ`.
+
+**Proof sketch.** Induct on the chain length. The empty chain is reflexive with error zero;
+append the last comparison using the public triangle inequality. -/
+theorem statClose_chain {Ω O : Type*} [Fintype Ω] (f : ℕ → Ω → O) (q : ℕ) (δ : ℝ)
+    (h : ∀ i < q, StatClose (f i) (f (i + 1)) δ) :
+    StatClose (f 0) (f q) ((q : ℝ) * δ) := by
+  revert h
+  induction q with
+  | zero =>
+    intro _
+    simpa only [Nat.cast_zero, zero_mul] using StatClose.refl (f 0)
+  | succ q ih =>
+    intro h
+    have hprev := ih fun i hi => h i (Nat.lt_succ_of_lt hi)
+    simpa only [Nat.cast_succ, add_mul, one_mul] using
+      hprev.trans (h q (Nat.lt_succ_self q))
+
+end TCSlib.Cryptography.SequentialZK
diff --git a/TCSlib/Cryptography/Composability/SequentialZK/StatisticalPostprocess.lean b/TCSlib/Cryptography/Composability/SequentialZK/StatisticalPostprocess.lean
new file mode 100644
index 000000000..dac42f97e
--- /dev/null
+++ b/TCSlib/Cryptography/Composability/SequentialZK/StatisticalPostprocess.lean
@@ -0,0 +1,60 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Asymptotic.Sampling
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Statistical post-processing with an unused product coordinate
+
+## Main definitions
+
+This module introduces no definitions.
+
+## Main results
+
+* `statClose_map_fst` post-processes close samplers and removes a product coordinate
+  on which the processed first sampler does not depend.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  Theorem 175.1 (sequential repetition of zero knowledge).
+-/
+
+namespace TCSlib.Cryptography.Composability
+
+/-- Suppose `X : α × β → γ` and `Y : τ → γ` are `ε`-close, and
+`f (X r) = H r.1` for every `r : α × β`. If `β` is nonempty, then
+`H` and `fun t => f (Y t)` are `ε`-close.
+[PS10, Theorem 175.1, statistical post-processing of one phase].
+
+**Proof sketch.** Apply the published statistical post-processing theorem to `f`.
+For each output test, pointwise equality changes the first processed event to an event
+of the first coordinate alone. The uniform-product projection law removes the unused
+second coordinate, giving exactly the desired test bound. -/
+theorem statClose_map_fst {α β τ γ δ : Type*} [Fintype α] [Fintype β] [Fintype τ]
+    [Nonempty β] (X : α × β → γ) (Y : τ → γ) (f : γ → δ) (H : α → δ) (ε : ℝ)
+    (hclose : StatClose X Y ε) (hfixed : ∀ r : α × β, f (X r) = H r.1) :
+    StatClose H (fun t => f (Y t)) ε := by
+  have hmap : StatClose (fun r : α × β => f (X r)) (fun t : τ => f (Y t)) ε :=
+    StatClose.map (X := X) (Y := Y) hclose f
+  apply (statClose_iff H (fun t : τ => f (Y t)) ε).2
+  intro T
+  have htest : |uprob (fun r : α × β => T (f (X r))) -
+      uprob (fun t : τ => T (f (Y t)))| ≤ ε :=
+    (statClose_iff (fun r : α × β => f (X r)) (fun t : τ => f (Y t)) ε).1 hmap T
+  have hreal : uprob (fun r : α × β => T (f (X r))) =
+      uprob (fun a : α => T (H a)) := by
+    have hpoint : uprob (fun r : α × β => T (f (X r))) =
+        uprob (fun r : α × β => T (H r.1)) :=
+      OneWay.uprob_congr fun r => Iff.of_eq (congrArg T (hfixed r))
+    exact hpoint.trans (uprob_fst (β := β) (fun a : α => T (H a)))
+  rw [hreal] at htest
+  exact htest
+
+end TCSlib.Cryptography.Composability
diff --git a/TCSlib/Cryptography/Composability/SequentialZK/StatisticalPrefix.lean b/TCSlib/Cryptography/Composability/SequentialZK/StatisticalPrefix.lean
new file mode 100644
index 000000000..5280812c5
--- /dev/null
+++ b/TCSlib/Cryptography/Composability/SequentialZK/StatisticalPrefix.lean
@@ -0,0 +1,155 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Composability.SequentialZK.NormalizedStep
+import TCSlib.Cryptography.Composability.SequentialZK.PaddedProverSpec
+import TCSlib.Cryptography.Composability.SequentialZK.PrefixLaws
+import TCSlib.Cryptography.Composability.SequentialZK.StatisticalRecursion
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Statistical comparison of sequential phase prefixes
+
+A padded repeated-prover specification supplies the original phase's message count. A
+pointwise prover-message bound makes real phase views fixed points of normalization. The
+one-phase statistical comparison therefore applies to each normalized prefix extension,
+and the public sampler-recursion bound accumulates the error. [PS10, Theorem 175.1].
+
+## Main definitions
+
+There are no new definitions.
+
+## Main results
+
+* `PaddedProverSpec.statClose_step`: raw one-phase closeness bounds every prefix update.
+* `PaddedProverSpec.statClose_prefix`: `q` phase updates accumulate at most `q * δ` error.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §7.2.1, Theorem 175.1.
+* [Gol01] O. Goldreich, *Foundations of Cryptography, Volume I: Basic Tools*, Cambridge
+  University Press, 2001, §4.3.4.
+-/
+
+namespace TCSlib.Cryptography.SequentialZK.PaddedProverSpec
+
+open Complexity
+
+/-- For `d : PaddedProverSpec π ρ x q p`, verifier `V`, simulator `S`, inputs `y,z`, tape
+`rV`, cap `B`, and error `δ`, a uniform `B` bound on `π.P.next` and raw `δ`-close phase views
+at every auxiliary input imply `δ`-close `realStep` and `simStep` at every index `i` and
+prefix `pre`. No shape assumption on `pre` and no efficiency assumption on `S` is required.
+[PS10, Theorem 175.1; Gol01, §4.3.4].
+`StatClose (realStep π V x y z rV p i pre) (simStep S x z rV (π.rounds.eval x.length) B p i pre) δ`.
+
+**Proof sketch.** Instantiate the zero-verifier normalization comparison with the original
+protocol whose verifier is the phase wrapper. The published wrapper reader supplies its
+zero coin length, and the specification supplies its exact received-message count. The
+published `withV` field readers preserve the original prover, move count and first mover.
+Transport the prover seed by the equality of its coin lengths; the public `ofFn` reader
+shows that this transport preserves its raw tape. The two update readers then identify
+exactly the real and normalized steps, with the same empty padding and error. -/
+theorem statClose_step {π ρ : Protocol} {x : List Bool} {q p : ℕ}
+    (d : PaddedProverSpec π ρ x q p) (V : Strategy) (S : NUPPT)
+    (y z rV : List Bool) (B : ℕ) (δ : ℝ)
+    (hbound : ∀ r hist, (π.P.next x y r hist).length ≤ B)
+    (hclose : ∀ aux : List Bool,
+      StatClose (fun r : (π.withV (phaseVerifier V)).ExecCoins
+        (π.withV (phaseVerifier V)).P x =>
+          ((π.withV (phaseVerifier V)).viewV x y aux r).encode) (S.simulate x aux) δ)
+    (i : ℕ) (pre : List (List Bool)) :
+    StatClose (realStep π V x y z rV p i pre)
+      (simStep S x z rV (π.rounds.eval x.length) B p i pre) δ := by
+  -- Read the wrapper's zero-coin contract and the original phase-count equation.
+  let aux := phaseAux z rV i pre
+  have hcoins : (π.withV (phaseVerifier V)).V.coinLen x.length = 0 := by
+    rw [Protocol.withV_V, phaseVerifier_coinLen]
+  have hP : ∀ r hist, ((π.withV (phaseVerifier V)).P.next x y r hist).length ≤ B := by
+    rw [Protocol.withV_P]
+    exact hbound
+  have hcount : ∀ r : List Bool,
+      (exec (π.withV (phaseVerifier V)).P (π.withV (phaseVerifier V)).V
+        (π.withV (phaseVerifier V)).verifierFirst x y aux r []
+        ((π.withV (phaseVerifier V)).rounds.eval x.length)).2.length = p := by
+    intro r
+    rw [Protocol.withV_P, Protocol.withV_V, Protocol.withV_verifierFirst,
+      Protocol.withV_rounds]
+    exact d.original_count (phaseVerifier V) y aux r []
+  let F : (π.withV (phaseVerifier V)).P.Coins x.length → List (List Bool) :=
+    fun r => pre ++
+      ((exec (π.withV (phaseVerifier V)).P (π.withV (phaseVerifier V)).V
+        (π.withV (phaseVerifier V)).verifierFirst x y aux (List.ofFn r) []
+        ((π.withV (phaseVerifier V)).rounds.eval x.length)).2 ++
+          List.replicate ((π.withV (phaseVerifier V)).rounds.eval x.length - p) [])
+  let G : S.Coins x.length → List (List Bool) :=
+    fun r => pre ++ (normalizePhaseMsgs x aux p B (S.simulate x aux r) ++
+      List.replicate ((π.withV (phaseVerifier V)).rounds.eval x.length - p) [])
+  have hn : StatClose F G δ := by
+    with_reducible exact (statClose_normalized_step (π.withV (phaseVerifier V)) S x y aux
+      pre p B δ hcoins hP hcount (hclose aux))
+  -- Reindex the unchanged prover tape through its explicit coin-length equality.
+  have hlen : π.P.coinLen x.length = (π.withV (phaseVerifier V)).P.coinLen x.length := by
+    rw [Protocol.withV_P]
+  let e : π.P.Coins x.length ≃ (π.withV (phaseVerifier V)).P.Coins x.length :=
+    Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)
+  have hword (r : π.P.Coins x.length) : List.ofFn (e r) = List.ofFn r :=
+    (List.ofFn_congr hlen r).symm
+  have hindex : StatClose (fun r : π.P.Coins x.length => F (e r)) G δ :=
+    StatClose.comp_equiv_left (X := F) (Y := G) hn e
+  -- Identify both concrete samplers with the public prefix-update readers.
+  have hleft : (fun r : π.P.Coins x.length => F (e r)) =
+      realStep π V x y z rV p i pre := by
+    funext r
+    dsimp only [F]
+    rw [hword, Protocol.withV_P, Protocol.withV_V, Protocol.withV_verifierFirst,
+      Protocol.withV_rounds, realStep_eq]
+  have hright : G = simStep S x z rV (π.rounds.eval x.length) B p i pre := by
+    funext r
+    dsimp only [G]
+    rw [Protocol.withV_rounds, simStep_eq]
+  rw [hleft, hright] at hindex
+  exact hindex
+
+/-- For `d : PaddedProverSpec π ρ x q p`, verifier `V`, simulator `S`, inputs `y,z`, tape
+`rV`, cap `B`, and error `δ`, suppose `∀ r hist, |π.P.next x y r hist| ≤ B` and every raw
+phase-view sampler is `δ`-close to `S.simulate x aux`. Then
+`StatClose (realPrefix π V x y z rV p q)
+  (simPrefix S x z rV (π.rounds.eval |x|) B p q) ((q : ℝ) * δ)`.
+No uniformity or efficiency premise on `S` is needed. [PS10, Theorem 175.1; Gol01, §4.3.4].
+
+**Proof sketch.** The raw comparison at any auxiliary input gives `0 ≤ δ`. The preceding
+step comparison applies at every possible prefix, including malformed simulated prefixes.
+Instantiate the generic sampler-recursion theorem with the real and simulated prefix folds,
+their published empty-table and snoc equations, and that uniform step comparison. Its
+linear accumulation gives exactly the stated `q * δ` error, also when `q = 0`. -/
+theorem statClose_prefix {π ρ : Protocol} {x : List Bool} {q p : ℕ}
+    (d : PaddedProverSpec π ρ x q p) (V : Strategy) (S : NUPPT)
+    (y z rV : List Bool) (B : ℕ) (δ : ℝ)
+    (hbound : ∀ r hist, (π.P.next x y r hist).length ≤ B)
+    (hclose : ∀ aux : List Bool,
+      StatClose (fun r : (π.withV (phaseVerifier V)).ExecCoins
+        (π.withV (phaseVerifier V)).P x =>
+          ((π.withV (phaseVerifier V)).viewV x y aux r).encode) (S.simulate x aux) δ) :
+    StatClose (realPrefix π V x y z rV p q)
+      (simPrefix S x z rV (π.rounds.eval x.length) B p q) ((q : ℝ) * δ) := by
+  have hδ : 0 ≤ δ := StatClose.nonneg
+    (X := fun r : (π.withV (phaseVerifier V)).ExecCoins
+      (π.withV (phaseVerifier V)).P x =>
+        ((π.withV (phaseVerifier V)).viewV x y [] r).encode)
+    (Y := S.simulate x []) (hclose [])
+  with_reducible exact (statClose_recursion
+    (α := π.P.Coins x.length) (β := S.Coins x.length) (State := List (List Bool))
+    (realPrefix π V x y z rV p) (simPrefix S x z rV (π.rounds.eval x.length) B p) []
+    (realStep π V x y z rV p) (simStep S x z rV (π.rounds.eval x.length) B p)
+    (realPrefix_zero π V x y z rV p)
+    (simPrefix_zero S x z rV (π.rounds.eval x.length) B p)
+    (realPrefix_snoc π V x y z rV p)
+    (simPrefix_snoc S x z rV (π.rounds.eval x.length) B p) q δ hδ
+    (fun i _ pre => d.statClose_step V S y z rV B δ hbound hclose i pre))
+
+end TCSlib.Cryptography.SequentialZK.PaddedProverSpec
diff --git a/TCSlib/Cryptography/Composability/SequentialZK/StatisticalRecursion.lean b/TCSlib/Cryptography/Composability/SequentialZK/StatisticalRecursion.lean
new file mode 100644
index 000000000..4ef1a4f3e
--- /dev/null
+++ b/TCSlib/Cryptography/Composability/SequentialZK/StatisticalRecursion.lean
@@ -0,0 +1,139 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Composability.SequentialZK.Statistical
+import Mathlib.Data.Fin.Tuple.Basic
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Statistical accumulation for caller-supplied sampler recursions
+
+Sequential zero-knowledge composition [PS10, Theorem 175.1] compares two recursively sampled
+prefixes. This file assumes their zero and snoc equations as public contracts, and proves
+that a common one-step statistical bound accumulates linearly. It defines no recursion,
+loop, simulator, or computational host.
+
+## Main definitions
+
+There are no new definitions.
+
+## Main results
+
+* `statClose_recursion`: caller-supplied real and simulated samplers, with a common initial
+  state and `δ`-close updates at every state, are `q * δ`-close after `q` updates.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §7.2.1, Theorem 175.1.
+-/
+
+namespace TCSlib.Cryptography.SequentialZK
+
+/-- For families `realFamily q` and `simFamily q` with common initial state `initial` and
+supplied zero/snoc equations for `realStep` and `simStep`, if `0 ≤ δ` and
+`∀ i < q, ∀ state, StatClose (realStep i state) (simStep i state) δ`, then
+`StatClose (realFamily q) (simFamily q) ((q : ℝ) * δ)`. The state type is arbitrary and the
+finite coin types need not be nonempty.
+
+**Proof sketch.** Induct on the number of updates. The zero equations give the same constant
+sampler on the unique empty coin table. At the successor step, first replace only the last
+real update by its simulated update, averaging its `δ` bound over the common real prefix.
+Then apply the induction hypothesis to the prefixes and the public randomized postprocessing
+reader to their common simulated last update. The triangle inequality adds `δ + qδ`.
+The snoc equivalences identify a prefix and a last coin with the full coin table. -/
+theorem statClose_recursion {α β State : Type*} [Fintype α] [Fintype β]
+    (realFamily : (q : ℕ) → (Fin q → α) → State)
+    (simFamily : (q : ℕ) → (Fin q → β) → State) (initial : State)
+    (realStep : ℕ → State → α → State) (simStep : ℕ → State → β → State)
+    (real_zero : ∀ r, realFamily 0 r = initial)
+    (sim_zero : ∀ r, simFamily 0 r = initial)
+    (real_snoc : ∀ q r a, realFamily (q + 1) (Fin.snoc r a) =
+      realStep q (realFamily q r) a)
+    (sim_snoc : ∀ q r b, simFamily (q + 1) (Fin.snoc r b) =
+      simStep q (simFamily q r) b)
+    (q : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
+    (hstep : ∀ i < q, ∀ state, StatClose (realStep i state) (simStep i state) δ) :
+    StatClose (realFamily q) (simFamily q) ((q : ℝ) * δ) := by
+  classical
+  revert hstep
+  induction q with
+  | zero =>
+    intro _
+    letI : Nonempty (Fin 0 → α) := ⟨Fin.elim0⟩
+    letI : Nonempty (Fin 0 → β) := ⟨Fin.elim0⟩
+    simp only [Nat.cast_zero, zero_mul]
+    refine (statClose_iff (realFamily 0) (simFamily 0) (0 : ℝ)).2 ?_
+    intro T
+    by_cases hT : T initial
+    · simp only [real_zero, sim_zero, hT, uprob_true, sub_self, abs_zero, le_refl]
+    · simp only [real_zero, sim_zero, hT, uprob_false, sub_self, abs_zero, le_refl]
+  | succ q ih =>
+    intro hstep
+    have hprev : StatClose (realFamily q) (simFamily q) ((q : ℝ) * δ) :=
+      ih fun i hi state => hstep i (Nat.lt_succ_of_lt hi) state
+    -- Replace only the last update while preserving the common real prefix.
+    have hcurrent (r : Fin q → α) :
+        StatClose (realStep q (realFamily q r)) (simStep q (realFamily q r)) δ :=
+      hstep q (Nat.lt_succ_self q) (realFamily q r)
+    have hfirst :
+        StatClose (fun r : (Fin q → α) × α => realStep q (realFamily q r.1) r.2)
+          (fun r : (Fin q → α) × β => simStep q (realFamily q r.1) r.2) δ :=
+      statClose_average (α := Fin q → α) (β := α) (γ := β) (O := State)
+        (F := fun r a => realStep q (realFamily q r) a)
+        (G := fun r b => simStep q (realFamily q r) b) (δ := δ) hδ hcurrent
+    -- Compare prefixes through the same randomized simulated last update.
+    have hsecond :
+        StatClose (fun r : (Fin q → α) × β => simStep q (realFamily q r.1) r.2)
+          (fun r : (Fin q → β) × β => simStep q (simFamily q r.1) r.2) ((q : ℝ) * δ) :=
+      (statClose_iff
+        (fun r : (Fin q → α) × β => simStep q (realFamily q r.1) r.2)
+        (fun r : (Fin q → β) × β => simStep q (simFamily q r.1) r.2)
+        ((q : ℝ) * δ)).2 fun T =>
+        hprev.abs_uprob_sub_le_prod (ρ := β) fun state coin => T (simStep q state coin)
+    have hjoined :
+        StatClose (fun r : (Fin q → α) × α => realStep q (realFamily q r.1) r.2)
+          (fun r : (Fin q → β) × β => simStep q (simFamily q r.1) r.2)
+          (δ + (q : ℝ) * δ) :=
+      hfirst.trans hsecond
+    -- Reindex full coin tables as their prefixes and last entries.
+    let eA : (Fin (q + 1) → α) ≃ (Fin q → α) × α :=
+      (Fin.snocEquiv (fun _ : Fin (q + 1) => α)).symm.trans
+        (Equiv.prodComm α (Fin q → α))
+    let eB : (Fin (q + 1) → β) ≃ (Fin q → β) × β :=
+      (Fin.snocEquiv (fun _ : Fin (q + 1) => β)).symm.trans
+        (Equiv.prodComm β (Fin q → β))
+    have heA (r : Fin (q + 1) → α) : eA r = (Fin.init r, r (Fin.last q)) := rfl
+    have heB (r : Fin (q + 1) → β) : eB r = (Fin.init r, r (Fin.last q)) := rfl
+    have hleftIndex :
+        StatClose
+          (fun r : Fin (q + 1) → α => realStep q (realFamily q (eA r).1) (eA r).2)
+          (fun r : (Fin q → β) × β => simStep q (simFamily q r.1) r.2)
+          (δ + (q : ℝ) * δ) :=
+      hjoined.comp_equiv_left eA
+    have hfull :
+        StatClose
+          (fun r : Fin (q + 1) → α => realStep q (realFamily q (eA r).1) (eA r).2)
+          (fun r : Fin (q + 1) → β => simStep q (simFamily q (eB r).1) (eB r).2)
+          (δ + (q : ℝ) * δ) :=
+      hleftIndex.comp_equiv_right eB
+    have hleft (r : Fin (q + 1) → α) :
+        realStep q (realFamily q (eA r).1) (eA r).2 = realFamily (q + 1) r := by
+      simp only [heA]
+      simpa only [Fin.snoc_init_self] using (real_snoc q (Fin.init r) (r (Fin.last q))).symm
+    have hright (r : Fin (q + 1) → β) :
+        simStep q (simFamily q (eB r).1) (eB r).2 = simFamily (q + 1) r := by
+      simp only [heB]
+      simpa only [Fin.snoc_init_self] using (sim_snoc q (Fin.init r) (r (Fin.last q))).symm
+    have hout : StatClose (realFamily (q + 1)) (simFamily (q + 1)) (δ + (q : ℝ) * δ) := by
+      simpa only [hleft, hright] using hfull
+    have herror : δ + (q : ℝ) * δ = ((q + 1 : ℕ) : ℝ) * δ := by
+      rw [Nat.cast_succ, add_mul, one_mul]
+      exact add_comm _ _
+    simpa only [herror] using hout
+
+end TCSlib.Cryptography.SequentialZK
diff --git a/TCSlib/Cryptography/Composability/SequentialZK/StatisticalTransfer.lean b/TCSlib/Cryptography/Composability/SequentialZK/StatisticalTransfer.lean
new file mode 100644
index 000000000..2aa997dd9
--- /dev/null
+++ b/TCSlib/Cryptography/Composability/SequentialZK/StatisticalTransfer.lean
@@ -0,0 +1,116 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Composability.SequentialZK.StatisticalPrefix
+import TCSlib.Cryptography.Composability.SequentialZK.EndpointSampling
+import TCSlib.Cryptography.ZeroKnowledge.Defs
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Statistical zero knowledge from the padded-prover contract
+
+## Main definitions
+
+This module introduces no definitions or computational hosts.
+
+## Main results
+
+* `statZK_of_padded_spec`: a padded repetition satisfying the published prover contract
+  preserves statistical zero knowledge with the exact sum of the phase errors.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  Theorem 175.1.
+-/
+
+namespace TCSlib.Cryptography.SequentialZK
+
+open Complexity
+
+/-- For protocols `π,ρ`, relation `R`, error `δ`, bound `B`, and phase polynomial `Q`, if
+`π` is statistically zero knowledge with error `δ`, has prover bound `B`, and `ρ` satisfies
+`PaddedProverSpec π ρ x (Q.eval |x|) p` at every `x`, with the original mover-dependent
+real-message count `p`, then `ρ` is statistically zero knowledge with error `Q(n)*δ(n)`.
+[PS10, Theorem 175.1; Gol01, §4.3.4].
+`StatZK ρ R (fun n => Q.eval n * δ n)`.
+
+**Proof sketch.** Apply the original statistical hypothesis to the efficient fixed-tape
+phase verifier. The existing uniform prefix machine supplies one strict-PPT simulator using
+one global verifier tape and independent phase simulator coins. At each witnessed input the
+original comparison makes its error nonnegative. The normalized phase-recursion theorem
+bounds each fixed-tape prefix comparison by the sum of the phase errors. Pair the prefixes
+with the common verifier tape and average. The canonical endpoint readers reindex both
+finite coin spaces and identify the real view and the constructed simulator exactly.
+Zero phases and zero rounds require no separate positivity premise. -/
+theorem statZK_of_padded_spec {π ρ : Protocol} {R : List Bool → List Bool → Prop}
+    {δ : ℕ → ℝ} {B : PolyExpr} (h : StatZK π R δ) (hB : π.ProverBounded R B)
+    (Q : PolyExpr)
+    (hspec : ∀ x, PaddedProverSpec π ρ x (Q.eval x.length)
+      (if π.verifierFirst then π.rounds.eval x.length / 2
+        else (π.rounds.eval x.length + 1) / 2)) :
+    StatZK ρ R (fun n => Q.eval n * δ n) := by
+  apply (StatZK_iff ρ R _).2
+  intro V hV
+  -- Choose one phase simulator and realize its repeated normalized prefix machine.
+  obtain ⟨S, hS, hclose⟩ := (StatZK_iff π R δ).1 h (phaseVerifier V)
+    (phaseVerifier_efficient (V := V) hV)
+  obtain ⟨SQ, hSQ, hcoins, hsim⟩ :=
+    exists_phaseSimulator S hS π.rounds B Q V.coins π.verifierFirst
+  refine ⟨SQ, hSQ, ?_⟩
+  intro x y z hxy
+  let p := if π.verifierFirst then π.rounds.eval x.length / 2
+    else (π.rounds.eval x.length + 1) / 2
+  have hδ : 0 ≤ δ x.length := by
+    with_reducible exact ((hclose x y [] hxy).nonneg)
+
+  have hprefix (rV : V.Coins x.length) :
+      StatClose (realPrefix π V x y z (List.ofFn rV) p (Q.eval x.length))
+        (simPrefix S x z (List.ofFn rV) (π.rounds.eval x.length) (B.eval x.length)
+          p (Q.eval x.length)) ((Q.eval x.length : ℝ) * δ x.length) := by
+    with_reducible exact ((hspec x).statClose_prefix V S y z (List.ofFn rV) (B.eval x.length)
+      (δ x.length)
+      (fun r hist => (Protocol.proverBounded_iff π R B).1 hB x y r hist hxy)
+      (fun aux => hclose x y aux hxy))
+  -- Pair both prefixes with their common verifier tape and average over that tape.
+  have hpair (rV : V.Coins x.length) : StatClose
+      (fun r : Fin (Q.eval x.length) → π.P.Coins x.length =>
+        (rV, realPrefix π V x y z (List.ofFn rV) p (Q.eval x.length) r))
+      (fun r : Fin (Q.eval x.length) → S.Coins x.length =>
+        (rV, simPrefix S x z (List.ofFn rV) (π.rounds.eval x.length)
+          (B.eval x.length) p (Q.eval x.length) r))
+      ((Q.eval x.length : ℝ) * δ x.length) := by
+    with_reducible exact (StatClose.map
+      (σ := Fin (Q.eval x.length) → π.P.Coins x.length)
+      (τ := Fin (Q.eval x.length) → S.Coins x.length)
+      (γ := List (List Bool)) (γ' := V.Coins x.length × List (List Bool))
+      (X := realPrefix π V x y z (List.ofFn rV) p (Q.eval x.length))
+      (Y := simPrefix S x z (List.ofFn rV) (π.rounds.eval x.length)
+        (B.eval x.length) p (Q.eval x.length)) (hprefix rV) (fun pre => (rV, pre)))
+  have hjoint : StatClose
+      (fun r : V.Coins x.length × (Fin (Q.eval x.length) → π.P.Coins x.length) =>
+        (r.1, realPrefix π V x y z (List.ofFn r.1) p (Q.eval x.length) r.2))
+      (fun r : V.Coins x.length × (Fin (Q.eval x.length) → S.Coins x.length) =>
+        (r.1, simPrefix S x z (List.ofFn r.1) (π.rounds.eval x.length)
+          (B.eval x.length) p (Q.eval x.length) r.2))
+      ((Q.eval x.length : ℝ) * δ x.length) := by
+    with_reducible exact (statClose_average
+      (α := V.Coins x.length)
+      (β := Fin (Q.eval x.length) → π.P.Coins x.length)
+      (γ := Fin (Q.eval x.length) → S.Coins x.length)
+      (O := V.Coins x.length × List (List Bool))
+      (mul_nonneg (Nat.cast_nonneg _) hδ) hpair)
+  -- The exact coin equivalences identify the actual real and simulated view laws.
+  have hlen : SQ.coinLen x.length =
+      V.coinLen x.length + Q.eval x.length * S.coinLen x.length := by
+    rw [NUPPT.coinLen_eq, hcoins, PolyExpr.eval_add, PolyExpr.eval_mul,
+      Strategy.coinLen_eq, NUPPT.coinLen_eq]
+  with_reducible exact (statClose_view_endpoints (hspec x) V y z S SQ B rfl hlen
+    (fun r => by simpa only [Strategy.coinLen_eq] using hsim x z r)
+    ((Q.eval x.length : ℝ) * δ x.length) hjoint)
+
+end TCSlib.Cryptography.SequentialZK
diff --git a/TCSlib/Cryptography/Composability/SequentialZK/SuffixLaws.lean b/TCSlib/Cryptography/Composability/SequentialZK/SuffixLaws.lean
new file mode 100644
index 000000000..5aaeb47d6
--- /dev/null
+++ b/TCSlib/Cryptography/Composability/SequentialZK/SuffixLaws.lean
@@ -0,0 +1,124 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Composability.SequentialZK.SuffixMachine
+import TCSlib.Cryptography.Composability.SequentialZK.PrefixLaws
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Front-step and tape-independence readers for simulated suffixes
+
+## Main definitions
+
+This module introduces no definitions.
+
+## Main results
+
+* `phaseStep_eq_simStep` reads a phase update from a supplied typed simulator coin block.
+* `phaseSuffix_front` separates the first update of a simulated suffix.
+* `phaseSuffix_congr_blocks` shows that a suffix depends only on its own phase coin blocks.
+* `phaseSuffix_update_before` ignores an overwritten table entry before its starting phase.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  Theorem 175.1 (sequential repetition of zero knowledge).
+-/
+
+namespace TCSlib.Cryptography.SequentialZK
+
+open Complexity
+
+/-- If global block `j` of `rS` equals `List.ofFn coin`, the normalized raw-tape update
+`phaseStep` equals the typed update `simStep` on `coin`.
+`phaseStep S k B verifierFirst x z rV rS j pre = simStep S x z rV (k.eval x.length) (B.eval
+x.length) (if verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2) j pre coin`. -/
+theorem phaseStep_eq_simStep (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
+    (x z rV rS : List Bool) (j : ℕ) (pre : List (List Bool)) (coin : S.Coins x.length)
+    (hcoin : coinBlock (S.coinLen x.length) j rS = List.ofFn coin) :
+    phaseStep S k B verifierFirst x z rV rS j pre =
+      simStep S x z rV (k.eval x.length) (B.eval x.length)
+        (if verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2)
+        j pre coin := by
+  rw [phaseStep_eq, simStep_eq]
+  dsimp only
+  rw [hcoin, ← NUPPT.runAt_eq, ← NUPPT.simulate_eq]
+
+/-- A suffix with `t+1` updates first applies phase `start` and then runs `t` updates from
+`start+1`: `phaseSuffix … start pre (t+1) = phaseSuffix … (start+1)
+(phaseStep … start pre) t`. -/
+theorem phaseSuffix_front (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
+    (x z rV rS : List Bool) (start : ℕ) (pre : List (List Bool)) (t : ℕ) :
+    phaseSuffix S k B verifierFirst x z rV rS start pre (t + 1) =
+      phaseSuffix S k B verifierFirst x z rV rS (start + 1)
+        (phaseStep S k B verifierFirst x z rV rS start pre) t := by
+  induction t with
+  | zero => rw [phaseSuffix_succ, phaseSuffix_zero, phaseSuffix_zero, Nat.add_zero]
+  | succ t ih =>
+    rw [phaseSuffix_succ, ih, phaseSuffix_succ]
+    congr 1
+    omega
+
+/-- If two raw simulator tapes have equal coin blocks on `start≤j<start+t`, their
+simulated suffixes from the same prefix are equal.
+
+**Proof sketch.** Induct on the number of updates and use the published last-step suffix
+reader. The induction hypothesis identifies the preceding prefixes. The last update reads
+only its own coin block through the published phase-step reader, so the supplied last-block
+equality identifies the final updates. -/
+theorem phaseSuffix_congr_blocks (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
+    (x z rV rS rS' : List Bool) (start : ℕ) (pre : List (List Bool)) (t : ℕ)
+    (hblocks : ∀ j, start ≤ j → j < start + t →
+      coinBlock (S.coinLen x.length) j rS = coinBlock (S.coinLen x.length) j rS') :
+    phaseSuffix S k B verifierFirst x z rV rS start pre t =
+      phaseSuffix S k B verifierFirst x z rV rS' start pre t := by
+  induction t with
+  | zero => rw [phaseSuffix_zero, phaseSuffix_zero]
+  | succ t ih =>
+    have hprevious := ih (fun j hlo hhi => hblocks j hlo (by omega))
+    have hlast := hblocks (start + t) (by omega) (by omega)
+    rw [phaseSuffix_succ, phaseSuffix_succ, hprevious, phaseStep_eq, phaseStep_eq]
+    dsimp only
+    rw [hlast]
+
+/-- Overwriting simulator coin-table entry `i` before `start` does not change a suffix
+whose indices lie within the table: for `i<start` and `start+t≤q`, `phaseSuffix` on
+`List.ofFn ((FunFamily.blocks q c).symm (Function.update coins i fresh))` equals its value
+on `List.ofFn ((FunFamily.blocks q c).symm coins)`, with `c=S.coinLen |x|`.
+
+**Proof sketch.** Apply the suffix block-congruence reader. Each relevant block is a
+canonical block-table projection. Its index is at least `start`, hence different from `i`,
+so the public function-update reader leaves that entry unchanged. -/
+theorem phaseSuffix_update_before (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
+    (x z rV : List Bool) (q : ℕ) (coins : Fin q → S.Coins x.length)
+    (i : Fin q) (fresh : S.Coins x.length) (start : ℕ) (pre : List (List Bool)) (t : ℕ)
+    (hi : (i : ℕ) < start) (hend : start + t ≤ q) :
+    phaseSuffix S k B verifierFirst x z rV
+        (List.ofFn ((FunFamily.blocks q (S.coinLen x.length)).symm
+          (Function.update coins i fresh))) start pre t =
+      phaseSuffix S k B verifierFirst x z rV
+        (List.ofFn ((FunFamily.blocks q (S.coinLen x.length)).symm coins)) start pre t := by
+  have hread (F : Fin q → S.Coins x.length) (j : Fin q) :
+      coinBlock (S.coinLen x.length) j
+          (List.ofFn ((FunFamily.blocks q (S.coinLen x.length)).symm F)) =
+        List.ofFn (F j) := by
+    have hb := FunFamily.ofFn_blocks q (S.coinLen x.length)
+      ((FunFamily.blocks q (S.coinLen x.length)).symm F) j
+    rw [Equiv.apply_symm_apply] at hb
+    exact (coinBlock_eq _ _ _).trans hb.symm
+  apply phaseSuffix_congr_blocks
+  intro j hlo hhi
+  have hj : j < q := lt_of_lt_of_le hhi hend
+  have hne : (⟨j, hj⟩ : Fin q) ≠ i := by
+    intro he
+    have hval := congrArg Fin.val he
+    change j = (i : ℕ) at hval
+    omega
+  rw [hread _ ⟨j, hj⟩, hread _ ⟨j, hj⟩]
+  exact congrArg List.ofFn (Function.update_of_ne hne fresh coins)
+
+end TCSlib.Cryptography.SequentialZK
diff --git a/TCSlib/Cryptography/Composability/SequentialZK/SuffixMachine.lean b/TCSlib/Cryptography/Composability/SequentialZK/SuffixMachine.lean
new file mode 100644
index 000000000..0212ec55a
--- /dev/null
+++ b/TCSlib/Cryptography/Composability/SequentialZK/SuffixMachine.lean
@@ -0,0 +1,343 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Composability.SequentialZK.SimulatorMachine
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Polynomial-time normalized suffix simulation
+
+A simulated suffix starts from an arbitrary message prefix and phase index. The initial
+messages are preserved, and each further phase adds only bounded normalized messages and
+empty fillers. The semantic recursion is realized by the existing published counted-loop
+host; no new control host or hand-built machine is introduced. All word inputs are total,
+including malformed prefix encodings and phase indices beyond the supplied random tape.
+
+## Main definitions
+
+* `phaseStep`: one normalized phase appended to an arbitrary prefix.
+* `phaseSuffix`: a specified number of normalized phases after an arbitrary starting phase.
+
+## Main results
+
+* `length_encodeMsgs_phaseStep_le`, `length_encodeMsgs_phaseSuffix_le`: additive growth bounds.
+* `phaseStep_poly`, `phaseSuffix_poly`: polynomial-time normalized step and suffix.
+* `phaseSuffix_raw_poly`: total polynomial-time suffix from a decoded arbitrary prefix word.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §7.2.1, Theorem 175.1.
+* [Gol01] O. Goldreich, *Foundations of Cryptography, Volume I: Basic Tools*, Cambridge
+  University Press, 2001, §4.3.4.
+-/
+
+namespace TCSlib.Cryptography.SequentialZK
+
+open Complexity Turing
+
+/-- For simulator `S`, bounds `k,B`, orientation `verifierFirst`, input/auxiliary words `x,z`,
+fixed verifier tape `rV`, phase-tape source `rS`, phase `j`, and earlier prefix `pre`,
+`phaseStep` appends the normalized `S` output at `phaseAux z rV j pre` and `k(|x|)-p` empty
+fillers, with `p = if verifierFirst then k(|x|)/2 else (k(|x|)+1)/2`.
+The simulator uses global coin block `j`. [PS10, Theorem 175.1, simulated suffix update]. -/
+def phaseStep (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
+    (x z rV rS : List Bool) (j : ℕ) (pre : List (List Bool)) : List (List Bool) :=
+  let aux := phaseAux z rV j pre
+  let p := if verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2
+  pre ++ (normalizePhaseMsgs x aux p (B.eval x.length)
+    (S.runAtL x.length (pairEncode x aux) (coinBlock (S.coinLen x.length) j rS)) ++
+      List.replicate (k.eval x.length - p) [])
+
+/-- The equation for `phaseStep S k B verifierFirst x z rV rS j pre` is the earlier prefix
+followed by normalized real messages from simulator coin block `j` and then empty fillers.
+`phaseStep S k B verifierFirst x z rV rS j pre = let aux := phaseAux z rV j pre; let p := if
+verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2; pre ++ (normalizePhaseMsgs x
+aux p (B.eval x.length) (S.runAtL x.length (pairEncode x aux) (coinBlock (S.coinLen x.length) j rS))
+++ List.replicate (k.eval x.length - p) [])`. -/
+theorem phaseStep_eq (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
+    (x z rV rS : List Bool) (j : ℕ) (pre : List (List Bool)) :
+    phaseStep S k B verifierFirst x z rV rS j pre =
+      let aux := phaseAux z rV j pre
+      let p := if verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2
+      pre ++ (normalizePhaseMsgs x aux p (B.eval x.length)
+        (S.runAtL x.length (pairEncode x aux) (coinBlock (S.coinLen x.length) j rS)) ++
+          List.replicate (k.eval x.length - p) []) := rfl
+
+/-- One normalized step increases the encoded prefix length by at most
+`k(|x|) * (2*B(|x|)+2)`, regardless of the earlier messages or simulator output.
+`(Strategy.encodeMsgs (phaseStep S k B verifierFirst x z rV rS j pre)).length ≤ (Strategy.encodeMsgs
+pre).length + k.eval x.length * (2 * B.eval x.length + 2)`.
+
+**Proof sketch.** The normalized real portion has `p` messages of at most `B` bits and the
+remaining `k-p` messages are empty. Their encoding lengths are bounded by `p(2B+2)` and
+`(k-p)(2B+2)`, whose sum is `k(2B+2)` because `p≤k`. The public encoding-append equation
+adds this bound to the unchanged initial encoding length. -/
+theorem length_encodeMsgs_phaseStep_le (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
+    (x z rV rS : List Bool) (j : ℕ) (pre : List (List Bool)) :
+    (Strategy.encodeMsgs (phaseStep S k B verifierFirst x z rV rS j pre)).length ≤
+      (Strategy.encodeMsgs pre).length + k.eval x.length * (2 * B.eval x.length + 2) := by
+  let p := if verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2
+  let aux := phaseAux z rV j pre
+  let raw := S.runAtL x.length (pairEncode x aux) (coinBlock (S.coinLen x.length) j rS)
+  have hreal := length_encodeMsgs_normalizePhaseMsgs_le x aux p (B.eval x.length) raw
+  have hfill := CommitmentLemmas.length_encodeMsgs_le
+    (List.replicate (k.eval x.length - p) ([] : List Bool)) (B.eval x.length)
+    (fun m hm => by
+      have he := (List.mem_replicate.mp hm).2
+      subst m
+      exact Nat.zero_le _)
+  rw [List.length_replicate] at hfill
+  have hp : p ≤ k.eval x.length := by
+    dsimp only [p]
+    cases verifierFirst <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega
+  have hpk : p + (k.eval x.length - p) = k.eval x.length := by omega
+  have hsum : p * (2 * B.eval x.length + 2) +
+      (k.eval x.length - p) * (2 * B.eval x.length + 2) =
+        k.eval x.length * (2 * B.eval x.length + 2) := by rw [← Nat.add_mul, hpk]
+  simp only [phaseStep_eq, CommitmentLemmas.encodeMsgs_append, List.length_append]
+  dsimp only [p, aux, raw] at hreal hfill hsum
+  omega
+
+/-- For uniform `S`, fixed `k,B,verifierFirst`, polynomial-time words `X,Z,RV,RS`, a unary
+polynomial-time phase `J`, and a message family `H` with polynomial-time encoding, the
+normalized update is polynomial-time: `w ↦ encodeMsgs (phaseStep S k B verifierFirst
+(X w) (Z w) (RV w) (RS w) (J w) (H w))`. No message bound on `H` is required.
+[PS10, Theorem 175.1, simulated-suffix step].
+`PolyTimeComputable fun w => Strategy.encodeMsgs (phaseStep S k B verifierFirst (X w) (Z w) (RV w)
+(RS w) (J w) (H w))`.
+
+**Proof sketch.** Assemble the phase auxiliary word from the input functions and encoded
+prefix, cut out global simulator coin block `J`, and run the original uniform simulator's
+polynomial-time output. Apply the published canonical phase normalizer. Unary arithmetic
+computes the real/filler slot counts; the existing counted emitter encodes the empty fillers.
+Concatenate the unchanged input encoding and both new encodings using the public append
+reader. This is a polynomial-time leaf, with no iteration host construction. -/
+theorem phaseStep_poly (S : NUPPT) (hS : S.Uniform) (k B : PolyExpr)
+    (verifierFirst : Bool) {X Z RV RS : List Bool → List Bool} {J : List Bool → ℕ}
+    {H : List Bool → List (List Bool)}
+    (hX : PolyTimeComputable X) (hZ : PolyTimeComputable Z)
+    (hRV : PolyTimeComputable RV) (hRS : PolyTimeComputable RS)
+    (hJ : PolyTimeComputable fun w => List.replicate (J w) true)
+    (hH : PolyTimeComputable fun w => Strategy.encodeMsgs (H w)) :
+    PolyTimeComputable fun w => Strategy.encodeMsgs
+      (phaseStep S k B verifierFirst (X w) (Z w) (RV w) (RS w) (J w) (H w)) := by
+  -- Assemble the known phase metadata, tape slice and one uniform simulator call.
+  have haux := phaseAux_poly hZ hRV hJ hH
+  have hcoins : PolyTimeComputable fun w =>
+      coinBlock (S.coinLen (X w).length) (J w) (RS w) := by
+    simpa only [NUPPT.coinLen_eq, List.length_replicate] using
+      GI.coinSlice_poly S.coins hX hJ hRS
+  have hlay := NUPPT.polyTimeComputable_layout (EncodingMachines.unaryLength_poly hX)
+    (hX.pairEncode haux) (polyTimeComputable_const []) hcoins
+  have hsim : PolyTimeComputable fun w =>
+      S.runAtL (X w).length (pairEncode (X w) (phaseAux (Z w) (RV w) (J w) (H w)))
+        (coinBlock (S.coinLen (X w).length) (J w) (RS w)) := by
+    refine (S.polyTimeComputable_output.comp hlay).congr fun w => ?_
+    rw [Function.comp_apply, NUPPT.runAtL_eq_output_layout, hS.advice_eq]
+  -- The canonical normalizer and empty-filler emitter provide the new message encoding.
+  have hK := EncodingMachines.unaryPolyOf_poly k (EncodingMachines.unaryLength_poly hX)
+  have hP : PolyTimeComputable fun w => List.replicate
+      (if verifierFirst then k.eval (X w).length / 2 else (k.eval (X w).length + 1) / 2) true := by
+    cases verifierFirst
+    · simpa only [EncodingMachines.divNum_eq] using EncodingMachines.divNum_poly
+        (EncodingMachines.unaryAdd_poly hK (EncodingMachines.unaryConst_poly 1))
+        (EncodingMachines.unaryConst_poly 2)
+    · simpa only [EncodingMachines.divNum_eq] using
+        EncodingMachines.divNum_poly hK (EncodingMachines.unaryConst_poly 2)
+  have hbits := EncodingMachines.unaryPolyOf_poly B (EncodingMachines.unaryLength_poly hX)
+  have hnorm := polyTimeComputable_encode_normalizePhaseMsgs hX haux hsim hP hbits
+  have hfill := encode_emptyMsgs_poly (EncodingMachines.unarySub_poly hK hP)
+  refine (hH.append (hnorm.append hfill)).congr fun w => ?_
+  rw [phaseStep_eq, CommitmentLemmas.encodeMsgs_append, CommitmentLemmas.encodeMsgs_append]
+
+/-- Starting from `pre0` at phase `start`, `phaseSuffix S k B verifierFirst x z rV rS start
+pre0 t` applies the normalized append update at phases `start, …, start+t-1`, reading those
+global coin blocks from `rS`. It is a mathematical sequence realized below by the existing
+published counted-loop host. [PS10, Theorem 175.1, normalized simulated suffix].
+`phaseSuffix S k B verifierFirst x z rV rS start pre0 t = match t with | 0 => pre0 | i + 1 =>
+phaseStep S k B verifierFirst x z rV rS (start + i) (phaseSuffix S k B verifierFirst x z rV rS start
+pre0 i)`. -/
+def phaseSuffix (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
+    (x z rV rS : List Bool) (start : ℕ) (pre0 : List (List Bool)) : ℕ → List (List Bool)
+  | 0 => pre0
+  | i + 1 => phaseStep S k B verifierFirst x z rV rS (start + i)
+      (phaseSuffix S k B verifierFirst x z rV rS start pre0 i)
+
+/-- At zero suffix phases, `phaseSuffix S k B verifierFirst x z rV rS start pre0 0 = pre0`. -/
+theorem phaseSuffix_zero (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
+    (x z rV rS : List Bool) (start : ℕ) (pre0 : List (List Bool)) :
+    phaseSuffix S k B verifierFirst x z rV rS start pre0 0 = pre0 := rfl
+
+/-- Suffix phase `i+1` applies `phaseStep` at global index `start+i` to the prefix after `i`
+steps: `phaseSuffix … (i+1) = phaseStep … (start+i) (phaseSuffix … i)`. -/
+theorem phaseSuffix_succ (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
+    (x z rV rS : List Bool) (start : ℕ) (pre0 : List (List Bool)) (i : ℕ) :
+    phaseSuffix S k B verifierFirst x z rV rS start pre0 (i + 1) =
+      phaseStep S k B verifierFirst x z rV rS (start + i)
+        (phaseSuffix S k B verifierFirst x z rV rS start pre0 i) := rfl
+
+/-- The exhaustive suffix equation returns `pre0` at zero and, at `i+1`, applies
+`phaseStep` at global index `start+i` to `phaseSuffix … i`.
+`phaseSuffix S k B verifierFirst x z rV rS start pre0 t = match t with | 0 => pre0 | i + 1 =>
+phaseStep S k B verifierFirst x z rV rS (start + i) (phaseSuffix S k B verifierFirst x z rV rS start
+pre0 i)`. -/
+theorem phaseSuffix_eq (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
+    (x z rV rS : List Bool) (start : ℕ) (pre0 : List (List Bool)) (t : ℕ) :
+    phaseSuffix S k B verifierFirst x z rV rS start pre0 t =
+      match t with
+      | 0 => pre0
+      | i + 1 => phaseStep S k B verifierFirst x z rV rS (start + i)
+          (phaseSuffix S k B verifierFirst x z rV rS start pre0 i) :=
+  match t with
+  | 0 => phaseSuffix_zero S k B verifierFirst x z rV rS start pre0
+  | i + 1 => phaseSuffix_succ S k B verifierFirst x z rV rS start pre0 i
+
+/-- For any initial prefix `pre0`, the suffix encoding grows by at most
+`t * k(|x|) * (2*B(|x|)+2)` beyond its initial encoded length. No bound is required on
+individual initial messages or on the starting phase index.
+`(Strategy.encodeMsgs (phaseSuffix S k B verifierFirst x z rV rS start pre0 t)).length ≤
+(Strategy.encodeMsgs pre0).length + t * k.eval x.length * (2 * B.eval x.length + 2)`. -/
+theorem length_encodeMsgs_phaseSuffix_le (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
+    (x z rV rS : List Bool) (start : ℕ) (pre0 : List (List Bool)) (t : ℕ) :
+    (Strategy.encodeMsgs (phaseSuffix S k B verifierFirst x z rV rS start pre0 t)).length ≤
+      (Strategy.encodeMsgs pre0).length + t * k.eval x.length * (2 * B.eval x.length + 2) := by
+  induction t with
+  | zero => rw [phaseSuffix_zero, Nat.zero_mul, Nat.zero_mul, Nat.add_zero]
+  | succ t ih =>
+    rw [phaseSuffix_succ]
+    have hstep := length_encodeMsgs_phaseStep_le S k B verifierFirst x z rV rS (start + t)
+      (phaseSuffix S k B verifierFirst x z rV rS start pre0 t)
+    rw [Nat.succ_mul, Nat.add_mul]
+    omega
+
+/-- For uniform `S`, fixed `k,B,verifierFirst`, polynomial-time words `X,Z,RV,RS`, unary
+polynomial-time starting phase/count `Start,Count`, and initial message family `H` with
+polynomial-time encoding, the entire suffix encoding is polynomial-time. There is no range
+premise on `Start,Count` and no bound on individual messages of `H`.
+[PS10, Theorem 175.1; Gol01, §4.3.4, efficient simulated suffix].
+`PolyTimeComputable fun w => Strategy.encodeMsgs (phaseSuffix S k B verifierFirst (X w) (Z w) (RV w)
+(RS w) (Start w) (H w) (Count w))`.
+
+**Proof sketch.** Use the published counted-loop host with encoded-prefix state and its
+existing unary counter `i`. The update is the polynomial-time leaf `phaseStep_poly`, at index
+`Start+i`, after canonically decoding the reached state. Induction identifies the state with
+the semantic suffix. Its additive encoding bound, together with polynomial output-length
+bounds for the initial encoding, unary count and common input, gives the existing host's
+polynomial orbit envelope. No new host or control machine is constructed. -/
+theorem phaseSuffix_poly (S : NUPPT) (hS : S.Uniform) (k B : PolyExpr)
+    (verifierFirst : Bool) {X Z RV RS : List Bool → List Bool}
+    {Start Count : List Bool → ℕ} {H : List Bool → List (List Bool)}
+    (hX : PolyTimeComputable X) (hZ : PolyTimeComputable Z)
+    (hRV : PolyTimeComputable RV) (hRS : PolyTimeComputable RS)
+    (hStart : PolyTimeComputable fun w => List.replicate (Start w) true)
+    (hCount : PolyTimeComputable fun w => List.replicate (Count w) true)
+    (hH : PolyTimeComputable fun w => Strategy.encodeMsgs (H w)) :
+    PolyTimeComputable fun w => Strategy.encodeMsgs
+      (phaseSuffix S k B verifierFirst (X w) (Z w) (RV w) (RS w) (Start w) (H w) (Count w)) := by
+  let upd : List Bool → List Bool := fun w => Strategy.encodeMsgs
+    (phaseStep S k B verifierFirst (X (pairFstD w)) (Z (pairFstD w))
+      (RV (pairFstD w)) (RS (pairFstD w))
+      (Start (pairFstD w) + (pairFstD (pairSndD w)).length)
+      (BinArith.decWords (pairSndD (pairSndD w))))
+  -- Instantiate the new leaf with the existing loop's input, counter and state projections.
+  have hXt : PolyTimeComputable fun w => X (pairFstD w) := hX.comp polyTimeComputable_pairFstD
+  have hZt : PolyTimeComputable fun w => Z (pairFstD w) := hZ.comp polyTimeComputable_pairFstD
+  have hRVt : PolyTimeComputable fun w => RV (pairFstD w) := hRV.comp polyTimeComputable_pairFstD
+  have hRSt : PolyTimeComputable fun w => RS (pairFstD w) := hRS.comp polyTimeComputable_pairFstD
+  have hJ := EncodingMachines.unaryAdd_poly (hStart.comp polyTimeComputable_pairFstD)
+    (EncodingMachines.unaryLength_poly
+      (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD))
+  have hcanonical := polyTimeComputable_encWords_decWords
+    (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
+  have hpre : PolyTimeComputable fun w =>
+      Strategy.encodeMsgs (BinArith.decWords (pairSndD (pairSndD w))) :=
+    hcanonical.congr fun w => (encodeMsgs_eq_encWords _).symm
+  have hupd : PolyTimeComputable upd :=
+    phaseStep_poly S hS k B verifierFirst hXt hZt hRVt hRSt hJ hpre
+  -- Every actual state is the canonical encoding of the mathematical suffix prefix.
+  have hclosed : ∀ w i,
+      EncodingMachines.loopState upd (fun w => Strategy.encodeMsgs (H w)) w i =
+        Strategy.encodeMsgs (phaseSuffix S k B verifierFirst
+          (X w) (Z w) (RV w) (RS w) (Start w) (H w) i) := by
+    intro w i
+    induction i with
+    | zero => rw [EncodingMachines.loopState_zero, phaseSuffix_zero]
+    | succ i ih =>
+      rw [EncodingMachines.loopState_succ]
+      dsimp only [upd]
+      simp only [pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]
+      rw [ih]
+      have hdec : BinArith.decWords (Strategy.encodeMsgs
+          (phaseSuffix S k B verifierFirst (X w) (Z w) (RV w) (RS w) (Start w) (H w) i)) =
+          phaseSuffix S k B verifierFirst (X w) (Z w) (RV w) (RS w) (Start w) (H w) i :=
+        (congrArg BinArith.decWords (encodeMsgs_eq_encWords _)).trans
+          (BinArith.decWords_encWords _)
+      rw [hdec, phaseSuffix_succ]
+  -- Add the initial encoding's polynomial size to the normalized suffix-growth envelope.
+  obtain ⟨CX, dX, hCX⟩ := hX.output_length_le
+  obtain ⟨CN, dN, hCN⟩ := hCount.output_length_le
+  obtain ⟨CH, dH, hCH⟩ := hH.output_length_le
+  let XP : PolyExpr := .normal CX dX
+  let bound : PolyExpr := .add (.normal CH dH)
+    (.mul (.mul (.normal CN dN) (k.subst XP))
+      (.add (.mul (.const 2) (B.subst XP)) (.const 2)))
+  have hloop := ColMachines.polyTimeComputable_loopState' hupd hH hCount bound
+    (fun w i hi => by
+      rw [hclosed]
+      have hx : (X w).length ≤ XP.eval w.length := by
+        simpa only [XP, PolyExpr.eval_normal] using hCX w
+      have hi' : i ≤ CN * (w.length + 1) ^ dN :=
+        hi.trans (by simpa only [List.length_replicate] using hCN w)
+      have hk := k.eval_mono hx
+      have hb := B.eval_mono hx
+      simp only [bound, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const,
+        PolyExpr.eval_normal, PolyExpr.eval_subst]
+      calc
+        _ ≤ (Strategy.encodeMsgs (H w)).length +
+            i * k.eval (X w).length * (2 * B.eval (X w).length + 2) :=
+          length_encodeMsgs_phaseSuffix_le S k B verifierFirst
+            (X w) (Z w) (RV w) (RS w) (Start w) (H w) i
+        _ ≤ CH * (w.length + 1) ^ dH + CN * (w.length + 1) ^ dN *
+            k.eval (XP.eval w.length) * (2 * B.eval (XP.eval w.length) + 2) :=
+          Nat.add_le_add (hCH w) (Nat.mul_le_mul (Nat.mul_le_mul hi' hk) (by omega)))
+  exact hloop.congr fun w => hclosed w _
+
+/-- For uniform `S`, fixed `k,B,verifierFirst`, polynomial-time words `X,Z,RV,RS,Raw`, and
+unary polynomial-time `Start,Count`, decode the arbitrary word `Raw w` as the initial prefix.
+The resulting suffix encoding is polynomial-time on every input, including malformed words
+and phase indices beyond the available tape.
+`PolyTimeComputable fun w => Strategy.encodeMsgs (phaseSuffix S k B verifierFirst (X w) (Z w) (RV w)
+(RS w) (Start w) (BinArith.decWords (Raw w)) (Count w))`. -/
+theorem phaseSuffix_raw_poly (S : NUPPT) (hS : S.Uniform) (k B : PolyExpr)
+    (verifierFirst : Bool) {X Z RV RS Raw : List Bool → List Bool}
+    {Start Count : List Bool → ℕ}
+    (hX : PolyTimeComputable X) (hZ : PolyTimeComputable Z)
+    (hRV : PolyTimeComputable RV) (hRS : PolyTimeComputable RS)
+    (hRaw : PolyTimeComputable Raw)
+    (hStart : PolyTimeComputable fun w => List.replicate (Start w) true)
+    (hCount : PolyTimeComputable fun w => List.replicate (Count w) true) :
+    PolyTimeComputable fun w => Strategy.encodeMsgs
+      (phaseSuffix S k B verifierFirst (X w) (Z w) (RV w) (RS w) (Start w)
+        (BinArith.decWords (Raw w)) (Count w)) :=
+  phaseSuffix_poly S hS k B verifierFirst hX hZ hRV hRS hStart hCount
+    ((polyTimeComputable_encWords_decWords hRaw).congr
+      (fun _ => (encodeMsgs_eq_encWords _).symm))
+
+/-- Starting at phase zero with empty prefix gives the whole-prefix semantics:
+`phaseSuffix S k B verifierFirst x z rV rS 0 [] t =
+phasePrefix S k B verifierFirst x z rV rS t`. -/
+theorem phaseSuffix_zero_nil (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
+    (x z rV rS : List Bool) (t : ℕ) :
+    phaseSuffix S k B verifierFirst x z rV rS 0 [] t =
+      phasePrefix S k B verifierFirst x z rV rS t := by
+  induction t with
+  | zero => rw [phaseSuffix_zero, phasePrefix_zero]
+  | succ t ih =>
+    rw [phaseSuffix_succ, ih, Nat.zero_add, phaseStep_eq, phasePrefix_succ]
+
+end TCSlib.Cryptography.SequentialZK
diff --git a/TCSlib/Cryptography/Composability/SequentialZK/VerifierPrefix.lean b/TCSlib/Cryptography/Composability/SequentialZK/VerifierPrefix.lean
new file mode 100644
index 000000000..f8e3e7eb4
--- /dev/null
+++ b/TCSlib/Cryptography/Composability/SequentialZK/VerifierPrefix.lean
@@ -0,0 +1,89 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Composability.SequentialZK.Congruence
+import TCSlib.Cryptography.Asymptotic.Adversary
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Earlier coin blocks determine an earlier padded execution
+
+## Main definitions
+
+This module introduces no definitions.
+
+## Main results
+
+* `Composability.exec_eq_of_verifier_blocks`: a padded verifier reads only the first `j`
+  coin blocks before move `2*k*j`, so tapes agreeing on those blocks have the same earlier
+  transcript against any prover.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  Theorem 175.1 (sequential composition and conditioning on earlier phases).
+-/
+
+namespace TCSlib.Cryptography.Composability
+
+/-- For prover `P`, padded verifier `S`, original verifier `V`, first-mover flag `vFirst`,
+inputs `x`, `y`, `z`, prover tape `rP`, verifier tapes `rV`, `rV2`, phase length `k`, phase
+count `q`, coin-block length `c`, cutoff `j < q`, and arbitrary terminal function `terminal`,
+suppose `S` follows the displayed padded-verifier equation and recovers the actual move
+index from its received-history length. If `coinBlock c i rV = coinBlock c i rV2` for all
+`i < j`, then
+`exec P S vFirst x y z rP rV (2*k*j) = exec P S vFirst x y z rP rV2 (2*k*j)`.
+[PS10, Theorem 175.1, earlier phases depend only on earlier coin blocks].
+
+**Proof sketch.** With zero real moves both executions are empty. Otherwise compare the
+replies on the source run's reached histories. At a verifier move `t < 2*k*j`, the recovered
+index implies twice the received-history length is at most `t+1`. Since `j < q`, this
+excludes the terminal history of length `q*k`. The phase index is `t/(2*k) < j`, so both
+tapes provide the same coin block. The padded-verifier equation therefore gives the same
+reply; prover replies agree because the prover tape is fixed. Reached-history execution
+congruence finishes the comparison. -/
+theorem exec_eq_of_verifier_blocks (P S V : Strategy) (vFirst : Bool)
+    (x y z rP rV rV2 : List Bool) (k q c j : ℕ)
+    (terminal : List Bool → List (List Bool) → List Bool)
+    (hnext : ∀ r hist, S.next x z r hist =
+      if hist.length = q * k then terminal r hist
+      else
+        let idx := if vFirst then 2 * hist.length else 2 * hist.length - 1
+        if idx % (2 * k) < k then
+          V.next x z (coinBlock c (idx / (2 * k)) r)
+            (hist.drop (idx / (2 * k) * k))
+        else [])
+    (hj : j < q)
+    (hindex : ∀ t < 2 * k * j, moverIsV vFirst t = true →
+      (if vFirst then 2 * (exec P S vFirst x y z rP rV t).2.length
+        else 2 * (exec P S vFirst x y z rP rV t).2.length - 1) = t)
+    (hblocks : ∀ i < j, coinBlock c i rV = coinBlock c i rV2) :
+    exec P S vFirst x y z rP rV (2 * k * j) =
+      exec P S vFirst x y z rP rV2 (2 * k * j) := by
+  by_cases hk : k = 0
+  · subst k
+    simp only [Nat.mul_zero, Nat.zero_mul, exec_zero]
+  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
+    apply exec_congr_reachable P S P S vFirst x y z rP rV rP rV2 (2 * k * j)
+    · intro _ _ _
+      rfl
+    · intro t ht hm
+      -- A pre-cutoff verifier move cannot already have the terminal history length.
+      have hi := hindex t ht hm
+      have hlen : 2 * (exec P S vFirst x y z rP rV t).2.length ≤ t + 1 := by
+        cases vFirst <;> simp only [Bool.false_eq_true, if_false, if_true] at hi <;> omega
+      have hne : (exec P S vFirst x y z rP rV t).2.length ≠ q * k := by
+        intro heq
+        rw [heq] at hlen
+        have hjk := Nat.mul_le_mul_right k hj
+        nlinarith
+      -- Only a block before j can contribute to this reply.
+      rw [hnext, hnext, if_neg hne, if_neg hne]
+      dsimp only
+      rw [hi, hblocks (t / (2 * k)) (Nat.div_lt_of_lt_mul ht)]
+
+end TCSlib.Cryptography.Composability
diff --git a/TCSlib/Cryptography/Composability/SequentialZK/WrappedVerifier.lean b/TCSlib/Cryptography/Composability/SequentialZK/WrappedVerifier.lean
new file mode 100644
index 000000000..5ae490c89
--- /dev/null
+++ b/TCSlib/Cryptography/Composability/SequentialZK/WrappedVerifier.lean
@@ -0,0 +1,220 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Composability.SequentialZK.NormalizationMachine
+import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.Efficiency
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# The fixed-tape phase verifier for sequential zero knowledge
+
+The phase wrapper of [PS10, Theorem 175.1] carries the original auxiliary input, one global
+verifier tape, the phase index and the earlier received-prover prefix in its auxiliary input.
+It invokes the original verifier on that fixed tape and the prefix followed by the current
+phase's received messages. The wrapper itself has zero random bits.
+
+## Main definitions
+
+* `phaseAux z r j pre`: the nested-pair auxiliary input for a phase.
+* `phaseVerifier V`: the deterministic phase wrapper of `V`.
+
+## Main results
+
+* `phaseAux_fields`, `phaseAux_prefix`: the auxiliary-input field readers.
+* `phaseAux_length`, `phaseAux_length_le`: exact and bounded auxiliary-input lengths.
+* `phaseAux_poly`: polynomial-time assembly of the auxiliary data.
+* `phaseVerifier_next_phaseAux`: the exact next-message equation on encoded phase data.
+* `phaseVerifier_efficient`: an efficient verifier has an efficient phase wrapper.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §7.2.1, Theorem 175.1.
+* [Gol01] O. Goldreich, *Foundations of Cryptography, Volume I: Basic Tools*, Cambridge
+  University Press, 2001, §4.3.4.
+-/
+
+namespace TCSlib.Cryptography.SequentialZK
+
+open Complexity Turing
+
+/-- For original auxiliary input `z`, verifier tape `r`, phase `j` and received prefix
+`pre`, the phase auxiliary word is `⟨z, ⟨r, ⟨1^j, encodeMsgs pre⟩⟩⟩`.
+[PS10, Theorem 175.1, phase-verifier auxiliary data].
+`phaseAux z r j pre = pairEncode z (pairEncode r (pairEncode (List.replicate j true)
+(Strategy.encodeMsgs pre)))`. -/
+def phaseAux (z r : List Bool) (j : ℕ) (pre : List (List Bool)) : List Bool :=
+  pairEncode z (pairEncode r (pairEncode (List.replicate j true) (Strategy.encodeMsgs pre)))
+
+/-- The equation for `phaseAux z r j pre` is the nested pair
+`pairEncode z (pairEncode r (pairEncode (List.replicate j true) (encodeMsgs pre)))`.
+`phaseAux z r j pre = pairEncode z (pairEncode r (pairEncode (List.replicate j true)
+(Strategy.encodeMsgs pre)))`. -/
+theorem phaseAux_eq (z r : List Bool) (j : ℕ) (pre : List (List Bool)) :
+    phaseAux z r j pre =
+      pairEncode z (pairEncode r (pairEncode (List.replicate j true)
+        (Strategy.encodeMsgs pre))) := rfl
+
+/-- The four projection fields of `phaseAux z r j pre` are, in order,
+`z`, `r`, `List.replicate j true`, and `Strategy.encodeMsgs pre`.
+`pairFstD (phaseAux z r j pre) = z ∧ pairFstD (pairSndD (phaseAux z r j pre)) = r ∧ pairFstD
+(pairSndD (pairSndD (phaseAux z r j pre))) = List.replicate j true ∧ pairSndD (pairSndD (pairSndD
+(phaseAux z r j pre))) = Strategy.encodeMsgs pre`. -/
+theorem phaseAux_fields (z r : List Bool) (j : ℕ) (pre : List (List Bool)) :
+    pairFstD (phaseAux z r j pre) = z ∧
+    pairFstD (pairSndD (phaseAux z r j pre)) = r ∧
+    pairFstD (pairSndD (pairSndD (phaseAux z r j pre))) = List.replicate j true ∧
+    pairSndD (pairSndD (pairSndD (phaseAux z r j pre))) = Strategy.encodeMsgs pre := by
+  simp only [phaseAux_eq, pairFstD_pairEncode, pairSndD_pairEncode, and_self]
+
+/-- The original auxiliary-input field is `pairFstD (phaseAux z r j pre) = z`. -/
+theorem phaseAux_z (z r : List Bool) (j : ℕ) (pre : List (List Bool)) :
+    pairFstD (phaseAux z r j pre) = z := (phaseAux_fields z r j pre).1
+
+/-- The fixed verifier tape is `pairFstD (pairSndD (phaseAux z r j pre)) = r`. -/
+theorem phaseAux_tape (z r : List Bool) (j : ℕ) (pre : List (List Bool)) :
+    pairFstD (pairSndD (phaseAux z r j pre)) = r := (phaseAux_fields z r j pre).2.1
+
+/-- The unary phase field has length `j`:
+`(pairFstD (pairSndD (pairSndD (phaseAux z r j pre)))).length = j`. -/
+theorem phaseAux_phase (z r : List Bool) (j : ℕ) (pre : List (List Bool)) :
+    (pairFstD (pairSndD (pairSndD (phaseAux z r j pre)))).length = j :=
+  (congrArg List.length (phaseAux_fields z r j pre).2.2.1).trans (List.length_replicate ..)
+
+/-- Decoding the prefix field recovers `pre`:
+`decWords (pairSndD (pairSndD (pairSndD (phaseAux z r j pre)))) = pre`. -/
+theorem phaseAux_prefix (z r : List Bool) (j : ℕ) (pre : List (List Bool)) :
+    BinArith.decWords (pairSndD (pairSndD (pairSndD (phaseAux z r j pre)))) = pre :=
+  (congrArg BinArith.decWords (phaseAux_fields z r j pre).2.2.2).trans
+    ((congrArg BinArith.decWords (encodeMsgs_eq_encWords pre)).trans
+      (BinArith.decWords_encWords pre))
+
+/-- The phase wrapper of `V` runs on original input `x`, the first auxiliary field as `z`,
+the second as fixed tape, and the decoded prefix followed by its current received history.
+Its own random-tape polynomial is `PolyExpr.const 0`.
+[PS10, Theorem 175.1; Gol01, §4.3.4, the fixed-prefix phase verifier].
+`phaseVerifier V = { next := fun x aux _ hist => V.next x (pairFstD aux) (pairFstD (pairSndD aux))
+(BinArith.decWords (pairSndD (pairSndD (pairSndD aux))) ++ hist), coins := .const 0 }`. -/
+def phaseVerifier (V : Strategy) : Strategy where
+  next x aux _ hist :=
+    V.next x (pairFstD aux) (pairFstD (pairSndD aux))
+      (BinArith.decWords (pairSndD (pairSndD (pairSndD aux))) ++ hist)
+  coins := .const 0
+
+/-- The complete strategy equation is `phaseVerifier V = ⟨next, PolyExpr.const 0⟩`, where
+`next x aux r hist = V.next x (pairFstD aux) (pairFstD (pairSndD aux))
+(decWords (pairSndD (pairSndD (pairSndD aux))) ++ hist)`. -/
+theorem phaseVerifier_eq (V : Strategy) :
+    phaseVerifier V =
+      { next := fun x aux _ hist =>
+          V.next x (pairFstD aux) (pairFstD (pairSndD aux))
+            (BinArith.decWords (pairSndD (pairSndD (pairSndD aux))) ++ hist)
+        coins := .const 0 } := rfl
+
+/-- The coin polynomial of `phaseVerifier V` is `PolyExpr.const 0`.
+`(phaseVerifier V).coins = .const 0`. -/
+theorem phaseVerifier_coins (V : Strategy) : (phaseVerifier V).coins = .const 0 := rfl
+
+/-- For `V, x, aux, r, hist`, the next message of the phase wrapper is
+`V.next x (pairFstD aux) (pairFstD (pairSndD aux)) (decWords (snd (snd (snd aux))) ++ hist)`.
+`(phaseVerifier V).next x aux r hist = V.next x (pairFstD aux) (pairFstD (pairSndD aux))
+(BinArith.decWords (pairSndD (pairSndD (pairSndD aux))) ++ hist)`. -/
+theorem phaseVerifier_next (V : Strategy) (x aux r : List Bool) (hist : List (List Bool)) :
+    (phaseVerifier V).next x aux r hist =
+      V.next x (pairFstD aux) (pairFstD (pairSndD aux))
+        (BinArith.decWords (pairSndD (pairSndD (pairSndD aux))) ++ hist) := rfl
+
+/-- At every input length `n`, `(phaseVerifier V).coinLen n = 0`. -/
+theorem phaseVerifier_coinLen (V : Strategy) (n : ℕ) : (phaseVerifier V).coinLen n = 0 :=
+  (Strategy.coinLen_eq (phaseVerifier V) n).trans
+    ((congrArg (fun q : PolyExpr => q.eval n) (phaseVerifier_coins V)).trans
+      (PolyExpr.eval_const 0 n))
+
+/-- For `z, r, j, pre`, the exact auxiliary-word length is
+`(phaseAux z r j pre).length = 2|z| + 2|r| + 2j + |encodeMsgs pre| + 6`. -/
+theorem phaseAux_length (z r : List Bool) (j : ℕ) (pre : List (List Bool)) :
+    (phaseAux z r j pre).length =
+      2 * z.length + 2 * r.length + 2 * j + (Strategy.encodeMsgs pre).length + 6 := by
+  rw [phaseAux_eq, length_pairEncode, length_pairEncode, length_pairEncode,
+    List.length_replicate]
+  omega
+
+/-- For verifier `V`, input `x`, original auxiliary input `z`, fixed tape `r`, phase `j`,
+earlier prefix `pre`, wrapper tape `s` and current history `hist`,
+`(phaseVerifier V).next x (phaseAux z r j pre) s hist = V.next x z r (pre ++ hist)`.
+[PS10, Theorem 175.1; Gol01, §4.3.4, the fixed-prefix phase verifier]. -/
+theorem phaseVerifier_next_phaseAux (V : Strategy) (x z r : List Bool) (j : ℕ)
+    (pre : List (List Bool)) (s : List Bool) (hist : List (List Bool)) :
+    (phaseVerifier V).next x (phaseAux z r j pre) s hist = V.next x z r (pre ++ hist) := by
+  rw [phaseVerifier_next, phaseAux_z, phaseAux_tape, phaseAux_prefix]
+
+/-- If `V` is efficient, its fixed-tape phase wrapper is efficient:
+`V.Efficient → (phaseVerifier V).Efficient`.
+[PS10, Theorem 175.1; Gol01, §4.3.4, efficiency of the phase verifier].
+
+**Proof sketch.** Take the uniform machine computing `V`. The new machine reads the original
+auxiliary input and fixed random tape from projection fields. It canonically reencodes the
+total decoded prefix with the published word-list map, appends the encoding of the current
+history, assembles the original machine's layout, and runs its polynomial-time output.
+The encoding of a concatenated history is the concatenation of its encodings, so the exact
+next-message equation holds on every auxiliary word, including malformed encodings.
+The machine uses the wrapper's zero coin polynomial. -/
+theorem phaseVerifier_efficient {V : Strategy} (hV : V.Efficient) :
+    (phaseVerifier V).Efficient := by
+  obtain ⟨A, hA, _, hnext⟩ := (Strategy.efficient_iff V).1 hV
+  -- Read the fixed data and canonically reencode the total prefix decoder.
+  have hz := polyTimeComputable_pairFstD.comp GI.argZ_poly
+  have hr := polyTimeComputable_pairFstD.comp
+    (polyTimeComputable_pairSndD.comp GI.argZ_poly)
+  have hraw := polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp
+    (polyTimeComputable_pairSndD.comp GI.argZ_poly))
+  have hprefix := polyTimeComputable_encWords_decWords hraw
+  have hmsgs := hprefix.append GI.argM_poly
+  have hlay := NUPPT.polyTimeComputable_layout
+    (EncodingMachines.unaryLength_poly GI.argX_poly)
+    ((GI.argX_poly.pairEncode hz).pairEncode hmsgs) (polyTimeComputable_const []) hr
+  let F : List Bool → List Bool := fun w =>
+    A.output (NUPPT.layout (List.replicate (GI.argX w).length true)
+      (pairEncode (pairEncode (GI.argX w) (pairFstD (GI.argZ w)))
+        (BinArith.encWords (BinArith.decWords
+          (pairSndD (pairSndD (pairSndD (GI.argZ w))))) ++ GI.argM w)) []
+      (pairFstD (pairSndD (GI.argZ w))))
+  have hF : PolyTimeComputable F := A.polyTimeComputable_output.comp hlay
+  -- The public strategy and encoding readers identify every actual activation.
+  apply GI.efficient_of_polyTime (phaseVerifier V) hF
+  intro x aux r hist
+  dsimp only [F]
+  rw [GI.argX_ilayout, GI.argZ_ilayout, GI.argM_ilayout]
+  rw [phaseVerifier_next, hnext, Strategy.ofNUPPT_next, NUPPT.runAtL_eq_output_layout,
+    hA.advice_eq, CommitmentLemmas.encodeMsgs_append,
+    encodeMsgs_eq_encWords (BinArith.decWords (pairSndD (pairSndD (pairSndD aux))))]
+
+/-- For polynomial-time words `Z, R`, a unary polynomial-time phase `J`, and a history
+family `H` whose encoding is polynomial-time, `w ↦ phaseAux (Z w) (R w) (J w) (H w)` is
+polynomial-time.
+`PolyTimeComputable fun w => phaseAux (Z w) (R w) (J w) (H w)`. -/
+theorem phaseAux_poly {Z R : List Bool → List Bool} {J : List Bool → ℕ}
+    {H : List Bool → List (List Bool)}
+    (hZ : PolyTimeComputable Z) (hR : PolyTimeComputable R)
+    (hJ : PolyTimeComputable fun w => List.replicate (J w) true)
+    (hH : PolyTimeComputable fun w => Strategy.encodeMsgs (H w)) :
+    PolyTimeComputable fun w => phaseAux (Z w) (R w) (J w) (H w) := by
+  refine (hZ.pairEncode (hR.pairEncode (hJ.pairEncode hH))).congr fun w => ?_
+  rw [phaseAux_eq]
+
+/-- For `z, r, j, pre, slots, B`, if `pre` has at most `slots` messages of at most `B` bits,
+then `(phaseAux z r j pre).length ≤ 2|z| + 2|r| + 2j + slots*(2B+2) + 6`. -/
+theorem phaseAux_length_le (z r : List Bool) (j : ℕ) (pre : List (List Bool))
+    (slots B : ℕ) (hcount : pre.length ≤ slots) (hB : ∀ m ∈ pre, m.length ≤ B) :
+    (phaseAux z r j pre).length ≤
+      2 * z.length + 2 * r.length + 2 * j + slots * (2 * B + 2) + 6 := by
+  rw [phaseAux_length]
+  have henc := CommitmentLemmas.length_encodeMsgs_le pre B hB
+  have hslots := Nat.mul_le_mul_right (2 * B + 2) hcount
+  omega
+
+end TCSlib.Cryptography.SequentialZK
diff --git a/TCSlib/Cryptography/ZeroKnowledge/Defs.lean b/TCSlib/Cryptography/ZeroKnowledge/Defs.lean
index cb6a212b6..9852e7b62 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/Defs.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/Defs.lean
@@ -183,6 +183,17 @@ def StatZK (π : Protocol) (R : List Bool → List Bool → Prop) (δ : ℕ →
   ∀ V' : Strategy, V'.Efficient → ∃ S : NUPPT, S.Uniform ∧ ∀ x y z, R x y →
     StatClose (fun r => ((π.withV V').viewV x y z r).encode) (S.simulate x z) (δ x.length)
 
+/-- Statistical zero-knowledge is equivalent to the simulator property: for every efficient
+verifier `V'` there is a uniform simulator `S` with statistical error at most `δ(|x|)` on
+`(x, z)` for every witness `y` satisfying `R x y`. [PS10, §4.6].
+`StatZK π R δ ↔ ∀ V' : Strategy, V'.Efficient → ∃ S : NUPPT, S.Uniform ∧ ∀ x y z, R x y → StatClose
+(fun r => ((π.withV V').viewV x y z r).encode) (S.simulate x z) (δ x.length)`. -/
+theorem StatZK_iff (π : Protocol) (R : List Bool → List Bool → Prop) (δ : ℕ → ℝ) :
+    StatZK π R δ ↔ ∀ V' : Strategy, V'.Efficient →
+      ∃ S : NUPPT, S.Uniform ∧ ∀ x y z, R x y →
+        StatClose (fun r => ((π.withV V').viewV x y z r).encode)
+          (S.simulate x z) (δ x.length) := Iff.rfl
+
 /-- Perfect zero-knowledge [PS10, §4.6, "perfect zero-knowledge"] (Def-122.a): statistical
 zero-knowledge with error `0`, i.e. the simulator's output has exactly the law of the view.
 

## ===== TCSlib/Cryptography/Composability/SequentialZK.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.ZeroKnowledge.Defs
import TCSlib.Cryptography.ZeroKnowledge.InteractiveProofs
import TCSlib.Cryptography.Composability.SequentialZK.Advice
import TCSlib.Cryptography.Composability.SequentialZK.BoundedMetadata
import TCSlib.Cryptography.Composability.SequentialZK.ComputationalAdvice
import TCSlib.Cryptography.Composability.SequentialZK.ComputationalHybrid
import TCSlib.Cryptography.Composability.SequentialZK.ComputationalPhaseBound
import TCSlib.Cryptography.Composability.SequentialZK.ComputationalReduction
import TCSlib.Cryptography.Composability.SequentialZK.ComputationalTransfer
import TCSlib.Cryptography.Composability.SequentialZK.Congruence
import TCSlib.Cryptography.Composability.SequentialZK.ContinuationProbability
import TCSlib.Cryptography.Composability.SequentialZK.Efficiency
import TCSlib.Cryptography.Composability.SequentialZK.EndpointSampling
import TCSlib.Cryptography.Composability.SequentialZK.ErrSoundness
import TCSlib.Cryptography.Composability.SequentialZK.ExecutionBounds
import TCSlib.Cryptography.Composability.SequentialZK.HybridRecursion
import TCSlib.Cryptography.Composability.SequentialZK.Normalization
import TCSlib.Cryptography.Composability.SequentialZK.NormalizationMachine
import TCSlib.Cryptography.Composability.SequentialZK.NormalizedStep
import TCSlib.Cryptography.Composability.SequentialZK.PaddedProverSpec
import TCSlib.Cryptography.Composability.SequentialZK.PhaseView
import TCSlib.Cryptography.Composability.SequentialZK.Phases
import TCSlib.Cryptography.Composability.SequentialZK.PrefixFolds
import TCSlib.Cryptography.Composability.SequentialZK.PrefixLaws
import TCSlib.Cryptography.Composability.SequentialZK.ProofTransfers
import TCSlib.Cryptography.Composability.SequentialZK.RealPhases
import TCSlib.Cryptography.Composability.SequentialZK.RealPrefixBounds
import TCSlib.Cryptography.Composability.SequentialZK.ReductionAdvantage
import TCSlib.Cryptography.Composability.SequentialZK.RepeatedSoundness
import TCSlib.Cryptography.Composability.SequentialZK.RepeatedVerifier
import TCSlib.Cryptography.Composability.SequentialZK.SimulatorMachine
import TCSlib.Cryptography.Composability.SequentialZK.Soundness
import TCSlib.Cryptography.Composability.SequentialZK.Statistical
import TCSlib.Cryptography.Composability.SequentialZK.StatisticalPostprocess
import TCSlib.Cryptography.Composability.SequentialZK.StatisticalPrefix
import TCSlib.Cryptography.Composability.SequentialZK.StatisticalRecursion
import TCSlib.Cryptography.Composability.SequentialZK.StatisticalTransfer
import TCSlib.Cryptography.Composability.SequentialZK.SuffixLaws
import TCSlib.Cryptography.Composability.SequentialZK.SuffixMachine
import TCSlib.Cryptography.Composability.SequentialZK.VerifierPrefix
import TCSlib.Cryptography.Composability.SequentialZK.WrappedVerifier
import TCSlib.Cryptography.Asymptotic.ReductionSupport

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Sequential composition of zero-knowledge proofs

[PS10, Theorem 175.1]: if `(P, V)` is a perfect or computational zero-knowledge proof for `L`
and `Q` is a polynomial, the protocol `(P_Q, V_Q)` that runs `(P, V)` on the common input `x`
`Q(|x|)` times in sequence, each time with fresh coins, is again a perfect or computational
zero-knowledge interactive proof.

**The construction** (`Protocol.seqRep`), on the interaction model of
`ZeroKnowledge/Interaction.lean` (D8): with `k = rounds(|x|)` moves of `π`, phase `j` occupies
the `2k` moves `2kj, …, 2kj + 2k − 1`.
- The first `k` moves of a phase are `π`'s; in the last `k` (**fillers**) the honest parties
  send `[]`. A phase thus has an even number of moves, so every phase starts with the same mover
  as `π` (`moverIsV_two_mul_add`), even when `k` is odd (the graph protocols have three
  messages). Each party moves exactly `k` times per phase.
- A party finds the global move from the number of messages it has received
  (`proverMoveIndex_exec`, `verifierMoveIndex_exec`), hence its phase `j` and position `t`.
  At a position `t < k` it runs `π`'s next-message function on the coin slice `j` of its tape
  (`coinBlock` from `Asymptotic/Adversary.lean`) and on the messages received in phase `j`
  (all of them real, since `t < k`).
- The coins of `P_Q` and `V_Q` are `Q` copies of `π`'s.
- `V_Q`'s verdict, on its complete history (`Q · k` messages), is `[true]` iff every phase's
  verdict, `V.next` on that phase's real messages, is `[true]`; otherwise `[false]`. When
  `π.verifierFirst = false`, `V_Q` makes the last move, and by the convention of D8 that move is
  its verdict (`outV_eq_getLast_of_moverIsV`); the filler position carries it, and nobody
  reads it.

**Deviations** (beyond D8, declared once here).
- **Filler moves**, as above: each phase is padded to `2k` moves; the honest parties' fillers
  are `[]` and are ignored.
- **Strict-PPT simulators and bounded abort retries** (ruling G02-#4, D8): zero-knowledge
  composes to zero-knowledge, and statistical error `δ` composes to `Q · δ`. The formal
  `PerfectZKAbort` premise is [Gol01, Definition 4.3.1]'s strict-PPT aborting formulation:
  abort probability at most `1/2`, and the exact real-view law conditioned on success.
  `PerfectZKAbort.statZK` runs this simulator on `n = |x|` independent fresh coin blocks,
  keeping the first non-aborting output. All retries abort with probability at most `2^{-n}`,
  giving statistical error `2^{-n}`; composition gives `Q(n) · 2^{-n}`. Each retry is already
  strict PPT. [PS10]'s expected-polynomial-time wording is a separate source convention;
  this bounded-retry argument does not assert that arbitrary expected-time truncation
  preserves an exact conditional output law.
- **Bounded prover messages** (`Protocol.ProverBounded`). Under D8, `Strategy.Efficient` bounds
  a verifier's work per activation in the total length of its input, not in `|x|`. A cheating
  `V_Q` may then double its message length in every phase. If the honest prover echoes the
  verifier's messages, which is zero-knowledge for one run, the views of `V_Q` grow like
  `2^{Q(|x|)}`, which no strict PPT simulator can output. The composition theorems therefore
  assume that the honest prover's messages on instances with witnesses have at most `B(|x|)`
  bits. The text's machines read only `t(|x|)` bits per message, so the issue does not arise
  there.
- **At least one phase** for soundness: with `Q(n) = 0`, `V_Q` accepts everything, so the
  interactive-proof statement assumes `1 ≤ Q(n)`.

## Contents

* `SequentialZK.Advice`: uniform finite selectors.
* `SequentialZK.BoundedMetadata`: finite bounded phase advice.
* `SequentialZK.ComputationalAdvice`: uniform negligible selectors.
* `SequentialZK.ComputationalHybrid`: conditional computational gaps and endpoints.
* `SequentialZK.ComputationalPhaseBound`: a common negligible phase bound.
* `SequentialZK.ComputationalReduction`: efficient advised continuation machines.
* `SequentialZK.ComputationalTransfer`: computational zero-knowledge transfer.
* `SequentialZK.Congruence`: reached-history execution congruence.
* `SequentialZK.ContinuationProbability`: continuation acceptance and drift.
* `SequentialZK.Efficiency`: phase and verdict machines.
* `SequentialZK.EndpointSampling`: coin and view endpoint equivalences.
* `SequentialZK.ErrSoundness`: acceptance bounds from soundness.
* `SequentialZK.ExecutionBounds`: bounded real messages.
* `SequentialZK.HybridRecursion`: conditional finite hybrid bounds.
* `SequentialZK.Normalization`: bounded message slots.
* `SequentialZK.NormalizationMachine`: normalization machines.
* `SequentialZK.NormalizedStep`: one normalized phase comparison.
* `SequentialZK.PaddedProverSpec`: the repeated-prover contract.
* `SequentialZK.PhaseView`: canonical view validation.
* `SequentialZK.Phases`: fixed-prefix phase executions.
* `SequentialZK.PrefixFolds`: typed phase-prefix samplers.
* `SequentialZK.PrefixLaws`: phase-fold recursion equations.
* `SequentialZK.ProofTransfers`: bounded completeness transfer.
* `SequentialZK.RealPhases`: real and filler phase endpoints.
* `SequentialZK.RealPrefixBounds`: bounded actual real prefixes.
* `SequentialZK.ReductionAdvantage`: typed reduction comparisons.
* `SequentialZK.RepeatedSoundness`: the exact power soundness bound.
* `SequentialZK.RepeatedVerifier`: the repeated-verifier contract.
* `SequentialZK.SimulatorMachine`: the uniform normalized simulator.
* `SequentialZK.Soundness`: execution prefixes and adaptive probability.
* `SequentialZK.Statistical`: averaging and finite chains.
* `SequentialZK.StatisticalPostprocess`: statistical mapping and marginalization.
* `SequentialZK.StatisticalPrefix`: normalized prefix comparisons.
* `SequentialZK.StatisticalRecursion`: linear error accumulation.
* `SequentialZK.StatisticalTransfer`: statistical zero-knowledge transfer.
* `SequentialZK.SuffixLaws`: normalized suffix equations.
* `SequentialZK.SuffixMachine`: strict-PPT normalized suffix simulation.
* `SequentialZK.VerifierPrefix`: prefix tape dependence.
* `SequentialZK.WrappedVerifier`: the deterministic phase verifier.

## Main definitions

* `Composability.proverMoveIndex`, `Composability.verifierMoveIndex`,
  `Composability.proverMoves`: positions from message counts.
* `TCSlib.Cryptography.Protocol.seqProver`, `seqVerifier`, `seqRep`: the `Q`-fold sequential
  repetition.

## Main results

* `moverIsV_two_mul_add`, `countP_moverIsV`, `countP_not_moverIsV`, `exec_fst_length`,
  `exec_snd_length`, `proverMoveIndex_exec`, `verifierMoveIndex_exec`: the parties know their
  position.
* `Protocol.seqRep_exec_phase`: phase `j` of an honest execution of `π.seqRep Q` is an execution
  of `π` with the coin slices `j`.
* `ZK.seqRep` (Thm 175.1, proved): computational zero knowledge composes sequentially.
* `StatZK.seqRep` (proved): statistical error composes as `Q · δ`;
  `PerfectZK.seqRep` is proved from it at zero error.
* `PerfectZKAbort.seqRep`: the aborting case, derived from `PerfectZKAbort.statZK` and
  `StatZK.seqRep`, with error `Q(n) · 2^{-n}`.
* `InteractiveProof.seqRep` (proved): sequential repetition with at least one phase preserves
  interactive proofs, using the same negligible soundness bound.
* `InteractiveProofErr.seqRep`, `EfficientProverProofErr.seqRep` (proved): sequential
  repetition multiplies the soundness error, `s ↦ s^Q` (ruling G3-7d, for the text's form of
  Thm 124.1).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.2.1, Theorem 175.1 and its proof sketch (book pp. 175–176).
* [Gol01] O. Goldreich, *Foundations of Cryptography, Volume I: Basic Tools*, Cambridge University
  Press, 2001, §4.3.4 (sequential composition) and Definition 4.3.1 (perfect zero-knowledge
  with abort).
-/

namespace TCSlib.Cryptography

open Complexity Turing

namespace Composability

/-! ### Positions -/

/-- The global index of a prover move, from the number `c` of messages it has received: with
the verifier first, the prover moves at the odd positions `2c − 1`; otherwise at `2c`. -/
def proverMoveIndex (vFirst : Bool) (c : ℕ) : ℕ := if vFirst then 2 * c - 1 else 2 * c

/-- The prover move index is `2c-1` when the verifier starts and `2c` otherwise. -/
theorem proverMoveIndex_eq (vFirst : Bool) (c : ℕ) :
    proverMoveIndex vFirst c = if vFirst then 2 * c - 1 else 2 * c := rfl

/-- The global index of a verifier move, from the number `c` of messages it has received. -/
def verifierMoveIndex (vFirst : Bool) (c : ℕ) : ℕ := if vFirst then 2 * c else 2 * c - 1

/-- The verifier move index is `2c` when the verifier starts and `2c-1` otherwise. -/
theorem verifierMoveIndex_eq (vFirst : Bool) (c : ℕ) :
    verifierMoveIndex vFirst c = if vFirst then 2 * c else 2 * c - 1 := rfl

/-- The number of prover moves among the first `k` moves. -/
def proverMoves (vFirst : Bool) (k : ℕ) : ℕ := (List.range k).countP fun t => !moverIsV vFirst t

/-- Prover moves are counted among the positions below the move budget. -/
theorem proverMoves_eq (vFirst : Bool) (k : ℕ) :
    proverMoves vFirst k = (List.range k).countP fun t => !moverIsV vFirst t := rfl

/-- The mover pattern has period `2`. -/
theorem moverIsV_two_mul_add (vFirst : Bool) (m t : ℕ) :
    moverIsV vFirst (2 * m + t) = moverIsV vFirst t := by
  cases vFirst <;> simp [moverIsV_true, moverIsV_false]

/-- The number of verifier moves among the first `g` moves. -/
theorem countP_moverIsV (vFirst : Bool) (g : ℕ) :
    (List.range g).countP (fun t => moverIsV vFirst t) =
      if vFirst then (g + 1) / 2 else g / 2 := by
  induction g with
  | zero => cases vFirst <;> simp
  | succ g ih =>
    rw [List.range_succ, List.countP_append, ih]
    cases vFirst <;> simp [moverIsV_true, moverIsV_false] <;> split_ifs <;> omega

/-- The number of prover moves among the first `g` moves. -/
theorem countP_not_moverIsV (vFirst : Bool) (g : ℕ) :
    (List.range g).countP (fun t => !moverIsV vFirst t) =
      if vFirst then g / 2 else (g + 1) / 2 := by
  induction g with
  | zero => cases vFirst <;> simp
  | succ g ih =>
    rw [List.range_succ, List.countP_append, ih]
    cases vFirst <;> simp [moverIsV_true, moverIsV_false] <;> split_ifs <;> omega

/-- After `g` moves the prover has received one message per verifier move. -/
theorem exec_fst_length (P V : Strategy) (vFirst : Bool) (x zP zV rP rV : List Bool) (g : ℕ) :
    (exec P V vFirst x zP zV rP rV g).1.length =
      (List.range g).countP (fun t => moverIsV vFirst t) := by
  induction g with
  | zero => simp
  | succ g ih =>
    rw [exec_succ, List.range_succ, List.countP_append]
    by_cases h : moverIsV vFirst g = true <;> simp [h, ih]

/-- After `g` moves the verifier has received one message per prover move. -/
theorem exec_snd_length (P V : Strategy) (vFirst : Bool) (x zP zV rP rV : List Bool) (g : ℕ) :
    (exec P V vFirst x zP zV rP rV g).2.length =
      (List.range g).countP (fun t => !moverIsV vFirst t) := by
  induction g with
  | zero => simp
  | succ g ih =>
    rw [exec_succ, List.range_succ, List.countP_append]
    by_cases h : moverIsV vFirst g = true <;> simp [h, ih]

/-- **The prover knows the global move**: when it moves at move `g`, the number of messages it
has received gives `g` back. -/
theorem proverMoveIndex_exec (P V : Strategy) (vFirst : Bool) (x zP zV rP rV : List Bool)
    (g : ℕ) (hg : moverIsV vFirst g = false) :
    proverMoveIndex vFirst (exec P V vFirst x zP zV rP rV g).1.length = g := by
  rw [exec_fst_length, countP_moverIsV]
  cases vFirst <;> simp [moverIsV_true, moverIsV_false, proverMoveIndex] at hg ⊢ <;> omega

/-- **The verifier knows the global move**: when it moves at move `g`, the number of messages
it has received gives `g` back. -/
theorem verifierMoveIndex_exec (P V : Strategy) (vFirst : Bool) (x zP zV rP rV : List Bool)
    (g : ℕ) (hg : moverIsV vFirst g = true) :
    verifierMoveIndex vFirst (exec P V vFirst x zP zV rP rV g).2.length = g := by
  rw [exec_snd_length, countP_not_moverIsV]
  cases vFirst <;> simp [moverIsV_true, moverIsV_false, verifierMoveIndex] at hg ⊢ <;> omega

/-- For `P,V,vFirst,x,zP,zV,rP,rV,k,j`, each party has received exactly `j*k` messages
at move `2*k*j`: both components of `exec P V vFirst x zP zV rP rV (2*k*j)` have length
`j*k`. [PS10, Theorem 175.1, padded-phase boundaries].
`(exec P V vFirst x zP zV rP rV (2 * k * j)).1.length = j * k ∧ (exec P V vFirst x zP zV rP rV (2 *
k * j)).2.length = j * k`. -/
theorem exec_boundary_lengths (P V : Strategy) (vFirst : Bool)
    (x zP zV rP rV : List Bool) (k j : ℕ) :
    (exec P V vFirst x zP zV rP rV (2 * k * j)).1.length = j * k ∧
      (exec P V vFirst x zP zV rP rV (2 * k * j)).2.length = j * k := by
  constructor
  · rw [exec_fst_length, countP_moverIsV,
      show 2 * k * j = 2 * (j * k) by ring]
    cases vFirst <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega
  · rw [exec_snd_length, countP_not_moverIsV,
      show 2 * k * j = 2 * (j * k) by ring]
    cases vFirst <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega

end Composability

open Composability

namespace Protocol

/-! ### The sequential repetition -/

/-- The prover `P_Q`: at a real position of phase `j`, `π.P` on the coin slice `j` and the
messages received in phase `j`; at a filler position, `[]`. Its coins are `Q` copies of
`π.P`'s. -/
@[simps (config := { isSimp := false }) coins next]
def seqProver (π : Protocol) (Q : PolyExpr) : Strategy where
  next x y r hist :=
    if proverMoveIndex π.verifierFirst hist.length % (2 * π.rounds.eval x.length) <
        π.rounds.eval x.length then
      π.P.next x y
        (coinBlock (π.P.coinLen x.length)
          (proverMoveIndex π.verifierFirst hist.length / (2 * π.rounds.eval x.length)) r)
        (hist.drop (proverMoveIndex π.verifierFirst hist.length /
          (2 * π.rounds.eval x.length) * π.rounds.eval x.length))
    else []
  coins := .mul Q π.P.coins

/-- The verdict of `V_Q` on its complete history: `[true]` iff for every phase `j < Q`, `π.V`
on the coin slice `j` and the real messages of phase `j` outputs `[true]`. -/
def seqVerdict (π : Protocol) (Q : ℕ) (x z r : List Bool) (hist : List (List Bool)) :
    List Bool :=
  if (List.range Q).all (fun j => decide (π.V.next x z (coinBlock (π.V.coinLen x.length) j r)
      ((hist.drop (j * π.rounds.eval x.length)).take
        (proverMoves π.verifierFirst (π.rounds.eval x.length))) = [true]))
  then [true] else [false]

/-- The repeated verdict is true exactly when every phase's original verdict is true. -/
theorem seqVerdict_eq (π : Protocol) (Q : ℕ) (x z r : List Bool)
    (hist : List (List Bool)) :
    seqVerdict π Q x z r hist =
      if (List.range Q).all (fun j => decide
        (π.V.next x z (coinBlock (π.V.coinLen x.length) j r)
          ((hist.drop (j * π.rounds.eval x.length)).take
            (proverMoves π.verifierFirst (π.rounds.eval x.length))) = [true]))
      then [true] else [false] := rfl

/-- The verifier `V_Q`: on its complete history (`Q · k` messages received) its verdict
(`seqVerdict`); otherwise, at a real position of phase `j`, `π.V` on the coin slice `j` and the
messages received in phase `j`; at a filler position, `[]`. Its coins are `Q` copies of
`π.V`'s. -/
@[simps (config := { isSimp := false }) coins next]
def seqVerifier (π : Protocol) (Q : PolyExpr) : Strategy where
  next x z r hist :=
    if hist.length = Q.eval x.length * π.rounds.eval x.length then
      seqVerdict π (Q.eval x.length) x z r hist
    else if verifierMoveIndex π.verifierFirst hist.length % (2 * π.rounds.eval x.length) <
        π.rounds.eval x.length then
      π.V.next x z
        (coinBlock (π.V.coinLen x.length)
          (verifierMoveIndex π.verifierFirst hist.length / (2 * π.rounds.eval x.length)) r)
        (hist.drop (verifierMoveIndex π.verifierFirst hist.length /
          (2 * π.rounds.eval x.length) * π.rounds.eval x.length))
    else []
  coins := .mul Q π.V.coins

/-- **The `Q`-fold sequential repetition** of `π` [PS10, Theorem 175.1, `(P_Q, V_Q)`]:
`Q(|x|)` phases of `2 · rounds(|x|)` moves, each running `π` on `x` with fresh coins and then
filler moves. -/
@[simps (config := { isSimp := false }) P V rounds verifierFirst]
def seqRep (π : Protocol) (Q : PolyExpr) : Protocol where
  P := π.seqProver Q
  V := π.seqVerifier Q
  rounds := .mul Q (.mul (.const 2) π.rounds)
  verifierFirst := π.verifierFirst

/-- The number of moves of the repetition. -/
theorem seqRep_rounds_eval (π : Protocol) (Q : PolyExpr) (n : ℕ) :
    (π.seqRep Q).rounds.eval n = 2 * π.rounds.eval n * Q.eval n := by
  simp [seqRep, PolyExpr.eval_mul, PolyExpr.eval_const]
  ring

/-- The repeated prover keeps the message bound: `π.ProverBounded R B` implies
`(π.seqRep Q).ProverBounded R B`, since every real reply is an original reply and every
filler reply is empty. [PS10, Theorem 175.1]. -/
theorem ProverBounded.seqRep {π : Protocol} {R : List Bool → List Bool → Prop}
    {B : PolyExpr} (hB : π.ProverBounded R B) (Q : PolyExpr) :
    (π.seqRep Q).ProverBounded R B := by
  rw [proverBounded_iff] at hB ⊢
  intro x y r hist hxy
  rw [seqRep_P, seqProver_next]
  split_ifs
  · exact hB x y _ _ hxy
  · exact Nat.zero_le _

/-- **Phase `j` of an honest execution of the repetition is an execution of `π`** with the coin
slices `j`: after the `j` earlier phases and the `k` real moves of phase `j`, the messages each
party received in phase `j` are those it receives in `π` with those coins.

**Proof sketch.** Induction on the position `t ≤ k` in phase `j`, for the move `2kj + t`.
1. At `t = 0` each party has received exactly `jk` messages (`exec_fst_length`,
   `countP_moverIsV` with `2kj` moves), so both dropped lists are empty.
2. At a move `2kj + t` with `t < k`, the mover is `π`'s mover at `t` (`moverIsV_two_mul_add`).
   The mover recovers `2kj + t` from its message count (`proverMoveIndex_exec`,
   `verifierMoveIndex_exec`). So it computes `j` and `t < k`, and it runs `π`'s strategy on the
   slice `j` and on the messages of phase `j`, which equal `π`'s by the induction hypothesis.
   `V_Q` is not at its verdict: it has received fewer than `jk + k ≤ Qk` messages.
3. Appending the same message on both sides preserves the equation (`List.drop_append_of_le`,
   as at least `jk` messages precede it). -/
theorem seqRep_exec_phase (π : Protocol) (Q : PolyExpr) (x y z rP rV : List Bool) {j : ℕ}
    (hj : j < Q.eval x.length) :
    (exec (π.seqRep Q).P (π.seqRep Q).V π.verifierFirst x y z rP rV
        (2 * π.rounds.eval x.length * j + π.rounds.eval x.length)).1.drop
          (j * π.rounds.eval x.length) =
      (exec π.P π.V π.verifierFirst x y z (coinBlock (π.P.coinLen x.length) j rP)
        (coinBlock (π.V.coinLen x.length) j rV) (π.rounds.eval x.length)).1 ∧
    (exec (π.seqRep Q).P (π.seqRep Q).V π.verifierFirst x y z rP rV
        (2 * π.rounds.eval x.length * j + π.rounds.eval x.length)).2.drop
          (j * π.rounds.eval x.length) =
      (exec π.P π.V π.verifierFirst x y z (coinBlock (π.P.coinLen x.length) j rP)
        (coinBlock (π.V.coinLen x.length) j rV) (π.rounds.eval x.length)).2 := by
  set k := π.rounds.eval x.length with hk
  set vF := π.verifierFirst with hvF
  set sP := coinBlock (π.P.coinLen x.length) j rP
  set sV := coinBlock (π.V.coinLen x.length) j rV
  have hjk : (j + 1) * k ≤ Q.eval x.length * k := Nat.mul_le_mul_right _ hj
  have hjk' : (j + 1) * k = j * k + k := by ring
  have h2 : 2 * k * j = 2 * (j * k) := by ring
  suffices key : ∀ t, t ≤ k →
      (exec (π.seqRep Q).P (π.seqRep Q).V vF x y z rP rV (2 * k * j + t)).1.drop (j * k) =
        (exec π.P π.V vF x y z sP sV t).1 ∧
      (exec (π.seqRep Q).P (π.seqRep Q).V vF x y z rP rV (2 * k * j + t)).2.drop (j * k) =
        (exec π.P π.V vF x y z sP sV t).2 from key k le_rfl
  intro t
  induction t with
  | zero =>
    intro _
    constructor
    · rw [List.drop_eq_nil_of_le]
      · exact (congrArg Prod.fst (exec_zero π.P π.V vF x y z sP sV)).symm
      · rw [exec_fst_length, countP_moverIsV]
        cases vF <;> simp <;> omega
    · rw [List.drop_eq_nil_of_le]
      · exact (congrArg Prod.snd (exec_zero π.P π.V vF x y z sP sV)).symm
      · rw [exec_snd_length, countP_not_moverIsV]
        cases vF <;> simp <;> omega
  | succ t ih =>
    intro ht
    obtain ⟨ih₁, ih₂⟩ := ih (by omega)
    have htk : t < k := by omega
    have hl₁ : (exec (π.seqRep Q).P (π.seqRep Q).V vF x y z rP rV (2 * k * j + t)).1.length =
        j * k + (exec π.P π.V vF x y z sP sV t).1.length := by
      rw [exec_fst_length, exec_fst_length, countP_moverIsV, countP_moverIsV]
      cases vF <;> simp <;> omega
    have hl₂ : (exec (π.seqRep Q).P (π.seqRep Q).V vF x y z rP rV (2 * k * j + t)).2.length =
        j * k + (exec π.P π.V vF x y z sP sV t).2.length := by
      rw [exec_snd_length, exec_snd_length, countP_not_moverIsV, countP_not_moverIsV]
      cases vF <;> simp <;> omega
    have hle₂ : (exec π.P π.V vF x y z sP sV t).2.length ≤ t := by
      rw [exec_snd_length]
      exact (List.countP_le_length).trans (by simp)
    have hmv : moverIsV vF (2 * k * j + t) = moverIsV vF t := by
      rw [show 2 * k * j + t = 2 * (k * j) + t by ring]
      exact moverIsV_two_mul_add _ _ _
    have hmod : (2 * k * j + t) % (2 * k) = t := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    have hdiv : (2 * k * j + t) / (2 * k) = j := by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega),
        Nat.zero_add]
    rw [show 2 * k * j + (t + 1) = (2 * k * j + t) + 1 by ring, exec_succ, exec_succ]
    simp only [hmv]
    by_cases hV : moverIsV vF t = true
    · simp only [hV, if_true]
      refine ⟨?_, ih₂⟩
      rw [List.drop_append_of_le_length (by omega), ih₁]
      congr 2
      have hidx := verifierMoveIndex_exec (π.seqRep Q).P (π.seqRep Q).V vF x y z rP rV
        (2 * k * j + t) (by rw [hmv]; exact hV)
      have hne : (exec (π.seqRep Q).P (π.seqRep Q).V vF x y z rP rV (2 * k * j + t)).2.length ≠
          Q.eval x.length * k := by omega
      show (π.seqVerifier Q).next x z rV _ = _
      simp only [seqVerifier, ← hk, ← hvF]
      rw [if_neg hne, hidx, hmod, if_pos htk, hdiv, ih₂]
    · simp only [Bool.not_eq_true] at hV
      simp only [hV, Bool.false_eq_true, if_false]
      refine ⟨ih₁, ?_⟩
      rw [List.drop_append_of_le_length (by omega), ih₂]
      congr 2
      have hidx := proverMoveIndex_exec (π.seqRep Q).P (π.seqRep Q).V vF x y z rP rV
        (2 * k * j + t) (by rw [hmv]; exact hV)
      show (π.seqProver Q).next x y rP _ = _
      simp only [seqProver, ← hk, ← hvF]
      rw [hidx, hmod, if_pos htk, hdiv, ih₁]

/-- Up to `t ≤ π.rounds.eval |x|`, the repeated verifier against any prover `P'` has the
same execution as the original verifier on coin block zero, provided `1 ≤ Q.eval |x|`.

**Proof sketch.** Induct on the real move index. The received history has length at most
that index, so it cannot trigger the repeated verdict. At a verifier move the recovered
index is the move index, its phase is zero, and its residue is the index itself. Thus the
same original verifier reply is appended. Prover moves agree because their histories agree.
-/
theorem seqVerifier_exec_first (π : Protocol) (Q : PolyExpr) (P' : Strategy)
    (x y z rP rV : List Bool) (hQ : 1 ≤ Q.eval x.length) {t : ℕ}
    (ht : t ≤ π.rounds.eval x.length) :
    exec P' (π.seqVerifier Q) π.verifierFirst x y z rP rV t =
      exec P' π.V π.verifierFirst x y z rP (coinBlock (π.V.coinLen x.length) 0 rV) t := by
  -- Induct through the first phase, keeping both received histories synchronized.
  induction t with
  | zero => rw [exec_zero, exec_zero]
  | succ t ih =>
    have htk : t < π.rounds.eval x.length := by omega
    rw [exec_succ, exec_succ, ih (by omega)]
    by_cases hm : moverIsV π.verifierFirst t = true
    · simp only [hm, if_true]
      -- The active move count excludes the aggregate-verdict branch in this prefix.
      have hl := exec_length P' π.V π.verifierFirst x y z rP
        (coinBlock (π.V.coinLen x.length) 0 rV) t
      have hkQ : π.rounds.eval x.length ≤ Q.eval x.length * π.rounds.eval x.length := by
        simpa only [one_mul] using Nat.mul_le_mul_right (π.rounds.eval x.length) hQ
      have hne : (exec P' π.V π.verifierFirst x y z rP
          (coinBlock (π.V.coinLen x.length) 0 rV) t).2.length ≠
            Q.eval x.length * π.rounds.eval x.length := by omega
      have hidx := verifierMoveIndex_exec P' π.V π.verifierFirst x y z rP
        (coinBlock (π.V.coinLen x.length) 0 rV) t hm
      have hn : (π.seqVerifier Q).next x z rV
          (exec P' π.V π.verifierFirst x y z rP
            (coinBlock (π.V.coinLen x.length) 0 rV) t).2 =
          π.V.next x z (coinBlock (π.V.coinLen x.length) 0 rV)
            (exec P' π.V π.verifierFirst x y z rP
              (coinBlock (π.V.coinLen x.length) 0 rV) t).2 := by
        rw [seqVerifier_next, if_neg hne, hidx,
          Nat.mod_eq_of_lt (by omega), if_pos htk, Nat.div_eq_of_lt (by omega),
          Nat.zero_mul, List.drop_zero]
      rw [hn]
    · simp only [hm, Bool.false_eq_true, if_false]

/-- The repeated output is the aggregate verdict on the final received history:
`(π.seqRep Q).outV P' x y z r = π.seqVerdict (Q.eval |x|) x z (List.ofFn r.2) hist`,
where `hist` is the verifier component of the repeated transcript.

**Proof sketch.** There are exactly `Q(|x|) · k` prover moves in the even-length repeated
execution. This is the terminal-history test in the repeated verifier, so its terminal
branch computes the aggregate verdict. -/
theorem seqRep_outV_eq (π : Protocol) (Q : PolyExpr) (P' : Strategy)
    (x y z : List Bool) (r : (π.seqRep Q).ExecCoins P' x) :
    (π.seqRep Q).outV P' x y z r =
      π.seqVerdict (Q.eval x.length) x z (List.ofFn r.2)
        ((π.seqRep Q).transcriptWith P' x y z r).2 := by
  have hl : ((π.seqRep Q).transcriptWith P' x y z r).2.length =
      Q.eval x.length * π.rounds.eval x.length := by
    rw [transcriptWith_eq, exec_snd_length, countP_not_moverIsV,
      seqRep_rounds_eval, seqRep_verifierFirst]
    rw [show 2 * π.rounds.eval x.length * Q.eval x.length =
      2 * (Q.eval x.length * π.rounds.eval x.length) by ring]
    cases π.verifierFirst <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega
  rw [outV_eq]
  have hn := congrArg (fun V : Strategy => V.next x z (List.ofFn r.2)
    ((π.seqRep Q).transcriptWith P' x y z r).2) (seqRep_V π Q)
  dsimp only at hn
  rw [hn, seqVerifier_next, if_pos hl]

/-- The final repeated history restricted to the real prover slots of phase `j < Q(|x|)`
is the original verifier history on coin slices `j`. [PS10, Theorem 175.1].

**Proof sketch.** The history just after the phase's real moves is a prefix of the final
history. Its length is the `j · k` slots of preceding phases plus the number of real prover
moves. Taking this prefix and dropping the preceding phases recovers the phase reader.
-/
theorem seqRep_exec_phase_take (π : Protocol) (Q : PolyExpr) (x y z rP rV : List Bool)
    {j : ℕ} (hj : j < Q.eval x.length) :
    ((exec (π.seqRep Q).P (π.seqRep Q).V π.verifierFirst x y z rP rV
      (2 * π.rounds.eval x.length * Q.eval x.length)).2.drop
        (j * π.rounds.eval x.length)).take
          (proverMoves π.verifierFirst (π.rounds.eval x.length)) =
      (exec π.P π.V π.verifierFirst x y z (coinBlock (π.P.coinLen x.length) j rP)
        (coinBlock (π.V.coinLen x.length) j rV) (π.rounds.eval x.length)).2 := by
  let k := π.rounds.eval x.length
  have hjk := Nat.mul_le_mul_right k hj
  have hle : 2 * k * j + k ≤ 2 * k * Q.eval x.length := by
    have hscaled := Nat.mul_le_mul_left 2 hjk
    rw [show 2 * ((j + 1) * k) = 2 * k * j + 2 * k by ring,
      show 2 * (Q.eval x.length * k) = 2 * k * Q.eval x.length by ring] at hscaled
    omega
  have hl : (exec (π.seqRep Q).P (π.seqRep Q).V π.verifierFirst x y z rP rV
      (2 * k * j + k)).2.length = j * k + proverMoves π.verifierFirst k := by
    rw [exec_snd_length, countP_not_moverIsV, proverMoves_eq, countP_not_moverIsV]
    rw [show 2 * k * j + k = 2 * (j * k) + k by ring]
    cases π.verifierFirst <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega
  have hp := exec_snd_take (π.seqRep Q).P (π.seqRep Q).V π.verifierFirst x y z rP rV
    (2 * k * j + k) (2 * k * Q.eval x.length - (2 * k * j + k))
  rw [Nat.add_sub_of_le hle, hl] at hp
  rw [List.take_drop, hp]
  exact (seqRep_exec_phase π Q x y z rP rV hj).2

/-- Perfect completeness on `x, y, z` is preserved by every number of sequential phases:
if `Pr[π.outV π.P x y z = [true]] = 1`, then
`Pr[(π.seqRep Q).outV (π.seqRep Q).P x y z = [true]] = 1`.
[PS10, Theorem 175.1].

**Proof sketch.** Probability one on the finite coin space means every original coin pair
accepts. For each repeated coin pair and phase, its coin slices have the original lengths.
The phase-history reader therefore identifies its verdict with an accepting original run.
All phase tests are true, so the aggregate output is true, including an empty phase list.
-/
theorem seqRep_complete (π : Protocol) (Q : PolyExpr) (x y z : List Bool)
    (hc : uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1) :
    uprob (fun r : (π.seqRep Q).ExecCoins (π.seqRep Q).P x =>
      (π.seqRep Q).outV (π.seqRep Q).P x y z r = [true]) = 1 := by
  -- Reduce completeness to pointwise acceptance on every repeated coin tape.
  apply HardcoreBit.uprob_eq_one_of_forall
  intro r
  rw [seqRep_outV_eq, seqVerdict_eq]
  have hall : (List.range (Q.eval x.length)).all (fun j => decide
      (π.V.next x z (coinBlock (π.V.coinLen x.length) j (List.ofFn r.2))
        ((((π.seqRep Q).transcriptWith (π.seqRep Q).P x y z r).2.drop
          (j * π.rounds.eval x.length)).take
            (proverMoves π.verifierFirst (π.rounds.eval x.length))) = [true])) = true := by
    rw [List.all_eq_true]
    intro j hj
    have hjQ : j < Q.eval x.length := List.mem_range.mp hj
    apply decide_eq_true
    rw [transcriptWith_eq, seqRep_verifierFirst, seqRep_rounds_eval,
      seqRep_exec_phase_take π Q x y z (List.ofFn r.1) (List.ofFn r.2) hjQ]
    -- Each phase uses original-length tapes, so the base acceptance fact applies.
    have hlP : (List.ofFn r.1).length = Q.eval x.length * π.P.coinLen x.length := by
      rw [List.length_ofFn, Strategy.coinLen_eq, seqRep_P, seqProver_coins,
        PolyExpr.eval_mul, Strategy.coinLen_eq]
    have hlV : (List.ofFn r.2).length = Q.eval x.length * π.V.coinLen x.length := by
      rw [List.length_ofFn, Strategy.coinLen_eq, seqRep_V, seqVerifier_coins,
        PolyExpr.eval_mul, Strategy.coinLen_eq]
    have hbP : (coinBlock (π.P.coinLen x.length) j (List.ofFn r.1)).length =
        π.P.coinLen x.length := length_coinBlock (by
      rw [hlP]; exact Nat.mul_le_mul_right _ hjQ)
    have hbV : (coinBlock (π.V.coinLen x.length) j (List.ofFn r.2)).length =
        π.V.coinLen x.length := length_coinBlock (by
      rw [hlV]; exact Nat.mul_le_mul_right _ hjQ)
    have hrun := HardcoreBit.forall_of_uprob_eq_one hc
      (padFin (π.P.coinLen x.length) (coinBlock (π.P.coinLen x.length) j (List.ofFn r.1)),
       padFin (π.V.coinLen x.length) (coinBlock (π.V.coinLen x.length) j (List.ofFn r.2)))
    rw [outV_eq, transcriptWith_eq, ofFn_padFin_of_length hbP,
      ofFn_padFin_of_length hbV] at hrun
    exact hrun
  rw [hall]
  rfl

/-- If the original verifier rejects phase zero against `P'`, then the repeated verifier
rejects the same repeated tape, when `1 ≤ Q.eval |x|`. [PS10, Theorem 175.1].

**Proof sketch.** The first real phase agrees with the original verifier on coin block zero.
Its prover-message history is the initial segment of the final history. Rejection therefore
makes the phase-zero test in the aggregate conjunction false, forcing the repeated output
to be `[false]`. -/
theorem seqRep_reject_of_first (π : Protocol) (Q : PolyExpr) (P' : Strategy)
    (x y z : List Bool) (r : (π.seqRep Q).ExecCoins P' x) (hQ : 1 ≤ Q.eval x.length)
    (hr : π.V.next x z (coinBlock (π.V.coinLen x.length) 0 (List.ofFn r.2))
      (exec P' π.V π.verifierFirst x y z (List.ofFn r.1)
        (coinBlock (π.V.coinLen x.length) 0 (List.ofFn r.2))
        (π.rounds.eval x.length)).2 = [false]) :
    (π.seqRep Q).outV P' x y z r = [false] := by
  -- Compare the first real phase with its prefix in the complete transcript.
  let k := π.rounds.eval x.length
  have hkQ : k ≤ Q.eval x.length * k := by
    simpa only [one_mul] using Nat.mul_le_mul_right k hQ
  have hle : k ≤ 2 * k * Q.eval x.length := by
    have hscaled := Nat.mul_le_mul_left 2 hkQ
    rw [show 2 * (Q.eval x.length * k) = 2 * k * Q.eval x.length by ring] at hscaled
    omega
  have hp := exec_snd_take P' (π.seqVerifier Q) π.verifierFirst x y z
    (List.ofFn r.1) (List.ofFn r.2) k (2 * k * Q.eval x.length - k)
  rw [Nat.add_sub_of_le hle,
    seqVerifier_exec_first π Q P' x y z (List.ofFn r.1) (List.ofFn r.2) hQ le_rfl] at hp
  have hl : (exec P' π.V π.verifierFirst x y z (List.ofFn r.1)
      (coinBlock (π.V.coinLen x.length) 0 (List.ofFn r.2)) k).2.length =
        proverMoves π.verifierFirst k := by
    rw [exec_snd_length, proverMoves_eq]
  rw [hl] at hp
  rw [seqRep_outV_eq, seqVerdict_eq]
  -- A failed initial phase test makes the aggregate conjunction false.
  have hnot : (List.range (Q.eval x.length)).all (fun j => decide
      (π.V.next x z (coinBlock (π.V.coinLen x.length) j (List.ofFn r.2))
        ((((π.seqRep Q).transcriptWith P' x y z r).2.drop (j * k)).take
          (proverMoves π.verifierFirst k)) = [true])) ≠ true := by
    intro hall
    have hz := List.all_eq_true.mp hall 0 (List.mem_range.mpr hQ)
    simp only [Nat.zero_mul, List.drop_zero] at hz
    rw [transcriptWith_eq, seqRep_verifierFirst, seqRep_rounds_eval] at hz
    have hpV := congrArg (fun V : Strategy =>
      (exec P' V π.verifierFirst x y z (List.ofFn r.1) (List.ofFn r.2)
        (2 * k * Q.eval x.length)).2.take (proverMoves π.verifierFirst k)) (seqRep_V π Q)
    dsimp only at hpV
    rw [hpV.trans hp, hr] at hz
    contradiction
  rw [if_neg hnot]

/-- The repeated rejection probability dominates the original rejection probability on
phase zero, against the same prover `P'`, when `1 ≤ Q.eval |x|`.
[PS10, Theorem 175.1].

**Proof sketch.** Restrict the repeated verifier's uniform tape to its initial original-length
prefix; this map preserves uniformity and leaves the prover's tape unchanged. Original
rejection on this projection implies repeated rejection by the first-phase reader, so
monotonicity of probability gives the bound. -/
theorem seqRep_sound_first (π : Protocol) (Q : PolyExpr) (P' : Strategy)
    (x y z : List Bool) (hQ : 1 ≤ Q.eval x.length) :
    uprob (fun r : π.ExecCoins P' x => π.outV P' x y z r = [false]) ≤
      uprob (fun r : (π.seqRep Q).ExecCoins P' x =>
        (π.seqRep Q).outV P' x y z r = [false]) := by
  have hlen : (π.seqRep Q).V.coinLen x.length =
      Q.eval x.length * π.V.coinLen x.length := by
    rw [Strategy.coinLen_eq, seqRep_V, seqVerifier_coins, PolyExpr.eval_mul,
      Strategy.coinLen_eq]
  have hcle : π.V.coinLen x.length ≤ (π.seqRep Q).V.coinLen x.length := by
    rw [hlen]
    simpa only [one_mul] using Nat.mul_le_mul_right (π.V.coinLen x.length) hQ
  let f : (π.seqRep Q).ExecCoins P' x → π.ExecCoins P' x :=
    fun r => (r.1, fun i => r.2 (Fin.castLE hcle i))
  have hf : HardcoreBit.PushesUniform f := HardcoreBit.pushesUniform_id.prodMap
    (HardcoreBit.pushesUniform_restrict (Fin.castLE_injective hcle))
  calc
    _ = uprob (fun r : (π.seqRep Q).ExecCoins P' x =>
        π.outV P' x y z (f r) = [false]) := (hf.uprob_eq _).symm
    _ ≤ _ := uprob_mono fun r hr => by
      apply seqRep_reject_of_first π Q P' x y z r hQ
      rw [outV_eq, transcriptWith_eq] at hr
      change π.V.next x z (List.ofFn (fun i => r.2 (Fin.castLE hcle i)))
        (exec P' π.V π.verifierFirst x y z (List.ofFn r.1)
          (List.ofFn (fun i => r.2 (Fin.castLE hcle i)))
          (π.rounds.eval x.length)).2 = [false] at hr
      rw [← take_ofFn_castLE hcle r.2] at hr
      simpa only [coinBlock_eq, Nat.zero_mul, List.drop_zero] using hr

/-- An efficient original prover gives an efficient sequential prover:
`π.P.Efficient → (π.seqProver Q).Efficient`. [PS10, Theorem 175.1]. -/
theorem seqProver_efficient (π : Protocol) (Q : PolyExpr) (hP : π.P.Efficient) :
    (π.seqProver Q).Efficient := by
  apply SeqEfficiency.phase_efficient (π.seqProver Q) π.P π.rounds π.verifierFirst hP
  intro x z r hist
  dsimp only
  rw [seqProver_next, proverMoveIndex_eq]

/-- An efficient original verifier gives an efficient sequential verifier:
`π.V.Efficient → (π.seqVerifier Q).Efficient`. [PS10, Theorem 175.1]. -/
theorem seqVerifier_efficient (π : Protocol) (Q : PolyExpr) (hV : π.V.Efficient) :
    (π.seqVerifier Q).Efficient := by
  classical
  apply SeqEfficiency.verifier_efficient (π.seqVerifier Q) π.V π.rounds Q π.verifierFirst hV
  intro x z r hist
  dsimp only
  rw [seqVerifier_next, verifierMoveIndex_eq, seqVerdict_eq, proverMoves_eq,
    countP_not_moverIsV]
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq]

/-- The repeated verifier satisfies the padded-verifier equations on `x`, with
`q=Q.eval |x|` and `p=proverMoves π.verifierFirst (π.rounds.eval |x|)`.
[PS10, Theorem 175.1].

**Proof sketch.** Read the coin, round, mover and next-message fields of the construction.
The existing move-index and message-count readers give each remaining contract field.
The aggregate verdict is its published conjunction of phase tests. -/
theorem seqRep_verifierSpec (π : Protocol) (Q : PolyExpr) (x : List Bool) :
    PaddedVerifierSpec π (π.seqRep Q) x (Q.eval x.length)
      (proverMoves π.verifierFirst (π.rounds.eval x.length))
      (fun z r hist => π.seqVerdict (Q.eval x.length) x z r hist) := by
  -- Expose the construction equations through the abstract verifier contract.
  refine {
    coinLen_eq := ?_
    rounds_eq := seqRep_rounds_eval π Q x.length
    first_eq := seqRep_verifierFirst π Q
    next_eq := ?_
    terminal_eq := ?_
    index_eq := ?_
    boundary_lengths := ?_
    local_length := ?_
    period := ?_
  }
  · rw [Strategy.coinLen_eq, seqRep_V, seqVerifier_coins, PolyExpr.eval_mul,
      Strategy.coinLen_eq]
  · intro z r hist
    rw [seqRep_V, seqVerifier_next, verifierMoveIndex_eq]
  · intro z r hist
    exact seqVerdict_eq π (Q.eval x.length) x z r hist
  -- Recover active indices and phase counts through the published execution readers.
  · intro P y z rP rV t hm
    simpa only [verifierMoveIndex_eq] using
      verifierMoveIndex_exec P (π.seqRep Q).V π.verifierFirst x y z rP rV t hm
  · intro P y z rP rV j _
    exact exec_boundary_lengths P (π.seqRep Q).V π.verifierFirst x y z rP rV
      (π.rounds.eval x.length) j
  · intro P y z rP rV
    rw [exec_snd_length, proverMoves_eq]
  · intro j t
    rw [show 2 * π.rounds.eval x.length * j + t =
      2 * (π.rounds.eval x.length * j) + t by ring]
    exact moverIsV_two_mul_add _ _ _

/-- The repeated prover satisfies the padded-prover equations on `x`, with
`q=Q.eval |x|` and `p=if π.verifierFirst then k/2 else (k+1)/2`, for
`k=π.rounds.eval |x|`. [PS10, Theorem 175.1].

**Proof sketch.** Read the prover's coin and reply equations. Recover actual move indices
using the existing prover index reader and obtain phase-boundary and local counts from
the published execution-length readers. The even phase length preserves the mover pattern.
-/
theorem seqRep_proverSpec (π : Protocol) (Q : PolyExpr) (x : List Bool) :
    SequentialZK.PaddedProverSpec π (π.seqRep Q) x (Q.eval x.length)
      (if π.verifierFirst then π.rounds.eval x.length / 2
        else (π.rounds.eval x.length + 1) / 2) := by
  -- Expose the prover construction and its padded execution fields.
  refine {
    prover_coinLen := ?_
    rounds_eval := seqRep_rounds_eval π Q x.length
    first := seqRep_verifierFirst π Q
    next := ?_
    prover_index := ?_
    boundary := ?_
    original_count := ?_
    real_le := ?_
    period := ?_
  }
  · rw [Strategy.coinLen_eq, seqRep_P, seqProver_coins, PolyExpr.eval_mul,
      Strategy.coinLen_eq]
  · intro y r hist
    rw [seqRep_P, seqProver_next, proverMoveIndex_eq]
  -- The same index, boundary and mover readers discharge the remaining contract.
  · intro V y z rP rV n hm
    simpa only [proverMoveIndex_eq] using
      proverMoveIndex_exec (π.seqRep Q).P V π.verifierFirst x y z rP rV n hm
  · intro V y z rP rV j
    exact exec_boundary_lengths (π.seqRep Q).P V π.verifierFirst x y z rP rV
      (π.rounds.eval x.length) j
  · intro V y z rP rV
    rw [exec_snd_length, countP_not_moverIsV]
  · cases π.verifierFirst <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega
  · intro j t
    rw [show 2 * π.rounds.eval x.length * j + t =
      2 * (π.rounds.eval x.length * j) + t by ring]
    exact moverIsV_two_mul_add _ _ _

end Protocol

/-! ### Theorem 175.1 -/

variable {π : Protocol} {R : List Bool → List Bool → Prop}

/-- **Theorem 175.1, computational case** [PS10, Theorem 175.1]: the sequential repetition of a
zero-knowledge protocol with a bounded prover is zero-knowledge.

**Proof sketch** ([Gol01, §4.3.4], with the hybrids made explicit).
1. Put `n = |x|`, `k = π.rounds.eval n` and `p = proverMoves π.verifierFirst k`. Each padded
   phase contributes `p` real prover messages and `k - p` empty prover fillers to the
   verifier's received history. If `k = 0` or `Q(n) = 0`, sample the cheating verifier's tape
   and output its exact empty-history view directly.
2. Given an efficient `V_Q*`, use one deterministic efficient wrapped verifier `V*` for a
   run of `π`. Its auxiliary input contains the original `z`, the global verifier tape `r`,
   the phase index and the bounded received-prover prefix of earlier padded phases. It runs
   `V_Q*` on `r` with that prefix followed by this phase's real prover messages. Its own tape
   is empty. Only the honest prover's fillers are fixed to `[]`; no restriction is imposed
   on a cheating verifier's filler replies. Let `S` be the simulator supplied by `ZK π R`.
3. `S_Q(x, z)` samples `r` once and calls `S` with fresh coins for each phase. Normalize each
   output before extending the prefix: syntactically parse its view and message-list
   encoding, take at most `p` real prover messages, truncate each to `B(n)` bits, and pad
   missing real messages with `[]`. Use the known phase input/auxiliary data and empty
   wrapper tape as the view fields. A bad/noncanonical encoding or unexpected view fields
   maps to that canonical phase view with `p` empty real messages. Append the `k - p`
   honest-prover fillers, all `[]`, and retain only these `k` prover-message slots.
   Every real phase view is fixed by this normalization: its count is exactly `p`, its
   metadata is the known phase data, and every real prover message is bounded by `hB`.
   No assumption that simulated outputs already have a valid shape is made.
4. On every simulator tape, the accumulated prefix has at most `Q(n) * k` messages of at
   most `B(n)` bits. Its message-list encoding has length at most `Q(n) * k * (2B(n) + 2)`.
   Including the original auxiliary input, verifier tape, phase index and fixed pairing
   overhead gives a polynomial bound in `n + |z|`; for `|z| ≤ Lz(n)` choose a polynomial
   `Lz'` bounding the phase auxiliary inputs. Thus the same `S_Q` is a uniform strict PPT.
   Its final output is the canonical view with fields `(x, z, r)` and the accumulated prefix.
5. In hybrid `H_i`, the first `i` phases are real and the rest use these normalized simulated
   phases. Normalization fixes real phases, so `H_Q` is the real view and `H_0` is `S_Q`.
   Apply the same normalization and simulated-suffix computation on both sides of each
   phase comparison. A nonuniform reduction may fix a maximizing phase and bounded prefix,
   together with `x`, `z` and `r`, as polynomial-length advice; it needs neither the witness
   nor an efficient honest prover, and need not trust metadata in an arbitrary simulator
   output. By `ZK π R` at `Lz'`, summing the `Q(n)` gaps gives `Q(n) * ε(n)`, negligible. -/
theorem ZK.seqRep {B : PolyExpr} (h : ZK π R) (hB : π.ProverBounded R B) (Q : PolyExpr) :
    ZK (π.seqRep Q) R := by
  exact SequentialZK.zk_of_padded_spec h hB Q (fun x => π.seqRep_proverSpec Q x)

/-- **Theorem 175.1, statistical case**: statistical error `δ` composes to `Q · δ`, under the
same prover bound.

**Proof sketch.** Use the same phase-shape normalization as `ZK.seqRep`: exactly
`proverMoves π.verifierFirst k` bounded real prover messages, the canonical empty prover
fillers giving `k` received slots per padded phase, and the fixed canonical fallback for a
malformed simulated view. This fixes every real phase view and bounds every simulated
prefix, so it also gives a strict-PPT simulator without an output-shape premise.
For a fixed earlier prefix, change one phase from real to simulated at distance at most
`δ(|x|)` (`StatZK π R δ` holds for every auxiliary input). The common normalization and
simulated-suffix computation do not increase statistical distance. Average over prefixes
and sum the `Q(|x|)` gaps by the triangle inequality, giving exactly `Q(|x|) · δ(|x|)`.
The empty-history construction handles `k = 0` or `Q(|x|) = 0` directly. The padded-prover
contract and split/block coin equivalences identify the two endpoint laws exactly. -/
theorem StatZK.seqRep {B : PolyExpr} {δ : ℕ → ℝ} (h : StatZK π R δ)
    (hB : π.ProverBounded R B) (Q : PolyExpr) :
    StatZK (π.seqRep Q) R (fun n => Q.eval n * δ n) := by
  exact SequentialZK.statZK_of_padded_spec h hB Q (fun x => π.seqRep_proverSpec Q x)

/-- **Theorem 175.1, perfect case**: the sequential repetition of a perfect zero-knowledge
protocol with a bounded prover is perfect zero-knowledge (`StatZK.seqRep` at `δ = 0`). -/
theorem PerfectZK.seqRep {B : PolyExpr} (h : PerfectZK π R) (hB : π.ProverBounded R B)
    (Q : PolyExpr) : PerfectZK (π.seqRep Q) R := by
  apply perfectZK_iff.mpr
  simpa only [mul_zero] using StatZK.seqRep h.statZK hB Q

/-- **Theorem 175.1, strict-PPT aborting case** [PS10, Theorem 175.1]
[Gol01, Definition 4.3.1 and §4.3.4]: the formal `PerfectZKAbort` premise gives statistical
zero-knowledge of the repetition with error `Q(n) · 2^{-n}`.

**Proof sketch.** The premise supplies a strict-PPT simulator that aborts with probability at
most `1/2` and, conditioned on success, has exactly the real view's law. First apply the proved
`PerfectZKAbort.statZK` bridge: run `n = |x|` independent retries on fresh coin blocks and keep
the first non-aborting output. The probability that all retries abort is at most `2^{-n}`;
conditioned on a retry succeeding, its output has the real view's law. This yields statistical
error `2^{-n}`. Then `StatZK.seqRep` [Gol01, §4.3.4] bounds the distance of the `Q(n)` phases by
the sum of their errors, `Q(n) · 2^{-n}`.

**Source distinction.** [PS10] uses expected-polynomial-time wording. This result instead uses
boundedly many executions of the strict-PPT aborting simulator in its formal premise; it does
not infer an exact conditional law by truncating an arbitrary expected-time simulator. -/
theorem PerfectZKAbort.seqRep {B : PolyExpr} (h : PerfectZKAbort π R)
    (hB : π.ProverBounded R B) (Q : PolyExpr) :
    StatZK (π.seqRep Q) R (fun n => Q.eval n * (1 / 2 : ℝ) ^ n) := by
  simpa only [one_div] using StatZK.seqRep h.statZK hB Q

/-- **The repetition of an interactive proof is an interactive proof** [PS10, Theorem 175.1,
"`(P_Q, V_Q)` is an interactive proof"], when every input length has at least one phase.

**Proof sketch.**
1. *Efficiency:* `V_Q` runs `π.V`'s machine on a coin slice and a suffix of its history, or
   `Q(|x|)` times for its verdict, so it is computed by a uniform machine with coins `Q · coins`.
2. *Completeness:* with the witness `y` of `π`, each phase is an honest execution of `π` with
   independent uniform coin slices (`seqRep_exec_phase`), accepted with probability one, so
   every phase accepts.
3. *Soundness:* for `x ∉ L` and a prover `P'`, phase `0` is an execution of `P'` against `π.V`
   on the coin slice `0`, which is uniform. Here the dropped prefix is empty, so
   `seqRep_exec_phase`'s argument applies with `P'` in place of `π.P`. Phase `0`'s verdict is
   `[false]` with probability `> 1 − ε(|x|)`, and then `V_Q` outputs `[false]`. Phase `0`
   exists since `1 ≤ Q(|x|)`. -/
theorem InteractiveProof.seqRep {L : Language Bool} (h : InteractiveProof π L) (Q : PolyExpr)
    (hQ : ∀ n, 1 ≤ Q.eval n) : InteractiveProof (π.seqRep Q) L := by
  constructor
  · rw [Protocol.seqRep_V]
    exact π.seqVerifier_efficient Q h.efficientV
  · exact SequentialZK.PaddedProverSpec.complete (fun x => π.seqRep_proverSpec Q x)
      (fun x y z hc => π.seqRep_complete Q x y z hc) h.complete
  · obtain ⟨ε, hε, hs⟩ := h.sound
    refine ⟨ε, hε, fun x hx P' z => ?_⟩
    exact (hs x hx P' z).trans_le (π.seqRep_sound_first Q P' x [] z (hQ x.length))

/-- **Sequential repetition multiplies the soundness error** [PS10, p. 120: the protocol "can be
repeated many times … to drive the probability of error as low as desired"; and p. 127, the
`O(n|E|)` repetitions of the 3-colouring protocol]: if `π` has soundness error `s`, its
`Q`-phase sequential repetition (which accepts iff every phase does) has soundness error
`s(|x|)^{Q(|x|)}`, with perfect completeness kept.

**Proof sketch.**
1. *Efficiency and completeness* as in `InteractiveProof.seqRep`: every phase of the honest
   execution is an honest execution of `π` with independent coin slices
   (`seqRep_exec_phase`), accepted with probability one.
2. *Soundness:* fix `x ∉ L`, a prover `P'` and `z`. Condition on the prover's coins and on the
   transcript of phases `0, …, j − 1`. Phase `j` is then an execution, against `π.V` on a fresh
   uniform coin slice, of the prover strategy that `P'` induces with that prefix hard-wired (the
   verifier reads only phase `j`'s messages). By `π`'s soundness it accepts with probability at
   most `s(|x|)`, whatever the prefix. By induction on `j`, all `Q(|x|)` phases accept with
   probability at most `s(|x|)^{Q(|x|)}`, so `V_Q` outputs `[false]` with probability at least
   `1 − s(|x|)^{Q(|x|)}`. -/
theorem InteractiveProofErr.seqRep {L : Language Bool} {s : ℕ → ℝ} (h : InteractiveProofErr π L s)
    (Q : PolyExpr) (hQ : ∀ n, 1 ≤ Q.eval n) :
    InteractiveProofErr (π.seqRep Q) L (fun n => s n ^ Q.eval n) := by
  constructor
  · rw [Protocol.seqRep_V]
    exact π.seqVerifier_efficient Q h.efficientV
  · exact SequentialZK.PaddedProverSpec.complete (fun x => π.seqRep_proverSpec Q x)
      (fun x y z hc => π.seqRep_complete Q x y z hc) h.complete
  · intro x hx P' z
    exact (π.seqRep_verifierSpec Q x).sound h hx P' z

/-- **The efficient-prover form**: the sequential repetition of an interactive proof with an
efficient prover and soundness error `s` is one with soundness error `s^Q`; the repeated prover
is efficient and complete for every witness.

**Proof sketch.** `InteractiveProofErr.seqRep` for the proof system; `P_Q` runs `π.P`'s machine
on its coin slice and a suffix of its history, so a uniform machine computes it; completeness for
every witness phase by phase, as in `InteractiveProof.seqRep`. -/
theorem EfficientProverProofErr.seqRep {L : Language Bool} {s : ℕ → ℝ}
    (h : EfficientProverProofErr π L R s) (Q : PolyExpr) (hQ : ∀ n, 1 ≤ Q.eval n) :
    EfficientProverProofErr (π.seqRep Q) L R (fun n => s n ^ Q.eval n) := by
  refine {
    toInteractiveProofErr := h.toInteractiveProofErr.seqRep Q hQ
    efficientP := ?_
    boundedP := ?_
    completeWitness := ?_
  }
  · rw [Protocol.seqRep_P]
    exact π.seqProver_efficient Q h.efficientP
  · obtain ⟨B, hB⟩ := h.boundedP
    exact ⟨B, hB.seqRep Q⟩
  · intro x y hxy z
    exact π.seqRep_complete Q x y z (h.completeWitness x y hxy z)

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/ZeroKnowledge/Defs.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.Interaction
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Asymptotic.Sampling
import TCSlib.Cryptography.Foundations.Negligible
import TCSlib.Cryptography.ZeroKnowledge.EncodingMachines
import TCSlib.Complexity.Randomized.Closure

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Zero-knowledge: honest-verifier, general, statistical and perfect

The zero-knowledge notions of [PS10, §4.6] on top of the interaction model of
`Interaction.lean` (foundation decision D8): honest-verifier zero-knowledge
[PS10, Definition 121.1], zero-knowledge against every efficient verifier
[PS10, Definition 121.2], and the perfect and statistical variants (Def-122.a) through the
sup-over-test-sets closeness `StatClose` of `Asymptotic/Sampling.lean`, together with the
implications statistical ⇒ computational (`StatZK.zk`, `StatZK.hvzk`), general ⇒ honest-verifier
(`ZK.hvzk`), and the negligibility bookkeeping converting the chapter's per-vertex bounds
`2^{-n}`, `e^{-n}` into functions of the instance length `|x|` (Inf-4.4).

The simulator is a uniform `Complexity.NUPPT` run once at parameter `|x|` on `⟨x, z⟩`
(`Complexity.NUPPT.simulate`); its output is a word read as an encoded view
(`View.encode`: `⟨⟨x, z⟩, ⟨r, messages⟩⟩`), and the distinguisher is a non-uniform PPT run at
parameter `|x|` on the encoded view (`Complexity.NUPPT.distinguisherL`).

**Deviation (D8):** strict PPT simulators (the text's expected polynomial time is not
formalized): the rewinding simulator of graph isomorphism is truncated, and that theorem becomes
statistical zero-knowledge (`gi_statZK`); the 3-colouring theorem remains computational
zero-knowledge, its truncated simulator contributing statistical sampling and failure terms to
the negligible error; the auxiliary input of the verifier is bounded by an arbitrary polynomial
`Lz : PolyExpr` quantified after the simulator (the class a `t(|x|)`-time verifier can read,
and what the non-uniform reduction of [PS10, Proposition 128.8] needs); the error bound is
a function of `|x|` (the text's `e(n)` leaves `n` undefined); the honest-verifier notion is
stated for a protocol and a witness relation without assuming the proof property, which the
theorems add separately.
The bound `Lz` is necessary for the 3-colouring protocol, not only convenient (gate 03e,
note 9; round 2, finding 6). The distinguisher runs in time polynomial in its input, the
encoded view, which contains `z`. With `|z|` exponential in `ℓ(n)` it can open the perfectly
binding commitments by exhaustive search. On a graph with two proper colourings outside one
colour-permutation orbit, that tells the two real views apart with advantage 1, while the
simulator does not see the witness. Read literally, [PS10, Definition 121.2] (every
`z ∈ {0,1}*`, with `D` polynomial-time in its input) has the same defect for that protocol.
Protocols with exactly simulable views are not affected. For the same reason the
distinguisher's advice is indexed by the parameter `|x|`, not by its input length.

**Perfect zero-knowledge (ruling G3-4 of gate 03).** With strict simulators and honest parties
drawing polynomially many fair coins (D8, D10), no protocol of the source attains `PerfectZK`
or `PerfectZKAbort` (see their docstrings). The source's perfect zero-knowledge protocol,
graph isomorphism [PS10, Theorem 122.3], is formalized as `StatZK` with negligible error
(`gi_statZK`, `ZeroKnowledge/GraphIsomorphismZK.lean`), the substantive instance of the
notions of this file; `perfectZK_zeroRounds` is a degenerate one. The abort form implies
statistical zero-knowledge with error `2^{-|x|}` (`PerfectZKAbort.statZK`), by running the
aborting simulator `|x|` times on fresh coins (`AbortRetry.retry`).

## Main definitions

* `Complexity.NUPPT.simulate` — the simulator's output on `(x, z)`.
* `TCSlib.Cryptography.HVZK` — honest-verifier zero-knowledge [PS10, Definition 121.1]
  (Def-121.1).
* `TCSlib.Cryptography.ZK` — zero-knowledge [PS10, Definition 121.2] (Def-121.2).
* `TCSlib.Cryptography.StatZK`, `TCSlib.Cryptography.PerfectZK`,
  `TCSlib.Cryptography.PerfectZKAbort` — statistical zero-knowledge with error `δ(|x|)`,
  perfect zero-knowledge (`δ = 0`), and the abort form of perfect zero-knowledge
  [Gol01, Definition 4.3.1] (Def-122.a).
* `TCSlib.Cryptography.AbortRetry.attempt`, `TCSlib.Cryptography.AbortRetry.retry` — one
  attempt of an aborting simulator on a coin block, and the simulator that retries it `|x|`
  times (as functions of the machine layout).

## Main results

* `TCSlib.Cryptography.StatZK.zk`, `TCSlib.Cryptography.StatZK.hvzk` — statistical
  zero-knowledge with negligible error implies zero-knowledge and honest-verifier
  zero-knowledge (`distAdv_le_of_statClose`).
* `TCSlib.Cryptography.ZK.hvzk` — zero-knowledge implies honest-verifier zero-knowledge.
* `TCSlib.Cryptography.PerfectZK.zk`, `TCSlib.Cryptography.StatZK.mono` — perfect
  zero-knowledge is zero-knowledge; weakening the error.
* `TCSlib.Cryptography.perfectZK_zeroRounds` — non-vacuity: the protocol with no messages is
  perfectly zero-knowledge.
* `TCSlib.Cryptography.PerfectZKAbort.statZK`, `TCSlib.Cryptography.PerfectZKAbort.zk` — the
  abort form implies statistical zero-knowledge with error `2^{-|x|}`, hence zero-knowledge
  (`TCSlib.Cryptography.AbortRetry.statClose_retry`: the first non-`⊥` output of `K`
  independent runs of an aborting sampler is `2^{-K}`-close to its conditional law;
  `TCSlib.Cryptography.AbortRetry.exists_retrySimulator`: the retrying simulator is a uniform
  PPT, by `EncodingMachines.polyTimeComputable_firstIdx`, an instance of
  `Complexity.polyTimeComputable_iterateFind`).
* `TCSlib.Cryptography.negligible_inv_pow_sqrt_div`,
  `TCSlib.Cryptography.negligible_two_pow_neg_sqrt_div`,
  `TCSlib.Cryptography.negligible_exp_neg_sqrt_div`,
  `TCSlib.Cryptography.negligible_of_le_inv_pow_sqrt_div` — `a^{-√(N/C)}` is negligible
  in `N` (Inf-4.4): the per-vertex bounds of the graph protocols are negligible in `|x|`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.6 Zero-knowledge, pp. 120–122.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Lemma 3.1 (statistical distance bounds every advantage).
* [Gol01] O. Goldreich, *Foundations of Cryptography, Volume I: Basic Tools*, Cambridge
  University Press, 2001, Definition 4.3.1 (perfect zero-knowledge with abort).
-/

namespace TCSlib.Cryptography

open Complexity Turing

/-! ### Simulators -/

/-- The simulator's output on `(x, z)` [PS10, Definitions 121.1 and 121.2, `S(x, z)`]: one
activation of `S` at parameter `|x|` on `⟨x, z⟩`, a word read as an encoded view. -/
def _root_.Complexity.NUPPT.simulate (S : NUPPT) (x z : List Bool) (r : S.Coins x.length) :
    List Bool :=
  S.runAt x.length (pairEncode x z) r

/-- `simulate` unfolds to the typed activation at parameter `|x|`. -/
theorem _root_.Complexity.NUPPT.simulate_eq (S : NUPPT) (x z : List Bool)
    (r : S.Coins x.length) : S.simulate x z r = S.runAt x.length (pairEncode x z) r := rfl

/-! ### Honest-verifier and general zero-knowledge -/

/-- Honest-verifier zero-knowledge of `π` for the witness relation `R`
[PS10, Definition 121.1] (Def-121.1): there is a uniform PPT simulator `S` such that for every
auxiliary-input bound `Lz` and every non-uniform PPT distinguisher `D` there is a negligible `ε`
with, for all `x`, witnesses `y` of `x` and auxiliary inputs `z` of length `≤ Lz(|x|)`, the
advantage of `D` (at parameter `|x|`) between the honest verifier's view of
`P(x, y) ↔ V(x, z)` and `S(x, z)` at most `ε(|x|)`.

**Deviation (D8):** strict PPT simulator; auxiliary inputs bounded by `∀ Lz : PolyExpr`;
simulator and distinguisher at parameter `|x|`; views encoded as `⟨⟨x, z⟩, ⟨r, msgs⟩⟩`. -/
def HVZK (π : Protocol) (R : List Bool → List Bool → Prop) : Prop :=
  ∃ S : NUPPT, S.Uniform ∧ ∀ (Lz : PolyExpr) (D : NUPPT), ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ x y z, R x y → z.length ≤ Lz.eval x.length →
      distAdv (fun r => (π.viewV x y z r).encode) (S.simulate x z) (D.distinguisherL x.length) ≤
        ε x.length

/-- Zero-knowledge of `π` for the witness relation `R` [PS10, Definition 121.2] (Def-121.2):
for every efficient verifier strategy `V'` there is a uniform PPT simulator `S` such that for
every auxiliary-input bound `Lz` and every non-uniform PPT distinguisher `D` there is a
negligible `ε` with, for all `x`, witnesses `y` and auxiliary inputs `z` of length `≤ Lz(|x|)`,
the advantage of `D` between the view of `V'` in `P(x, y) ↔ V'(x, z)` and `S(x, z)` at most
`ε(|x|)`.

**Deviation (D8):** strict PPT simulator; auxiliary inputs bounded by `∀ Lz : PolyExpr`;
simulator and distinguisher at parameter `|x|`; views encoded as `⟨⟨x, z⟩, ⟨r, msgs⟩⟩`. The
cheating verifier `V'` is only `Efficient`, with no message-prefix cap (question Q-1 of
gate 03, ruled: no cap on `V*`), so its class is larger than the text's. Since the honest
prover's messages are polynomially bounded in `|x|` in the proof systems
(`Protocol.ProverBounded`, ruling G3-3 of gate 03), the view of every efficient `V'` — `x`,
`z`, its tape and the honest prover's messages — is polynomially bounded all the same. -/
def ZK (π : Protocol) (R : List Bool → List Bool → Prop) : Prop :=
  ∀ V' : Strategy, V'.Efficient → ∃ S : NUPPT, S.Uniform ∧
    ∀ (Lz : PolyExpr) (D : NUPPT), ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ x y z, R x y → z.length ≤ Lz.eval x.length →
        distAdv (fun r => ((π.withV V').viewV x y z r).encode) (S.simulate x z)
          (D.distinguisherL x.length) ≤ ε x.length

/-- The defining property of `ZK`: `ZK π R` iff for every efficient `V'` there is a uniform
simulator `S` such that for every `Lz` and every distinguisher `D` some negligible `ε` bounds
`distAdv (view of V' in P(x, y) ↔ V'(x, z)) (S(x, z)) (D at |x|) ≤ ε(|x|)` for all `x`, `y` with
`R x y`, and `z` with `|z| ≤ Lz(|x|)`. -/
theorem ZK_iff (π : Protocol) (R : List Bool → List Bool → Prop) :
    ZK π R ↔ ∀ V' : Strategy, V'.Efficient → ∃ S : NUPPT, S.Uniform ∧
      ∀ (Lz : PolyExpr) (D : NUPPT), ∃ ε : ℕ → ℝ, Negligible ε ∧
        ∀ x y z, R x y → z.length ≤ Lz.eval x.length →
          distAdv (fun r => ((π.withV V').viewV x y z r).encode) (S.simulate x z)
            (D.distinguisherL x.length) ≤ ε x.length := Iff.rfl

/-- Statistical zero-knowledge of `π` for `R` with error `δ(|x|)` (Def-122.a, campaign
addition needed for the truncated simulators): for every efficient `V'` there is a uniform PPT
simulator whose output on `(x, z)` is `StatClose` (every test set, sup form) within `δ(|x|)`
to the view of `V'` in `P(x, y) ↔ V'(x, z)`, for all `x`, witnesses `y` and all auxiliary
inputs `z`.

**Deviation (D8):** strict PPT simulator; the bound is in `|x|`. -/
def StatZK (π : Protocol) (R : List Bool → List Bool → Prop) (δ : ℕ → ℝ) : Prop :=
  ∀ V' : Strategy, V'.Efficient → ∃ S : NUPPT, S.Uniform ∧ ∀ x y z, R x y →
    StatClose (fun r => ((π.withV V').viewV x y z r).encode) (S.simulate x z) (δ x.length)

/-- Statistical zero-knowledge is equivalent to the simulator property: for every efficient
verifier `V'` there is a uniform simulator `S` with statistical error at most `δ(|x|)` on
`(x, z)` for every witness `y` satisfying `R x y`. [PS10, §4.6].
`StatZK π R δ ↔ ∀ V' : Strategy, V'.Efficient → ∃ S : NUPPT, S.Uniform ∧ ∀ x y z, R x y → StatClose
(fun r => ((π.withV V').viewV x y z r).encode) (S.simulate x z) (δ x.length)`. -/
theorem StatZK_iff (π : Protocol) (R : List Bool → List Bool → Prop) (δ : ℕ → ℝ) :
    StatZK π R δ ↔ ∀ V' : Strategy, V'.Efficient →
      ∃ S : NUPPT, S.Uniform ∧ ∀ x y z, R x y →
        StatClose (fun r => ((π.withV V').viewV x y z r).encode)
          (S.simulate x z) (δ x.length) := Iff.rfl

/-- Perfect zero-knowledge [PS10, §4.6, "perfect zero-knowledge"] (Def-122.a): statistical
zero-knowledge with error `0`, i.e. the simulator's output has exactly the law of the view.

**Cost (D8, D10; ruling G3-4 of gate 03):** no protocol of the source attains this notion. A
strict simulator with bit coins outputs every string with a dyadic probability, and an
honest prover drawing polynomially many fair coins cannot draw a uniform permutation of
`n ≥ 3` points (`n! ∤ 2^c`), so the reply of the honest graph-isomorphism prover
[PS10, Protocol 120.6] depends on the witness. [PS10, Theorem 122.3] is formalized as
`StatZK` with negligible error (`gi_statZK`); the instances of this notion are degenerate
(`perfectZK_zeroRounds`). -/
def PerfectZK (π : Protocol) (R : List Bool → List Bool → Prop) : Prop :=
  StatZK π R (fun _ => 0)

/-- Perfect zero-knowledge is statistical zero-knowledge with identically zero error. -/
theorem perfectZK_iff {π : Protocol} {R : List Bool → List Bool → Prop} :
    PerfectZK π R ↔ StatZK π R (fun _ => 0) := Iff.rfl

/-- Perfect zero-knowledge with abort [Gol01, Definition 4.3.1] (Def-122.a, the GMR form):
for every efficient `V'` there is a uniform PPT simulator that outputs `⊥ = []` with
probability at most `1/2` and whose output, conditioned on not aborting, has exactly the law
of the view of `V'`: for every test set `T`,
`Pr[T(view)] · Pr[S ≠ ⊥] = Pr[S ≠ ⊥ ∧ T(S)]` (`⊥ = []` is never a view encoding).

**Cost (D8, D10; ruling G3-4 of gate 03):** no protocol of the source attains this notion:
as for `PerfectZK`, the honest graph-isomorphism prover's permutation, drawn from fair coins,
is not uniform, so its reply depends on the witness, which no simulator sees. The abort form
holds for ideal permutations at the concrete layer (`giSimAttempt_perfectAbort`). It implies
statistical zero-knowledge with error `2^{-|x|}` (`PerfectZKAbort.statZK`), hence
zero-knowledge (`PerfectZKAbort.zk`); the source's "perfect" results are stated as `StatZK`
with negligible error. -/
def PerfectZKAbort (π : Protocol) (R : List Bool → List Bool → Prop) : Prop :=
  ∀ V' : Strategy, V'.Efficient → ∃ S : NUPPT, S.Uniform ∧ ∀ x y z, R x y →
    uprob (fun r : S.Coins x.length => S.simulate x z r = []) ≤ 1 / 2 ∧
    ∀ T : List Bool → Prop,
      uprob (fun r : (π.withV V').ExecCoins (π.withV V').P x =>
          T ((π.withV V').viewV x y z r).encode) *
          uprob (fun r : S.Coins x.length => S.simulate x z r ≠ []) =
        uprob (fun r : S.Coins x.length => S.simulate x z r ≠ [] ∧ T (S.simulate x z r))

/-! ### Implications between the notions -/

/-- Statistical zero-knowledge with negligible error implies zero-knowledge
[PS10, §4.6, perfect/statistical ⇒ computational]: the same simulator works for every
distinguisher, with `ε := δ`, since a distinguisher's advantage between `δ`-close samplers is
at most `δ` (`distAdv_le_of_statClose`, [Gar26, Lemma 3.1]). -/
theorem StatZK.zk {π : Protocol} {R : List Bool → List Bool → Prop} {δ : ℕ → ℝ}
    (hδ : Negligible δ) (h : StatZK π R δ) : ZK π R := by
  intro V' hV'
  obtain ⟨S, hS, hclose⟩ := h V' hV'
  exact ⟨S, hS, fun _ D => ⟨δ, hδ, fun x y z hR _ =>
    distAdv_le_of_statClose _ _ (hclose x y z hR) _⟩⟩

/-- Statistical zero-knowledge with negligible error implies honest-verifier zero-knowledge
when the honest verifier is efficient: instantiate `V' := V` (`Protocol.withV_self`) and
apply `distAdv_le_of_statClose`. -/
theorem StatZK.hvzk {π : Protocol} {R : List Bool → List Bool → Prop} {δ : ℕ → ℝ}
    (hδ : Negligible δ) (hV : π.V.Efficient) (h : StatZK π R δ) : HVZK π R := by
  obtain ⟨S, hS, hclose⟩ := h π.V hV
  refine ⟨S, hS, fun _ D => ⟨δ, hδ, fun x y z hR _ => ?_⟩⟩
  have hc := hclose x y z hR
  rw [Protocol.withV_self] at hc
  exact distAdv_le_of_statClose _ _ hc _

/-- Zero-knowledge implies honest-verifier zero-knowledge when the honest verifier is
efficient [PS10, §4.6, after Definition 121.2]: instantiate `V' := V`. -/
theorem ZK.hvzk {π : Protocol} {R : List Bool → List Bool → Prop} (hV : π.V.Efficient)
    (h : ZK π R) : HVZK π R := by
  obtain ⟨S, hS, hsim⟩ := h π.V hV
  refine ⟨S, hS, fun Lz D => ?_⟩
  obtain ⟨ε, hε, hadv⟩ := hsim Lz D
  refine ⟨ε, hε, fun x y z hR hz => ?_⟩
  have hc := hadv x y z hR hz
  rwa [Protocol.withV_self] at hc

/-- Weakening the statistical error. -/
theorem StatZK.mono {π : Protocol} {R : List Bool → List Bool → Prop} {δ δ' : ℕ → ℝ}
    (h : StatZK π R δ) (hle : ∀ n, δ n ≤ δ' n) : StatZK π R δ' := by
  intro V' hV'
  obtain ⟨S, hS, hclose⟩ := h V' hV'
  exact ⟨S, hS, fun x y z hR => (hclose x y z hR).mono (hle _)⟩

/-- Perfect zero-knowledge is statistical zero-knowledge with error `0`. -/
theorem PerfectZK.statZK {π : Protocol} {R : List Bool → List Bool → Prop} (h : PerfectZK π R) :
    StatZK π R (fun _ => 0) := h

/-- Perfect zero-knowledge implies zero-knowledge [PS10, §4.6]. -/
theorem PerfectZK.zk {π : Protocol} {R : List Bool → List Bool → Prop} (h : PerfectZK π R) :
    ZK π R :=
  StatZK.zk negligible_zero h

/-- Non-vacuity (gate 03e, note 10): the protocol with no messages is perfectly
zero-knowledge for every relation.

**Proof sketch.** The view of any `V'` is `⟨x, z, r, []⟩` (no moves, `exec_zero`), and the
simulator `NUPPT.ofPolyTimeUniform` of the layout map `w ↦ ⟨inArg w, ⟨inCoins w, []⟩⟩` with
`V'`'s coin polynomial outputs `⟨⟨x, z⟩, ⟨r, []⟩⟩` on its own tape `r`; the prover's tape does
not enter the view (`uprob_fst` after `Equiv.prodComm`), so the two laws coincide. -/
theorem perfectZK_zeroRounds (P V : Strategy) (b : Bool) (R : List Bool → List Bool → Prop) :
    PerfectZK ⟨P, V, .const 0, b⟩ R := by
  intro V' _
  have hF : PolyTimeComputable fun w =>
      pairEncode (NUPPT.inArg w) (pairEncode (NUPPT.inCoins w) []) :=
    NUPPT.polyTimeComputable_inArg.pairEncode
      (NUPPT.polyTimeComputable_inCoins.pairEncode (polyTimeComputable_const []))
  refine ⟨NUPPT.ofPolyTimeUniform hF V'.coins, NUPPT.ofPolyTimeUniform_uniform hF _,
    fun x y z _ T => ?_⟩
  have h1 : uprob (fun r : (Protocol.withV ⟨P, V, .const 0, b⟩ V').ExecCoins P x =>
      T ((Protocol.withV ⟨P, V, .const 0, b⟩ V').viewV x y z r).encode) =
      uprob (fun ρ : V'.Coins x.length =>
        T (pairEncode (pairEncode x z) (pairEncode (List.ofFn ρ) []))) := by
    rw [← uprob_comp_equiv (Equiv.prodComm _ _)]
    exact uprob_fst (fun ρ : V'.Coins x.length =>
      T (pairEncode (pairEncode x z) (pairEncode (List.ofFn ρ) [])))
  have h2 : uprob (fun ρ : (NUPPT.ofPolyTimeUniform hF V'.coins).Coins x.length =>
      T ((NUPPT.ofPolyTimeUniform hF V'.coins).simulate x z ρ)) =
      uprob (fun ρ : V'.Coins x.length =>
        T (pairEncode (pairEncode x z) (pairEncode (List.ofFn ρ) []))) := by
    refine OneWay.uprob_congr fun ρ => ?_
    rw [NUPPT.simulate_eq, NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
    simp [NUPPT.inArg_eq, NUPPT.inCoins_eq, NUPPT.advInput_eq]
  simp only [h2]
  rw [abs_nonpos_iff, sub_eq_zero]
  exact h1

/-! ### Retrying an aborting simulator -/

namespace AbortRetry

open EncodingMachines Finset Complexity.StateLoop

/-- One attempt of the retrying simulator on its machine layout
`w = ⟨⟨⟨1^n, y⟩, α⟩, r⟩` at the index `t`: the simulator `S` at parameter `n = |1^n|` on the
argument `y`, with empty advice and the `t`-th block of `S.coinLen n` coins of `r`. -/
def attempt (S : NUPPT) (w : List Bool) (t : ℕ) : List Bool :=
  S.output (NUPPT.layout (NUPPT.inParam w) (NUPPT.inArg w) []
    (((NUPPT.inCoins w).drop (t * S.coinLen (NUPPT.inParam w).length)).take
      (S.coinLen (NUPPT.inParam w).length)))

/-- One attempt unfolded: `attempt S w t` is `S.output` on the layout with parameter
`inParam w`, argument `inArg w`, empty advice and coins
`((inCoins w).drop (t · c)).take c`, where `c = S.coinLen |inParam w|`. -/
theorem attempt_eq (S : NUPPT) (w : List Bool) (t : ℕ) :
    attempt S w t = S.output (NUPPT.layout (NUPPT.inParam w) (NUPPT.inArg w) []
      (((NUPPT.inCoins w).drop (t * S.coinLen (NUPPT.inParam w).length)).take
        (S.coinLen (NUPPT.inParam w).length))) :=
  rfl

/-- The retrying simulator on its machine layout `w = ⟨⟨⟨1^n, y⟩, α⟩, r⟩`
(for the abort form of [Gol01, Definition 4.3.1], amplified by repetition): the
first of the `n` attempts that does not output `⊥ = []` (the first accepted index,
`EncodingMachines.firstIdx`), or `⊥` if every attempt aborts. -/
noncomputable def retry (S : NUPPT) (w : List Bool) : List Bool :=
  if firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length <
      (NUPPT.inParam w).length then
    attempt S w (firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length)
  else []

/-- The retrying simulator unfolded: with `N = |inParam w|` and `i` the least index below `N`
whose attempt is not `⊥ = []` (`firstIdx`, equal to `N` if there is none), `retry S w` is
attempt `i` if `i < N`, and `[]` otherwise. -/
theorem retry_eq (S : NUPPT) (w : List Bool) :
    retry S w =
      if firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length <
          (NUPPT.inParam w).length then
        attempt S w (firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length)
      else [] :=
  rfl

/-- If attempt `i < |inParam w|` is the first that does not abort (`attempt S w i ≠ []`, and
`attempt S w j = []` for every `j < i`), then `retry S w` is attempt `i`.

**Proof sketch.** `firstIdx` of the non-abort test is `i` (`firstIdx_eq_of`); rewrite
`retry_eq` with it and take the `i < |inParam w|` branch. -/
theorem retry_eq_attempt {S : NUPPT} {w : List Bool} {i : ℕ}
    (hi : i < (NUPPT.inParam w).length) (hne : attempt S w i ≠ [])
    (hmin : ∀ j < i, attempt S w j = []) : retry S w = attempt S w i := by
  have h : firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length = i :=
    firstIdx_eq_of hi (decide_eq_true hne) fun j hj => decide_eq_false (not_not.2 (hmin j hj))
  rw [retry_eq, h, if_pos hi]

/-- If all `|inParam w|` attempts abort (`attempt S w t = []` for every `t < |inParam w|`),
then `retry S w = []`. Together with `retry_eq_attempt` this covers every input.

**Proof sketch.** `firstIdx` of the non-abort test is `|inParam w|` (`firstIdx_eq_of_forall`);
rewrite `retry_eq` with it and take the `else` branch. -/
theorem retry_eq_nil {S : NUPPT} {w : List Bool}
    (h : ∀ t < (NUPPT.inParam w).length, attempt S w t = []) : retry S w = [] := by
  have h' : firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length =
      (NUPPT.inParam w).length :=
    firstIdx_eq_of_forall fun t ht => decide_eq_false (not_not.2 (h t ht))
  rw [retry_eq, h', if_neg (lt_irrefl _)]

/-- One attempt is polynomial-time on the indexed layout `⟨1^t, w⟩`.

**Proof sketch.** The block `(r.drop (t · c)).take c` with `c = S.coinLen n` in unary
(`unaryPoly_comp`, `unaryMul_poly`, `polyTimeComputable_pairDropPoly`, `truncate_poly`), the
layout (`NUPPT.polyTimeComputable_layout`) and the machine of `S`
(`NUPPT.polyTimeComputable_output`). -/
theorem attempt_poly (S : NUPPT) :
    PolyTimeComputable fun u => attempt S (pairSndD u) (pairFstD u).length := by
  have congr : ∀ {f g : List Bool → List Bool}, PolyTimeComputable f → (∀ w, g w = f w) →
      PolyTimeComputable g := fun hf h => by rw [show _ = _ from funext h]; exact hf
  have hpar : PolyTimeComputable fun u => NUPPT.inParam (pairSndD u) :=
    NUPPT.polyTimeComputable_inParam.comp polyTimeComputable_pairSndD
  have hr : PolyTimeComputable fun u => NUPPT.inCoins (pairSndD u) :=
    NUPPT.polyTimeComputable_inCoins.comp polyTimeComputable_pairSndD
  have hc : PolyTimeComputable fun u =>
      List.replicate (S.coinLen (NUPPT.inParam (pairSndD u)).length) true :=
    unaryPoly_comp S.coins hpar
  have ht : PolyTimeComputable fun u => List.replicate (pairFstD u).length true :=
    unaryLength_poly polyTimeComputable_pairFstD
  have hdrop : PolyTimeComputable fun u => (NUPPT.inCoins (pairSndD u)).drop
      ((pairFstD u).length * S.coinLen (NUPPT.inParam (pairSndD u)).length) :=
    congr ((polyTimeComputable_pairDropPoly .var).comp ((unaryMul_poly ht hc).pairEncode hr))
      fun u => by simp
  have hblk := truncate_poly hdrop hc
  have hlay := NUPPT.polyTimeComputable_layout hpar
    (NUPPT.polyTimeComputable_inArg.comp polyTimeComputable_pairSndD)
    (polyTimeComputable_const []) hblk
  exact congr (S.polyTimeComputable_output.comp hlay) fun u => rfl

/-- **The retrying simulator is polynomial-time** as a function of its layout: the first
non-aborting index is `EncodingMachines.polyTimeComputable_firstIdx` (an instance of the
repetition lemma `Complexity.polyTimeComputable_iterateFind`) with the test of
`attempt_poly`, and the output is that attempt (`attempt_poly` at the found index) or `[]`
(`polyTimeComputable_ite`). -/
theorem retry_poly (S : NUPPT) : PolyTimeComputable (retry S) := by
  have congr : ∀ {f g : List Bool → List Bool}, PolyTimeComputable f → (∀ w, g w = f w) →
      PolyTimeComputable g := fun hf h => by rw [show _ = _ from funext h]; exact hf
  have hatt := attempt_poly S
  have hp : PolyTimeComputable fun u =>
      [decide (attempt S (pairSndD u) (pairFstD u).length ≠ [])] :=
    congr (ltTest_poly (unaryConst_poly 0) (unaryLength_poly hatt)) fun u => by
      simp [List.length_pos_iff]
  have hN : PolyTimeComputable fun w => List.replicate (NUPPT.inParam w).length true :=
    unaryLength_poly NUPPT.polyTimeComputable_inParam
  have hidx := polyTimeComputable_firstIdx (p := fun w t => decide (attempt S w t ≠ [])) hp hN
  have hsel : PolyTimeComputable fun w => attempt S w
      (firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length) :=
    congr (hatt.comp (hidx.pairEncode polyTimeComputable_id)) fun w => by simp
  refine congr (polyTimeComputable_ite (ltTest_poly hidx hN) hsel (polyTimeComputable_const []))
    fun w => ?_
  simp only [retry, decide_eq_true_eq]

/-- **The retrying simulator is a uniform PPT**: `NUPPT.ofPolyTimeUniform` of `retry_poly`
with `|x|` blocks of `S.coinLen |x|` coins; on `(x, z)` it computes `retry S` on the layout
`⟨⟨⟨1^{|x|}, ⟨x, z⟩⟩, []⟩, r⟩` (`NUPPT.runAtL_ofPolyTimeUniform`). -/
theorem exists_retrySimulator (S : NUPPT) :
    ∃ S' : NUPPT, S'.Uniform ∧ S'.coins = .mul .var S.coins ∧
      ∀ x z (r : S'.Coins x.length), S'.simulate x z r =
        retry S (NUPPT.layout (List.replicate x.length true) (pairEncode x z) [] (List.ofFn r)) :=
  ⟨NUPPT.ofPolyTimeUniform (retry_poly S) (.mul .var S.coins),
    NUPPT.ofPolyTimeUniform_uniform _ _, rfl, fun x z r => by
      rw [NUPPT.simulate_eq, NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
      rfl⟩

/-- The first hit of `K` draws read through `EncodingMachines.firstIdx`: if `a t` is `g` of
the `t`-th draw and `q t` tests `E` on it (for `t < K`), then the first hit mapped by `g` and
defaulted to `d` is `a` at the first index accepted by `q`, or `d` if there is none.

**Proof sketch.** If `i := firstIdx q K < K`, the draw `i` is in `E` (`q_firstIdx`) and no
earlier draw is (`firstIdx_min`); splitting `List.finRange K` at `i`
(`List.drop_eq_getElem_cons`, `List.take_append_drop`, `List.getElem_finRange`) gives
`firstHit E xs = some (xs i)` by `List.findSome?_eq_some_iff`. Otherwise no draw is in `E`
(`firstIdx_eq_iff`) and `firstHit E xs = none` (`firstHit_eq_none_iff`). -/
theorem firstHit_map_getD_eq {α β : Type*} (E : α → Prop) [DecidablePred E] {K : ℕ}
    (xs : Fin K → α) (g : α → β) (d : β) (a : ℕ → β) (q : ℕ → Bool)
    (ha : ∀ t (ht : t < K), a t = g (xs ⟨t, ht⟩))
    (hq : ∀ t (ht : t < K), q t = decide (E (xs ⟨t, ht⟩))) :
    ((firstHit E xs).map g).getD d = if firstIdx q K < K then a (firstIdx q K) else d := by
  split_ifs with h
  · set i := firstIdx q K with hi_def
    have hEi : E (xs ⟨i, h⟩) := by
      have := q_firstIdx h
      rw [hq i h] at this
      exact of_decide_eq_true this
    have hmin : ∀ j (hj : j < i), ¬ E (xs ⟨j, hj.trans h⟩) := fun j hj hE => by
      have := firstIdx_min hj
      rw [hq j (hj.trans h)] at this
      exact absurd (decide_eq_true hE) (by rw [this]; decide)
    have hsome : firstHit E xs = some (xs ⟨i, h⟩) := by
      simp only [firstHit_eq]
      rw [List.findSome?_eq_some_iff]
      refine ⟨(List.finRange K).take i, ⟨i, h⟩, (List.finRange K).drop (i + 1), ?_, ?_, ?_⟩
      · have hlen : i < (List.finRange K).length := by simpa using h
        have hsplit : List.finRange K = (List.finRange K).take i ++
            (List.finRange K)[i] :: (List.finRange K).drop (i + 1) := by
          rw [← List.drop_eq_getElem_cons hlen, List.take_append_drop]
        rw [List.getElem_finRange] at hsplit
        exact hsplit
      · simp [hEi]
      · intro j hj
        obtain ⟨k, hk, rfl⟩ := List.mem_take_iff_getElem.1 hj
        have hki : k < i := lt_of_lt_of_le hk (min_le_left _ _)
        simp [hmin k hki]
    rw [hsome, ha i h]
    rfl
  · have hall := firstIdx_eq_iff.1 (le_antisymm firstIdx_le (not_lt.1 h))
    have hnone : firstHit E xs = none := (firstHit_eq_none_iff E xs).2 fun t hE => by
      have := hall t t.isLt
      rw [hq t t.isLt] at this
      exact absurd (decide_eq_true hE) (by rw [this]; decide)
    rw [hnone]
    rfl

/-- **Retrying an aborting sampler** (amplification by repetition): let `g` be a
sampler on a finite uniform space `Ω`, `E` the event "`g` does not abort", with
`Pr[¬ E] ≤ 1/2`, and suppose the output of `g` conditioned on `E` has the law of the sampler
`Y`. Then the output of `g` on the first of `K` independent draws in `E` (the default `d₀` if
there is none) is within `2^{-K}` of `Y`.

**Proof sketch.** Let `p := Pr[E] ≥ 1/2` and `f := (1 - p)^K`, the probability that no draw
is in `E` (`uprob_firstHit_none`). Each `a ∈ E` is the first hit with the same probability
`q₀` (`firstHit_uniform_of_some`), so for a test set `T`, splitting over the fibres of
`firstHit` (`uprob_comp_eq_sum_fiber`, `Fintype.sum_option`),
`Pr[T(retry)] = [T d₀] · f + q₀ · #{a ∈ E : T (g a)}`, and with `T := ⊤`,
`1 = f + q₀ · #E`. The conditional-law hypothesis times `|Ω|` is
`Pr[T(Y)] · #E = #{a ∈ E : T (g a)}`, so `Pr[T(retry)] = [T d₀] · f + (1 - f) · Pr[T(Y)]`
(`linear_combination`) and `|Pr[T(Y)] - Pr[T(retry)]| = f · |Pr[T(Y)] - [T d₀]| ≤ f ≤ 2^{-K}`. -/
theorem statClose_retry {Ω τ : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω] [Fintype τ]
    (E : Ω → Prop) [DecidablePred E] (g : Ω → List Bool) (Y : τ → List Bool) (d₀ : List Bool)
    (habort : uprob (fun ω => ¬ E ω) ≤ 1 / 2)
    (hcond : ∀ T : List Bool → Prop,
      uprob (fun t => T (Y t)) * uprob E = uprob (fun ω => E ω ∧ T (g ω)))
    (K : ℕ) :
    StatClose Y (fun ws : Fin K → Ω => ((firstHit E ws).map g).getD d₀) ((2 : ℝ)⁻¹ ^ K) := by
  classical
  intro T
  have hpE : uprob E = 1 - uprob (fun ω => ¬ E ω) := by rw [uprob_not]; ring
  obtain ⟨d, hd⟩ : ∃ d, E d := by
    by_contra hne
    push_neg at hne
    have h0 : uprob E = 0 := by
      rw [← uprob_false (α := Ω)]
      exact OneWay.uprob_congr fun ω => ⟨fun h => hne ω h, False.elim⟩
    linarith
  have hsome : ∀ a, E a → uprob (fun xs : Fin K → Ω => firstHit E xs = some a) =
      uprob (fun xs : Fin K → Ω => firstHit E xs = some d) :=
    fun a ha => firstHit_uniform_of_some E K ha hd
  have hnot : ∀ a, ¬ E a → uprob (fun xs : Fin K → Ω => firstHit E xs = some a) = 0 := by
    intro a ha
    rw [← uprob_false (α := Fin K → Ω)]
    exact OneWay.uprob_congr fun xs => ⟨fun h => ha (firstHit_eq_some_imp E h), False.elim⟩
  have hdec : ∀ S' : Option Ω → Prop, uprob (fun xs : Fin K → Ω => S' (firstHit E xs)) =
      (if S' none then (1 - uprob E) ^ K else 0) +
        uprob (fun xs : Fin K → Ω => firstHit E xs = some d) *
          (univ.filter fun a => E a ∧ S' (some a)).card := by
    intro S'
    rw [uprob_comp_eq_sum_fiber (firstHit E) S', sum_filter, Fintype.sum_option,
      uprob_firstHit_none E K]
    congr 1
    rw [mul_comm, ← nsmul_eq_mul, ← sum_const, sum_filter]
    refine sum_congr rfl fun a _ => ?_
    by_cases hSa : S' (some a)
    · by_cases hEa : E a
      · simp [hSa, hEa, hsome a hEa]
      · simp [hSa, hEa, hnot a hEa]
    · simp [hSa]
  have hsim := hdec fun o => T ((o.map g).getD d₀)
  have htot := hdec fun _ => True
  rw [uprob_true] at htot
  simp only [Option.map_none, Option.getD_none, Option.map_some, Option.getD_some, if_true,
    and_true] at hsim htot
  -- the conditional law in counting form
  have hcard : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hc := hcond T
  rw [uprob_eq_card_filter E, uprob_eq_card_filter (fun ω => E ω ∧ T (g ω)), mul_div_assoc',
    div_left_inj' hcard] at hc
  generalize uprob (fun xs : Fin K → Ω => firstHit E xs = some d) = q₀ at hsim htot
  generalize hf : (1 - uprob E) ^ K = f at hsim htot
  have hY0 := uprob_nonneg (fun t => T (Y t))
  have hY1 := uprob_le_one (fun t => T (Y t))
  have hsimeq : uprob (fun xs : Fin K → Ω => T (((firstHit E xs).map g).getD d₀)) =
      (if T d₀ then f else 0) + (1 - f) * uprob (fun t => T (Y t)) := by
    rw [hsim]
    linear_combination (-q₀) * hc + (-uprob (fun t => T (Y t))) * htot
  have hf0 : 0 ≤ f := hf ▸ pow_nonneg (by linarith [uprob_le_one E]) K
  have hfK : f ≤ (2 : ℝ)⁻¹ ^ K :=
    hf ▸ pow_le_pow_left₀ (by linarith [uprob_le_one E]) (by linarith) K
  show |uprob (fun t => T (Y t)) -
    uprob (fun xs : Fin K → Ω => T (((firstHit E xs).map g).getD d₀))| ≤ (2 : ℝ)⁻¹ ^ K
  rw [hsimeq, abs_le]
  split_ifs <;> constructor <;> nlinarith

/-- The probability that the retrying simulator's attempt aborts is the complement of its
success probability (a restatement of `PerfectZKAbort`'s first clause for
`AbortRetry.statClose_retry`). -/
theorem uprob_not_ne_nil_le {Ω : Type*} [Fintype Ω] (g : Ω → List Bool)
    (h : uprob (fun ω => g ω = []) ≤ 1 / 2) : uprob (fun ω => ¬ g ω ≠ []) ≤ 1 / 2 := by
  simpa using h

end AbortRetry

open AbortRetry in
/-- **Perfect zero-knowledge with abort implies statistical zero-knowledge with error
`2^{-|x|}`** (the abort form of [Gol01, Definition 4.3.1], amplified by repetition)
(ruling G3-4 of gate 03): retry the aborting simulator on `|x|` disjoint coin blocks and
output the first non-`⊥` result.

**Proof sketch.** For an efficient `V'` take the aborting simulator `S` of `h`; the
retrying simulator `S'` of `AbortRetry.exists_retrySimulator` is a uniform PPT with `|x|`
blocks of `S.coinLen |x|` coins. Read its tape as `|x|` independent blocks (the bijection
`e` built from `finCongr`, `finProdFinEquiv` and `Equiv.curry`, through
`StatClose.comp_equiv_right`): the `t`-th slice of the tape is `List.ofFn` of block `t`, so
attempt `t` is `S` on block `t` (`S` is uniform, so its advice is `[]`), and the retrying
simulator is the first non-`⊥` attempt (`AbortRetry.firstHit_map_getD_eq`). The two clauses
of `h` are the hypotheses of `AbortRetry.statClose_retry` with `K = |x|`. -/
theorem PerfectZKAbort.statZK {π : Protocol} {R : List Bool → List Bool → Prop}
    (h : PerfectZKAbort π R) : StatZK π R (fun n => (2 : ℝ)⁻¹ ^ n) := by
  intro V' hV'
  obtain ⟨S, hSu, hS⟩ := h V' hV'
  obtain ⟨S', hS'u, hS'c, hS'⟩ := exists_retrySimulator S
  refine ⟨S', hS'u, fun x y z hxy => ?_⟩
  obtain ⟨habort, hcond⟩ := hS x y z hxy
  have hlen : S'.coinLen x.length = x.length * S.coinLen x.length := by
    simp only [NUPPT.coinLen_eq, hS'c, PolyExpr.eval_mul, PolyExpr.eval_var]
  -- the tape of `S'` as `|x|` blocks of `S.coinLen |x|` coins
  let e : S'.Coins x.length ≃ (Fin x.length → S.Coins x.length) :=
    ((Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)).trans
      (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool))).trans (Equiv.curry _ _ _)
  have hblock : ∀ (r : S'.Coins x.length) (t : ℕ) (ht : t < x.length),
      ((List.ofFn r).drop (t * S.coinLen x.length)).take (S.coinLen x.length) =
        List.ofFn (e r ⟨t, ht⟩) := by
    intro r t ht
    have hle : t * S.coinLen x.length + S.coinLen x.length ≤ x.length * S.coinLen x.length := by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right _ ht
    refine List.ext_getElem ?_ fun j h₁ h₂ => ?_
    · simp only [List.length_take, List.length_drop, List.length_ofFn, hlen]
      omega
    · simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]
      simp only [e, Equiv.trans_apply, Equiv.arrowCongr_apply, Equiv.coe_refl,
        Function.comp_apply, Equiv.symm_symm, Equiv.curry_apply, Function.curry_apply]
      congr 1
      ext
      simp [finProdFinEquiv_apply_val]
      ring
  have hatt : ∀ (r : S'.Coins x.length) (t : ℕ) (ht : t < x.length),
      attempt S (NUPPT.layout (List.replicate x.length true) (pairEncode x z) [] (List.ofFn r)) t =
        S.simulate x z (e r ⟨t, ht⟩) := by
    intro r t ht
    simp only [attempt, NUPPT.inParam_layout, NUPPT.inArg_layout, NUPPT.inCoins_layout,
      List.length_replicate]
    rw [hblock r t ht, NUPPT.simulate_eq, NUPPT.runAt_eq, NUPPT.runAtL_eq_output_layout, hSu]
  have heq : ∀ r : S'.Coins x.length, S'.simulate x z r =
      ((firstHit (fun ω => S.simulate x z ω ≠ []) (e r)).map (S.simulate x z)).getD [] := by
    intro r
    rw [hS' x z r, firstHit_map_getD_eq (fun ω => S.simulate x z ω ≠ []) (e r)
      (S.simulate x z) []
      (attempt S (NUPPT.layout (List.replicate x.length true) (pairEncode x z) [] (List.ofFn r)))
      (fun t => decide (attempt S
        (NUPPT.layout (List.replicate x.length true) (pairEncode x z) [] (List.ofFn r)) t ≠ []))
      (hatt r) (fun t ht => by simp only [hatt r t ht])]
    simp only [retry, NUPPT.inParam_layout, List.length_replicate]
  have key := (statClose_retry (fun ω => S.simulate x z ω ≠ []) (S.simulate x z)
    (fun r : (π.withV V').ExecCoins π.P x => ((π.withV V').viewV x y z r).encode) []
    (uprob_not_ne_nil_le _ habort) hcond x.length).comp_equiv_right e
  intro T
  have hu : uprob (fun t : S'.Coins x.length => T (S'.simulate x z t)) =
      uprob (fun t : S'.Coins x.length => T (((firstHit (fun ω => S.simulate x z ω ≠ []) (e t)).map
        (S.simulate x z)).getD [])) :=
    OneWay.uprob_congr fun t => by rw [heq t]
  rw [hu]
  exact key T

/-- **Perfect zero-knowledge with abort implies zero-knowledge** (ruling G3-4 of gate 03):
`PerfectZKAbort.statZK` and `StatZK.zk` with the negligible error `2^{-n}`
(`negligible_two_pow_neg`). -/
theorem PerfectZKAbort.zk {π : Protocol} {R : List Bool → List Bool → Prop}
    (h : PerfectZKAbort π R) : ZK π R :=
  h.statZK.zk negligible_two_pow_neg

/-! ### Negligibility in the instance length (Inf-4.4) -/

/-- For `a > 1` and `C > 0` the function `N ↦ a^{-√(N / C)}` (with `Nat.sqrt` and natural
division) is negligible in `N` (Inf-4.4): the per-vertex error bounds `2^{-n}` and `e^{-n}` of
the graph protocols, whose instances have length `|x| ≥ n² / C`, are negligible in `|x|`.

**Proof sketch.** Fix `c`. Put `t := Nat.sqrt (N / C)`; then `N / C < (t + 1)²`
(`Nat.lt_succ_sqrt`), so `N < C (t + 1)² + C ≤ 2 C (t + 1)²` and
`N ^ c ≤ (2 C)^c (t + 1)^{2c}`. By `tendsto_pow_const_div_const_pow_of_one_lt`
(as in `negligible_two_pow_neg`), `(t + 1)^{2c} / a^{t+1} → 0`, so there is `t₀` with
`(2 C)^c · a · (t + 1)^{2c} < a^{t+1}` for `t ≥ t₀`, i.e. `(2C)^c (t+1)^{2c} < a^t`; and
`t ≥ t₀` as soon as `N ≥ C (t₀ + 1)²` (`Nat.le_sqrt`). Hence for such `N`,
`a⁻¹ ^ t = 1 / a^t < 1 / ((2C)^c (t+1)^{2c}) ≤ 1 / N^c`. -/
theorem negligible_inv_pow_sqrt_div {a : ℝ} (ha : 1 < a) {C : ℕ} (hC : 0 < C) :
    Negligible fun N => a⁻¹ ^ Nat.sqrt (N / C) := by
  intro c
  have ha0 : (0 : ℝ) < a := zero_lt_one.trans ha
  have hCr : (0 : ℝ) < (C : ℝ) ^ c := by positivity
  have hpos : (0 : ℝ) < 1 / ((C : ℝ) ^ c * a) := by positivity
  have ht := tendsto_pow_const_div_const_pow_of_one_lt (2 * c) ha
  obtain ⟨t₀, ht₀⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds hpos))
  refine ⟨max (C * t₀ * t₀) 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have hNC : C * t₀ * t₀ ≤ N := le_of_max_le_left hN
  set t := Nat.sqrt (N / C) with ht_def
  -- `t₀ ≤ t` since `C t₀² ≤ N`
  have ht0 : t₀ ≤ t := by
    rw [ht_def, Nat.le_sqrt, Nat.le_div_iff_mul_le hC]
    calc t₀ * t₀ * C = C * t₀ * t₀ := by ring
      _ ≤ N := hNC
  -- `N < (t + 1)² C`
  have hNlt : N < (t + 1) * (t + 1) * C :=
    (Nat.div_lt_iff_lt_mul hC).1 (Nat.lt_succ_sqrt (N / C))
  have hNltR : (N : ℝ) < ((t : ℝ) + 1) ^ 2 * C := by
    have := hNlt
    rw [← pow_two] at this
    exact_mod_cast this
  -- the limit at `t + 1`: `(t + 1)^{2c} C^c < a^t`
  have hlim := ht₀ (t + 1) (by omega)
  have hlim' : ((t : ℝ) + 1) ^ (2 * c) * ((C : ℝ) ^ c * a) < a ^ (t + 1) := by
    have hapos : (0 : ℝ) < a ^ (t + 1) := pow_pos ha0 _
    rw [div_lt_iff₀ hapos] at hlim
    push_cast at hlim
    calc ((t : ℝ) + 1) ^ (2 * c) * ((C : ℝ) ^ c * a)
        < 1 / ((C : ℝ) ^ c * a) * a ^ (t + 1) * ((C : ℝ) ^ c * a) := by
          gcongr
      _ = a ^ (t + 1) := by field_simp
  have hkey : ((t : ℝ) + 1) ^ (2 * c) * (C : ℝ) ^ c < a ^ t := by
    rw [pow_succ, ← mul_assoc] at hlim'
    exact lt_of_mul_lt_mul_right hlim' ha0.le
  -- `N^c ≤ (t + 1)^{2c} C^c`
  have hNpow : (N : ℝ) ^ c ≤ ((t : ℝ) + 1) ^ (2 * c) * (C : ℝ) ^ c := by
    rw [pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg N) hNltR.le c
  have hNpos : (0 : ℝ) < (N : ℝ) ^ c := pow_pos (by exact_mod_cast hN1) c
  show |a⁻¹ ^ t| < 1 / (N : ℝ) ^ c
  rw [abs_of_pos (pow_pos (inv_pos.mpr ha0) t), inv_pow, ← one_div]
  exact one_div_lt_one_div_of_lt hNpos (hNpow.trans_lt hkey)

/-- `2^{-√(N / C)}` is negligible in `N` (Inf-4.4, the graph-isomorphism bound). -/
theorem negligible_two_pow_neg_sqrt_div {C : ℕ} (hC : 0 < C) :
    Negligible fun N => (2 : ℝ)⁻¹ ^ Nat.sqrt (N / C) :=
  negligible_inv_pow_sqrt_div one_lt_two hC

/-- `e^{-√(N / C)}` is negligible in `N` (Inf-4.4, the 3-colouring bound). -/
theorem negligible_exp_neg_sqrt_div {C : ℕ} (hC : 0 < C) :
    Negligible fun N => Real.exp (-(Nat.sqrt (N / C) : ℝ)) := by
  have h1 : (1 : ℝ) < Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  refine (negligible_inv_pow_sqrt_div h1 hC).mono ⟨0, fun n _ => le_of_eq ?_⟩
  congr 1
  rw [Real.exp_neg, inv_pow, ← Real.exp_nat_mul, mul_one]

/-- A function bounded by `a^{-√(N / C)}` is negligible (Inf-4.4 in the form used by the
protocol theorems: a bound `a^{-n}` in the number of vertices `n ≥ √(|x| / C)` is a bound
`a^{-√(|x| / C)}` in the instance length). -/
theorem negligible_of_le_inv_pow_sqrt_div {a : ℝ} (ha : 1 < a) {C : ℕ} (hC : 0 < C)
    {ν : ℕ → ℝ} (hν : ∀ N, |ν N| ≤ a⁻¹ ^ Nat.sqrt (N / C)) : Negligible ν :=
  (negligible_inv_pow_sqrt_div ha hC).mono ⟨0, fun N _ => by
    rw [abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (zero_le_one.trans ha.le)) _)]
    exact hν N⟩

/-- A bound `a^{-n}` in a parameter `n ≥ √(N / C)` transfers to `a^{-√(N / C)}`
(monotonicity of `a⁻¹ ^ ·` for `a > 1`). -/
theorem inv_pow_le_inv_pow_sqrt_div {a : ℝ} (ha : 1 < a) {C N n : ℕ}
    (hn : Nat.sqrt (N / C) ≤ n) : a⁻¹ ^ n ≤ a⁻¹ ^ Nat.sqrt (N / C) :=
  pow_le_pow_of_le_one (inv_nonneg.mpr (zero_le_one.trans ha.le)) (inv_le_one_of_one_le₀ ha.le) hn

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Composability/SequentialZK/SimulatorMachine.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Composability.SequentialZK.PhaseView
import TCSlib.Cryptography.Composability.SequentialZK.WrappedVerifier
import TCSlib.Cryptography.ZeroKnowledge.Defs
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.EfficiencyRep

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The strict polynomial-time sequential phase simulator

A single verifier tape and independent blocks of the phase simulator's tape drive a sequence
of canonical bounded phase normalizations. The semantic recursion `phasePrefix` specifies
that sequence. Its machine implementation instantiates the published counted-loop host
`ColMachines.polyTimeComputable_loopState'`; it introduces no new control host or machine.

## Main definitions

* `phasePrefix`: the normalized received-prover prefix after a specified number of phases.

## Main results

* `phasePrefix_eq`, `phasePrefix_zero`, `phasePrefix_succ`: exact semantic readers.
* `length_phasePrefix`, `length_le_of_mem_phasePrefix`, `length_encodeMsgs_phasePrefix_le`:
  exact slot count and uniform message/encoding bounds.
* `phasePrefix_poly`: polynomial-time assembly of the entire normalized prefix.
* `exists_phaseSimulator`: a uniform simulator with one verifier tape and fresh phase tapes.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.2.1, Theorem 175.1.
* [Gol01] O. Goldreich, *Foundations of Cryptography, Volume I: Basic Tools*, Cambridge
  University Press, 2001, §4.3.4.
-/

namespace TCSlib.Cryptography.SequentialZK

open Complexity Turing

/-- The normalized prefix after `i` phases uses simulator `S`, round/bit bounds `k,B`,
orientation `verifierFirst`, input/auxiliary words `x,z`, one verifier tape `rV`, and phase-tape
source `rS`. Each phase calls `S` on `phaseAux z rV i pre`, retains exactly
`p = if verifierFirst then k(|x|)/2 else (k(|x|)+1)/2` bounded real messages, and appends
`k(|x|)-p` empty fillers. [PS10, Theorem 175.1, the sequential simulator].

This recursion is the public mathematical specification; its polynomial-time realization
below is an instance of the existing counted-loop host, rather than a new control host. -/
def phasePrefix (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
    (x z rV rS : List Bool) : ℕ → List (List Bool)
  | 0 => []
  | i + 1 =>
    let pre := phasePrefix S k B verifierFirst x z rV rS i
    let aux := phaseAux z rV i pre
    let p := if verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2
    pre ++ (normalizePhaseMsgs x aux p (B.eval x.length)
      (S.runAtL x.length (pairEncode x aux) (coinBlock (S.coinLen x.length) i rS)) ++
        List.replicate (k.eval x.length - p) [])

/-- Before any phase, `phasePrefix S k B verifierFirst x z rV rS 0 = []`. -/
theorem phasePrefix_zero (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
    (x z rV rS : List Bool) : phasePrefix S k B verifierFirst x z rV rS 0 = [] := rfl

/-- Phase `i+1` extends `pre = phasePrefix S k B verifierFirst x z rV rS i` with the normalized
output of `S.runAtL |x| (pairEncode x (phaseAux z rV i pre))` on coin block `i`, then the
`k(|x|)-p` empty fillers, for `p = if verifierFirst then k(|x|)/2 else (k(|x|)+1)/2`. -/
theorem phasePrefix_succ (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
    (x z rV rS : List Bool) (i : ℕ) :
    phasePrefix S k B verifierFirst x z rV rS (i + 1) =
      let pre := phasePrefix S k B verifierFirst x z rV rS i
      let aux := phaseAux z rV i pre
      let p := if verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2
      pre ++ (normalizePhaseMsgs x aux p (B.eval x.length)
        (S.runAtL x.length (pairEncode x aux) (coinBlock (S.coinLen x.length) i rS)) ++
          List.replicate (k.eval x.length - p) []) := rfl

/-- The exhaustive equation for `phasePrefix … i` is `[]` at zero; at `j+1`, with
`pre = phasePrefix … j`, it appends the canonical normalized `S.runAtL` output at
`phaseAux z rV j pre` on coin block `j`, followed by the `k(|x|)-p` empty fillers. -/
theorem phasePrefix_eq (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
    (x z rV rS : List Bool) (i : ℕ) :
    phasePrefix S k B verifierFirst x z rV rS i =
      match i with
      | 0 => []
      | j + 1 =>
        let pre := phasePrefix S k B verifierFirst x z rV rS j
        let aux := phaseAux z rV j pre
        let p := if verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2
        pre ++ (normalizePhaseMsgs x aux p (B.eval x.length)
          (S.runAtL x.length (pairEncode x aux) (coinBlock (S.coinLen x.length) j rS)) ++
            List.replicate (k.eval x.length - p) []) :=
  match i with
  | 0 => phasePrefix_zero S k B verifierFirst x z rV rS
  | j + 1 => phasePrefix_succ S k B verifierFirst x z rV rS j

/-- If phase coin block `i` equals `List.ofFn r`, phase `i+1` calls precisely
`S.simulate x (phaseAux z rV i pre) r`, with `pre` the earlier phase prefix.
`phasePrefix S k B verifierFirst x z rV rS (i + 1) = let pre := phasePrefix S k B verifierFirst x z
rV rS i; let aux := phaseAux z rV i pre; let p := if verifierFirst then k.eval x.length / 2 else
(k.eval x.length + 1) / 2; pre ++ (normalizePhaseMsgs x aux p (B.eval x.length) (S.simulate x aux r)
++ List.replicate (k.eval x.length - p) [])`. -/
theorem phasePrefix_succ_simulate (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
    (x z rV rS : List Bool) (i : ℕ) (r : S.Coins x.length)
    (hcoins : coinBlock (S.coinLen x.length) i rS = List.ofFn r) :
    phasePrefix S k B verifierFirst x z rV rS (i + 1) =
      let pre := phasePrefix S k B verifierFirst x z rV rS i
      let aux := phaseAux z rV i pre
      let p := if verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2
      pre ++ (normalizePhaseMsgs x aux p (B.eval x.length) (S.simulate x aux r) ++
        List.replicate (k.eval x.length - p) []) := by
  rw [phasePrefix_succ]
  dsimp only
  rw [hcoins, ← NUPPT.runAt_eq, ← NUPPT.simulate_eq]

/-- After `i` phases the normalized prefix has exactly `i * k(|x|)` messages:
`(phasePrefix S k B verifierFirst x z rV rS i).length = i * k.eval x.length`. -/
theorem length_phasePrefix (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
    (x z rV rS : List Bool) (i : ℕ) :
    (phasePrefix S k B verifierFirst x z rV rS i).length = i * k.eval x.length := by
  induction i with
  | zero => rw [phasePrefix_zero, List.length_nil, Nat.zero_mul]
  | succ i ih =>
    rw [phasePrefix_succ]
    dsimp only
    rw [List.length_append, List.length_append, length_normalizePhaseMsgs,
      List.length_replicate, ih, Nat.succ_mul]
    have hp : (if verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2) ≤
        k.eval x.length := by cases verifierFirst <;> simp only [Bool.false_eq_true,
          if_false, if_true] <;> omega
    omega

/-- Every message in `phasePrefix S k B verifierFirst x z rV rS i` has at most `B(|x|)` bits.
`m.length ≤ B.eval x.length`.

**Proof sketch.** Induct on the number of phases. Earlier messages satisfy the induction
hypothesis, normalized real messages satisfy the published bit bound, and every filler is
empty. These are exactly the three portions of the next prefix. -/
theorem length_le_of_mem_phasePrefix (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
    (x z rV rS : List Bool) (i : ℕ) {m : List Bool}
    (hm : m ∈ phasePrefix S k B verifierFirst x z rV rS i) : m.length ≤ B.eval x.length := by
  induction i generalizing m with
  | zero =>
    rw [phasePrefix_zero] at hm
    exact False.elim (List.not_mem_nil hm)
  | succ i ih =>
    rw [phasePrefix_succ] at hm
    dsimp only at hm
    rcases List.mem_append.mp hm with hm | hm
    · exact ih hm
    · rcases List.mem_append.mp hm with hm | hm
      · exact length_le_of_mem_normalizePhaseMsgs _ _ _ _ _ hm
      · have he := (List.mem_replicate.mp hm).2
        subst m
        exact Nat.zero_le _

/-- The encoded prefix after `i` phases has length at most
`i * k(|x|) * (2 * B(|x|) + 2)`, uniformly over every simulator output and tape.
`(Strategy.encodeMsgs (phasePrefix S k B verifierFirst x z rV rS i)).length ≤ i * k.eval x.length *
(2 * B.eval x.length + 2)`. -/
theorem length_encodeMsgs_phasePrefix_le (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
    (x z rV rS : List Bool) (i : ℕ) :
    (Strategy.encodeMsgs (phasePrefix S k B verifierFirst x z rV rS i)).length ≤
      i * k.eval x.length * (2 * B.eval x.length + 2) := by
  have h := CommitmentLemmas.length_encodeMsgs_le
    (phasePrefix S k B verifierFirst x z rV rS i) (B.eval x.length)
    (fun m hm => length_le_of_mem_phasePrefix S k B verifierFirst x z rV rS i hm)
  simpa only [length_phasePrefix] using h

/-- If `N` is polynomial-time in unary, the encoding of `N w` empty messages is
polynomial-time: `w ↦ Strategy.encodeMsgs (List.replicate (N w) [])`.
`PolyTimeComputable fun w => Strategy.encodeMsgs (List.replicate (N w) [])`. -/
theorem encode_emptyMsgs_poly {N : List Bool → ℕ}
    (hN : PolyTimeComputable fun w => List.replicate (N w) true) :
    PolyTimeComputable fun w => Strategy.encodeMsgs (List.replicate (N w) []) := by
  have h := ColMachines.polyTimeComputable_flatMap_range
    (E := fun _ _ => pairEncode ([] : List Bool) [])
    (polyTimeComputable_const (pairEncode ([] : List Bool) [])) hN
  refine h.congr fun w => ?_
  have he : List.replicate (N w) ([] : List Bool) =
      (List.range (N w)).map (fun _ => []) := by
    rw [List.map_const', List.length_range]
  rw [ColMachines.encodeMsgs_eq_flatMap, he, List.flatMap_map]

/-- For a uniform `S`, fixed polynomials `k,B,Q`, orientation `verifierFirst`, and
polynomial-time words `X,Z,RV,RS`, the entire encoded prefix is polynomial-time:
`w ↦ encodeMsgs (phasePrefix S k B verifierFirst (X w) (Z w) (RV w) (RS w)
(Q.eval (X w).length))`. [PS10, Theorem 175.1, strict-PPT sequential simulation].
`PolyTimeComputable fun w => Strategy.encodeMsgs (phasePrefix S k B verifierFirst (X w) (Z w) (RV w)
(RS w) (Q.eval (X w).length))`.

**Proof sketch.** Instantiate the published counted-loop host with the encoded prefix as
state and its existing unary counter as phase index. The step decodes the prior state,
assembles the phase auxiliary input, runs `S` on the selected fresh coin block, canonically
normalizes its output, and appends that phase's real-message encoding and empty fillers.
The state is exactly the encoding of the semantic prefix, by induction using the published
loop equations. Its encoding bound, together with a polynomial bound on `|X w|`, bounds every
genuine orbit state. The existing orbit-bounded counted-loop theorem then gives strict
polynomial time, with no newly constructed host. -/
theorem phasePrefix_poly (S : NUPPT) (hS : S.Uniform) (k B Q : PolyExpr)
    (verifierFirst : Bool) {X Z RV RS : List Bool → List Bool}
    (hX : PolyTimeComputable X) (hZ : PolyTimeComputable Z)
    (hRV : PolyTimeComputable RV) (hRS : PolyTimeComputable RS) :
    PolyTimeComputable fun w => Strategy.encodeMsgs
      (phasePrefix S k B verifierFirst (X w) (Z w) (RV w) (RS w) (Q.eval (X w).length)) := by
  let upd : List Bool → List Bool := fun w =>
    let t := pairFstD w
    let i := (pairFstD (pairSndD w)).length
    let pre := BinArith.decWords (pairSndD (pairSndD w))
    let aux := phaseAux (Z t) (RV t) i pre
    let p := if verifierFirst then k.eval (X t).length / 2 else (k.eval (X t).length + 1) / 2
    pairSndD (pairSndD w) ++
      (Strategy.encodeMsgs (normalizePhaseMsgs (X t) aux p (B.eval (X t).length)
        (S.runAtL (X t).length (pairEncode (X t) aux)
          (coinBlock (S.coinLen (X t).length) i (RS t)))) ++
        Strategy.encodeMsgs (List.replicate (k.eval (X t).length - p) []))
  -- Every component of one update is assembled from published polynomial-time machines.
  have hXt : PolyTimeComputable fun w => X (pairFstD w) := hX.comp polyTimeComputable_pairFstD
  have hZt : PolyTimeComputable fun w => Z (pairFstD w) := hZ.comp polyTimeComputable_pairFstD
  have hRVt : PolyTimeComputable fun w => RV (pairFstD w) := hRV.comp polyTimeComputable_pairFstD
  have hRSt : PolyTimeComputable fun w => RS (pairFstD w) := hRS.comp polyTimeComputable_pairFstD
  have hIword := polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hI := EncodingMachines.unaryLength_poly hIword
  have hstate := polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have hcanonical := polyTimeComputable_encWords_decWords hstate
  have hpre : PolyTimeComputable fun w =>
      Strategy.encodeMsgs (BinArith.decWords (pairSndD (pairSndD w))) :=
    hcanonical.congr fun w => (encodeMsgs_eq_encWords _).symm
  have haux := phaseAux_poly hZt hRVt hI hpre
  have hcoins : PolyTimeComputable fun w =>
      coinBlock (S.coinLen (X (pairFstD w)).length) (pairFstD (pairSndD w)).length
        (RS (pairFstD w)) := by
    simpa only [NUPPT.coinLen_eq] using GI.coinSlice_poly S.coins hXt hIword hRSt
  have hlay := NUPPT.polyTimeComputable_layout (EncodingMachines.unaryLength_poly hXt)
    (hXt.pairEncode haux) (polyTimeComputable_const []) hcoins
  have hsim : PolyTimeComputable fun w =>
      S.runAtL (X (pairFstD w)).length
        (pairEncode (X (pairFstD w)) (phaseAux (Z (pairFstD w)) (RV (pairFstD w))
          (pairFstD (pairSndD w)).length (BinArith.decWords (pairSndD (pairSndD w)))))
        (coinBlock (S.coinLen (X (pairFstD w)).length) (pairFstD (pairSndD w)).length
          (RS (pairFstD w))) := by
    refine (S.polyTimeComputable_output.comp hlay).congr fun w => ?_
    rw [Function.comp_apply, NUPPT.runAtL_eq_output_layout, hS.advice_eq]
    simp only [Function.comp_apply]
  have hK := EncodingMachines.unaryPolyOf_poly k (EncodingMachines.unaryLength_poly hXt)
  have hP : PolyTimeComputable fun w => List.replicate
      (if verifierFirst then k.eval (X (pairFstD w)).length / 2
        else (k.eval (X (pairFstD w)).length + 1) / 2) true := by
    cases verifierFirst
    · simpa only [EncodingMachines.divNum_eq] using EncodingMachines.divNum_poly
        (EncodingMachines.unaryAdd_poly hK (EncodingMachines.unaryConst_poly 1))
        (EncodingMachines.unaryConst_poly 2)
    · simpa only [EncodingMachines.divNum_eq] using
        EncodingMachines.divNum_poly hK (EncodingMachines.unaryConst_poly 2)
  have hbits := EncodingMachines.unaryPolyOf_poly B (EncodingMachines.unaryLength_poly hXt)
  have hnorm := polyTimeComputable_encode_normalizePhaseMsgs hXt haux hsim hP hbits
  have hfill := encode_emptyMsgs_poly (EncodingMachines.unarySub_poly hK hP)
  have hupd : PolyTimeComputable upd := hstate.append (hnorm.append hfill)
  -- The machine state is exactly the public semantic prefix on the genuine orbit.
  have hclosed : ∀ w i, EncodingMachines.loopState upd (fun _ => []) w i =
      Strategy.encodeMsgs (phasePrefix S k B verifierFirst (X w) (Z w) (RV w) (RS w) i) := by
    intro w i
    induction i with
    | zero => rw [EncodingMachines.loopState_zero, phasePrefix_zero, Strategy.encodeMsgs_nil]
    | succ i ih =>
      rw [EncodingMachines.loopState_succ]
      dsimp only [upd]
      simp only [pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]
      rw [ih]
      have hdec : BinArith.decWords (Strategy.encodeMsgs
          (phasePrefix S k B verifierFirst (X w) (Z w) (RV w) (RS w) i)) =
          phasePrefix S k B verifierFirst (X w) (Z w) (RV w) (RS w) i :=
        (congrArg BinArith.decWords (encodeMsgs_eq_encWords _)).trans
          (BinArith.decWords_encWords _)
      rw [hdec, phasePrefix_succ, CommitmentLemmas.encodeMsgs_append,
        CommitmentLemmas.encodeMsgs_append]
  -- The phase-independent normalized-message bound supplies the loop's polynomial envelope.
  obtain ⟨C, c, hC⟩ := hX.output_length_le
  let XP : PolyExpr := .normal C c
  let bound : PolyExpr := .mul (.mul (Q.subst XP) (k.subst XP))
    (.add (.mul (.const 2) (B.subst XP)) (.const 2))
  have hN := EncodingMachines.unaryPolyOf_poly Q (EncodingMachines.unaryLength_poly hX)
  have hloop := ColMachines.polyTimeComputable_loopState' hupd (polyTimeComputable_const [])
    hN bound (fun w i hi => by
      rw [hclosed]
      have hx : (X w).length ≤ XP.eval w.length := by
        simpa only [XP, PolyExpr.eval_normal] using hC w
      have hq := Q.eval_mono hx
      have hk := k.eval_mono hx
      have hb := B.eval_mono hx
      simp only [bound, PolyExpr.eval_mul, PolyExpr.eval_add, PolyExpr.eval_const,
        PolyExpr.eval_subst]
      calc
        _ ≤ i * k.eval (X w).length * (2 * B.eval (X w).length + 2) :=
          length_encodeMsgs_phasePrefix_le S k B verifierFirst (X w) (Z w) (RV w) (RS w) i
        _ ≤ Q.eval (X w).length * k.eval (X w).length *
            (2 * B.eval (X w).length + 2) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hi)
        _ ≤ Q.eval (XP.eval w.length) * k.eval (XP.eval w.length) *
            (2 * B.eval (XP.eval w.length) + 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul hq hk) (by omega))
  exact hloop.congr fun w => hclosed w _

/-- For uniform phase simulator `S`, polynomials `k,B,Q,CV`, and orientation `verifierFirst`,
there is a uniform simulator `SQ` with coin polynomial `CV + Q*S.coins`. On `(x,z)` it samples
one verifier tape from the first `CV(|x|)` coins, uses the remaining coins for the `Q(|x|)`
phase calls, and outputs the canonical view with their normalized prefix.
[PS10, Theorem 175.1; Gol01, §4.3.4, strict-PPT sequential simulation].
`∃ SQ : NUPPT, SQ.Uniform ∧ SQ.coins = .add CV (.mul Q S.coins) ∧ ∀ x z (r : SQ.Coins x.length),
SQ.simulate x z r = let rV := (List.ofFn r).take (CV.eval x.length); let rS := (List.ofFn r).drop
(CV.eval x.length); View.encode ⟨x, z, rV, phasePrefix S k B verifierFirst x z rV rS (Q.eval
x.length)⟩`.

**Proof sketch.** Apply `phasePrefix_poly` to the common-input and auxiliary-input projections
of the simulator layout, the first verifier-tape coin slice and the remaining phase tape.
Pair these fields with the encoded prefix to produce the canonical view. The published
`NUPPT.ofPolyTimeUniform` construction uses exactly the stated coin polynomial. Its activation
and simulator readers, followed by the layout projection equations, give the exact formula.
This includes empty prefixes when the phase count or round count is zero. -/
theorem exists_phaseSimulator (S : NUPPT) (hS : S.Uniform) (k B Q CV : PolyExpr)
    (verifierFirst : Bool) :
    ∃ SQ : NUPPT, SQ.Uniform ∧ SQ.coins = .add CV (.mul Q S.coins) ∧
      ∀ x z (r : SQ.Coins x.length), SQ.simulate x z r =
        let rV := (List.ofFn r).take (CV.eval x.length)
        let rS := (List.ofFn r).drop (CV.eval x.length)
        View.encode ⟨x, z, rV, phasePrefix S k B verifierFirst x z rV rS (Q.eval x.length)⟩ := by
  -- Decode both inputs and split the verifier and phase tapes through public PT readers.
  let X : List Bool → List Bool := fun w => pairFstD (NUPPT.inArg w)
  let Z : List Bool → List Bool := fun w => pairSndD (NUPPT.inArg w)
  let RV : List Bool → List Bool := fun w => (NUPPT.inCoins w).take (CV.eval (X w).length)
  let RS : List Bool → List Bool := fun w => (NUPPT.inCoins w).drop (CV.eval (X w).length)
  have hX : PolyTimeComputable X :=
    polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg
  have hZ : PolyTimeComputable Z :=
    polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg
  have hcut := hX.pairEncode NUPPT.polyTimeComputable_inCoins
  have hRV : PolyTimeComputable RV := by
    refine ((polyTimeComputable_pairTakePoly CV).comp hcut).congr fun w => ?_
    rw [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hRS : PolyTimeComputable RS := by
    refine ((polyTimeComputable_pairDropPoly CV).comp hcut).congr fun w => ?_
    rw [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  -- Assemble the normalized repeated prefix and encode the complete canonical view.
  have hpre := phasePrefix_poly S hS k B Q verifierFirst hX hZ hRV hRS
  let F : List Bool → List Bool := fun w =>
    View.encode ⟨X w, Z w, RV w,
      phasePrefix S k B verifierFirst (X w) (Z w) (RV w) (RS w) (Q.eval (X w).length)⟩
  have hF : PolyTimeComputable F := by
    refine ((hX.pairEncode hZ).pairEncode (hRV.pairEncode hpre)).congr fun w => ?_
    dsimp only [F]
    rw [View.encode_mk]
  -- The uniform constructor and activation/layout readers identify every output field.
  refine ⟨NUPPT.ofPolyTimeUniform hF (.add CV (.mul Q S.coins)),
    NUPPT.ofPolyTimeUniform_uniform hF _, NUPPT.coins_ofPolyTimeUniform hF _, ?_⟩
  intro x z r
  rw [NUPPT.simulate_eq, NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform,
    NUPPT.advInput_eq, ← NUPPT.layout_eq]
  dsimp only [F, X, Z, RV, RS]
  rw [NUPPT.inArg_layout, NUPPT.inCoins_layout, pairFstD_pairEncode, pairSndD_pairEncode]

end TCSlib.Cryptography.SequentialZK
