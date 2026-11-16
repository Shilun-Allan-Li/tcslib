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
