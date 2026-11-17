# Gate 50 · the GSW 6a fills gate: #366 (with LE-g50) and #368 · round 1

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews). This is **Gate 50**,
the fills gate of GSW phase 6a: the proofs of the 98 6a targets that Gate 45 froze as statements. Seyoon's ruling of
2026-11-17 (decision-log line 578, "#368 gating (Seyoon): fold into Gate 50") audits the 6b owner prerequisites #368 here as
well. Two open draft PRs are audited:

- **PR #366** ([link](https://github.com/Shilun-Allan-Li/tcslib/pull/366)), branch `land/gsw-6a-fills`, head
  **`597fb736e545706a058cc212243a13f6dadfeceb`** (tree `df05652d512a702fa8e379fe3f16258f0e1d20d5`), base
  `cryptography/pass-shelat-ch2-4`. Its merge base with the records tip and its REST `base.sha` are both
  `555f0fe1b10a20d1be72386a97c6fe7a2f39c204`. It has 22 SSH-signed first-parent commits since the branch point
  `036d823933c8248bd8894c7963e15dd0f1837075` (`checks/series.txt`). It changes 24 files (+6435/−214) against its merge
  base.
- **PR #368** ([link](https://github.com/Shilun-Allan-Li/tcslib/pull/368)), branch `land/gsw-6b-owner-prereqs`, head
  **`1953898b18a33ab2cd533820c5754a1aacffeb44`** (tree `89952a4a153c1183e0345f88a10568a936762a7d`), one SSH-signed commit on
  `55f553715f280be36827ad86a94c93db39ec56c3` (its REST `base.sha` and merge base). 2 files, +33/−12.
- **Records pin:** the commit that files this directory, `briefs/lattice-gsw/gates/50-gsw-6a-fills/`. `dispatch-r1.md`
  and the prompt name it. Its parent is the records tip at staging, `f19b8056488fb01214d00915064669dda7e65cc2`
  ("Records: LE-g50 on #366 (PASS; TreeNCAC seal failures cleared)"), and the pin adds only this directory, so every
  record this pack cites reads the same at `f19b8056` and at the pin.
- **Lean base.** The tip's Lean equals `2dd2e60ed0cdd4681a7bd12fe4a86825e98db664`, the #365 merge, which is **olean
  snapshot #8** (map `28677767…`), and equals `555f0fe1` (`checks/lean-equality.txt`). #368's base `55f55371` is
  Lean-equal to snapshot #7's T `a1fa7b65` (#8 minus #365's `Pairing/Group.lean`).

Lean paths below are under `TCSlib/Complexity/` unless they start with `TCSlib/`. `BP/` is `BranchingPrograms/`, `CC/` is
`CircuitComplexity/` and `FA/` is `CircuitComplexity/FormulaArith/`. Line numbers are at the heads.

## Scope

#366 is a landing branch that **contains** #358 (O1) and #359 (the 6a statements, with LE-g45 and LE-g45b) as signed
`--no-ff` merges. Its first-parent line splits into segments (`source-head-r1.json` `segments`):

| Segment | Commits | In scope here |
|---|---|---|
| merges of #358 `a616adca` and #359 `d154c883` | `49f88fef`, `76efe1ba` | **no** (Gate 45, CLEAR in round 2). Only as the base: the frozen statements |
| merge of #360 `cc05f76c` | `32ec2ef5` | **yes**: 15 owner readers, never gated |
| #360 addendum 2 (LE-gf3 part 1) | `40c7215c` | **yes** |
| in-house fills U1/U2, U3, U8, U6 | `c7fb15ee`, `bec8eefd`, `2ddada22`, `e0d3e537` | **yes** (no external review before this gate) |
| external fills U4 (2 commits), U5, U9, U10, U11, U7 | `e2b7020c`, `2f38e2b9`, `80de2e4e`, `72bfcab0`, `1bf78b47`, `153811f1`, `bf8aef14` | **yes** |
| landing edits LE-gf1, LE-gf3 part 2, LE-gf2, LE-gf4 | `91e2f807`, `c1a444f2`, `22636300`, `ccca6f80` | **yes** |
| merges of the records tip (#347/#355, then #365) | `e4d77a5e`, `93ae671e` | **yes**, as merges: they must add nothing to the 6a change |
| **LE-g50** (this gate's pre-dispatch sweep) | `597fb736` | **yes** |

#368 is audited whole: `decrypt_eq_decode_dotProduct` (new, `GSW/Scheme.lean`, promoted from step 1 of the private
`decrypt_eq_decode_errorSum`, whose proof body changes) and the reader `hybridPlant_eq`
(`Encryption/PublicKey/EnsembleSecurity.lean`).

**Out of scope** (mention only if something in scope depends on them):
- #358/#359 content: the statements, definitions, readers and helpers Gate 45 cleared, and LE-g45/LE-g45b. Their
  statements are the **base** of question 2, not an audit item.
- The 6b statements (delivery `gsw-6b-statements`, Gate 46) and their consumers of #368.
- Cleanup Stage 1 (#347/#355, Gate 47) and #365 (Gate 49), which reach #366 only through the tip merges.
- The merge conditions: snapshot adoption and merge order (#366 then #368, or either order). See *Merge interaction*.

## What changed

| Segment | Files | What | Size |
|---|---|---|---:|
| #360 | `CC/Basic`, `CC/Adder`, `CC/DAGCircuit`, `CC/DAGTransform`, `CC/TreeNCAC`, `CC/TreeDAG` | 15 public readers, pure insertions: `Lit.eval_eq`; `TreeCircuit.depth_lit`/`size_lit`/`maxFanin_lit` (by `simp [TreeCircuit.depth]` etc., not `rfl`: the definitions are well-founded, deviation D1); `carryBit_zero`/`_succ`; `gatesAcyclic_iff`; `DAGCircuit.isWellFormed_iff`; `gadgetCorrect_iff`; `TreeCircuitFamily.isPolySize_iff`/`hasFaninTwo_iff`/`hasPolylogDepth_iff`; `Language.inTreeNC_iff`; addendum `vertexValue_eq`/`vertexDepth_eq` (ruling "N2 reader ruling") | +79/−0 |
| addendum 2 | `CC/Basic`, `CC/Adder` | `TreeCircuit.maxDepth_le_of_forall`, `maxFaninL_le_of_forall`, `prefixVal_eq_of_false`, `prefixVal_testBit`: public, the worker's bodies verbatim (ruling GF-W1 A) | +36 |
| U1/U2 | `BP/Defs`, `BP/Eval` | C1–C8, 16 declarations; 1 private helper (`stepWith_single`); import `Mathlib.Algebra.BigOperators.Group.Finset.Piecewise` | +132/−16 |
| U3 | `BP/Barrington` | C9–C16, 11 declarations; 16 private helpers | +438/−11 |
| U8 | `FA/Combinators` | F1–F3, 23 declarations (`const_eval` was proved by LE-g45; the 3-way merge kept LE-g45's body); 0 private helpers | +155/−23 |
| U6 | `CC/NANDForm` | N1–N6, 6 declarations; 4 private helpers; import `Mathlib.Algebra.Order.BigOperators.Group.List` | +242/−6 |
| U4, U5, U9, U10, U11, U7 | `BP/BarringtonConverse`, `BP/NC1`, `FA/CarrySave`, `FA/Compare`, `FA/ModSum`, `CC/NANDLayering` | 41 targets (C17–C25, F5–F10, N7–N13); 52 private helpers at delivery; four Mathlib imports | +2043/−170 |
| LE-gf1 | `BP/NC1` | C23/C24 use `Nat.pow_log_le_add_one` (GF-F01) | +5/−8 |
| LE-gf3 part 2 | `BarringtonConverse`, `CarrySave`, `Compare`, `ModSum` | 14 private copies deleted; CarrySave's `depth_getD_le`/`maxFanin_getD_le` made public (GF-F02) | +36/−168 |
| LE-gf2 | `CC/NANDLayering` | one sentence of the **frozen** `layerNAND` docstring (GF-F04; Seyoon's freeze exception GF-W2 A) | +3/−2 |
| LE-gf4 | `FA/ModSum` | F9 uses `Finset.sum_le_card_nsmul` (GF-F03) | +6/−6 |
| LE-g50 | `FA/Combinators`, `CC/TreeNCAC`, `BP/Barrington` | U1: `depth_subst_le`/`maxFanin_subst_le` use the public `_le_of_forall` lemmas; U2: TreeNCAC's private `maxDepth_map_le`/`maxFaninL_map_le` deleted, `toBinary_maxFanin_le`/`toBinary_depth_le` re-pointed; U3: private `IsFiveCycle.pow_apply_eq_iff` proved from Mathlib's `Equiv.Perm.IsCycleOn.pow_apply_eq_pow_apply` | +24/−51 |
| #368 | `TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Scheme.lean`, `TCSlib/Cryptography/Encryption/PublicKey/EnsembleSecurity.lean` | `decrypt_eq_decode_dotProduct` (public, with tags and a sketch); `decrypt_eq_decode_errorSum`'s step 1 replaced by it (proof body only); `hybridPlant_eq` (`rfl`) | +33/−12 |

- The 98 targets: U1/U2 16 + U3 11 + U8 23 + U6 6 + external 41 = 97 admitted at #359, plus `const_eval` (proved by
  LE-g45 at #359). Every 6a module has 0 `sorry`.
- **The external units** are the worker's 7 commits (exchange `60703442`, head `bb7efa82`, base `05999162` = #359 × #360
  at `3ea428fd`), cherry-picked with `-S` (range-diff 7/7 `=`; the 7 patches reproduce `bb7efa82` hash for hash on
  `mkbase.sh`'s base). Author and messages are the worker's.
- **The in-house units** are content commits: U1/U2 and U6 are the blobs of `fill/gsw-6a-u1-u2` `f31382a5` and
  `fill/gsw-6a-u8-u6` `b65668a9`; U3 and U8 are three-way merges of the in-house diffs onto #359's files (`mergefile/` in
  the phase-2 ZIP). U8's one conflict was `const_eval`'s body; LE-g45's was kept.
- **The tip merges add nothing to the 6a change:** `git diff 036d8239 ccca6f80` is byte-equal to
  `git diff 555f0fe1 93ae671e` (SHA-256 `364f447e…`; `checks/lean-equality.txt`), and LE-g50 is exactly
  `git diff 93ae671e 597fb736` (SHA-256 `475e16b7…`, byte-equal to the evidence copy,
  `checks/leg50-diff-vs-evidence.txt`).
- **Freeze, independent check at staging** (`checks/frozen.txt`, `tools/frozen.py`, git blobs only; two controls each
  give exactly CHANGED 1 / DOC 1): from #359's head `d154c883` to `597fb736` over the 17 6a and #360 Lean files,
  **0 declaration headers CHANGED**, 78 ADDED (21 public: #360's 15 and LE-gf3's 6; 57 private helpers), 2 REMOVED (the
  TreeNCAC private pair, LE-g50). Public docstrings that changed: 37, of which **36 only inside their
  `**Proof sketch.**` paragraph** (permitted) and **1 outside it: `layerNAND` (LE-gf2)**. In the five in-house files the
  only removed lines are `  sorry`, except LE-g50's three sketch lines in Combinators. For #368: 2 ADDED, 0 CHANGED, 0
  docstring changes.

## Rulings and records in force

1. **Phase-6 rulings** (`records/phase6/rulings.md`): P6-Q1 (Gate 45 = 6a statements; the 6a fills follow),
   P6-Q3/Q4/Q9/Q14/Q16/Q18 (the models), the location ruling, and plan section r3 (`records/phase6/plan-section.md`;
   §H5 the targets, §H7 the units).
2. **Gate 45** (closed CLEAR in round 2; `records/gate45/`): the 98 statements at `d154c883` are frozen; G45-01 moved
   `eval_node_nil` into `Combinators` (decls2's one REMOVED entry) and made `const_eval` a proved citation.
3. **Q3 reader ruling** and the **N2 reader ruling** (decision log, `LatticeCryptographyPlan.md` lines 545 and 555; extract in `records/extracts/`): #360's readers, pure insertions, landed
   before the fills.
4. **Overnight ruling** (line 547): in-house fills of the small units, drafts only, by the maintainer.
5. **gsw-6a-fills rulings GF-W1..W5** (line 566, all as recommended): LE-gf3 repays GF-F02 (no ledger row), LE-gf1 and
   LE-gf4 (GF-F01, GF-F03), **LE-gf2 is a one-sentence freeze exception** to the frozen `layerNAND` docstring, and
   `NANDLayering` is accepted at 947 lines (split only above 1,000).
6. **Gate 50 pre-dispatch sweep ruling** (line 580): fix now in #366 by LE-g50 (below, question 6).
7. **Q-C1** (6b checkpoint-1 review `records/phase6/checkpoint1-6b-review.md`, G6B-C1-F03): the residual step behind the
   6b target G6 becomes an owner-side public lemma in `Scheme.lean`, with `hybridPlant`'s reader (#368).
8. **Duplication:** G44-01, G48-01 and G45-01: disclosure is not acceptance; an inline re-derivation of a Mathlib lemma is
   a re-proof (major). Ledger extract `records/extracts/duplication-ledger-header-DL54.md` (DL-54: `reidx` move,
   scheduled after the 6a landing).
9. **Rule 10 rulings:** canonical coe-A seals; a file may read its own definitions; projection `CoeFun` is notation.
   G6A-F05 (TreeNCAC's two pre-existing seal failures) is **cleared by LE-g50**.
10. **Signatures:** the account's Claude sessions share one SSH signing key (BS-F08). A signature attests a session on the
    account, not the maintainer.
11. **Policy** (`records/policy.md`): modularity, attribution (tags or "Glue."), proof sketches for proofs of 20+ lines
    (any proof of more than about 20 lines of tactics; files target 150–600 lines, and a file nearing 1,000 is split).

## Questions for the audit

**1. Correctness of the proofs (all 98 targets, and every helper)**
- Does every proof establish its Gate-45-frozen statement? The axiom probe (phase 2; LE-g50 re-run) reports all 98
  targets on `propext`/`Classical.choice`/`Quot.sound` only, 0 `sorryAx`, 0 TRACE lines over the 853-constant census.
  Spot-check the hard units for hidden weakenings (a target proved for a special case through an instance argument, a
  `decide`/kernel case check that does not cover the statement):
  - U3: C10's explicit conjugator (`conjugator_conj`, by orbit matching and `IsFiveCycle.pow_apply_eq_iff`), C13's
    commutator and De Morgan steps, C14's `4 ^ depth` bound, `isFiveCycle_commutator` by `decide +kernel`.
  - U4 (Thm 2, C17–C21) and U5 (NC¹ corollaries C22–C25).
  - U7 (N7–N13: the layering; `NANDLayering`'s structural and semantic column invariants).
  - U9–U11 (carry-save, comparison, modular interval sum: F5–F10).
  - U6 (N1–N6: the NAND gadget through `DAGCircuit.rewrite`).
- Are the 57 private helpers true as stated and used as their docstrings say?
- #368: is `decrypt_eq_decode_dotProduct` true for every `P`, `s`, `C` (the `Fin.snoc` split at the last coordinate,
  `secretVector_eq`), and does `decrypt_eq_decode_errorSum` still prove its unchanged statement? Is `hybridPlant_eq` the
  definition's body verbatim?

**2. Frozen-statement fidelity**
- Is every target's header identical to `d154c883`'s (decls2 against the tip: **289 ADDED, 1 REMOVED, 0 CHANGED**; the
  staging's `checks/frozen.txt`: 0 headers changed)? Did a fill weaken, re-bind or re-type a statement through a changed
  definition, instance or `set_option`?
- Docstrings: the 36 sketch-only changes are permitted (fills may update their own sketches). Are the updated sketches
  accurate descriptions of the delivered proofs?
- **LE-gf2** is the one change outside a sketch: one sentence of the frozen `layerNAND` docstring, under Seyoon's freeze
  exception (GF-W2 A). Is the new sentence true at the head ("N12 and N13 are proved structurally, so no admission
  reaches it through them"), and is the edit limited to that sentence?
- Module docstrings: the worker's permitted admission sentences (U4, U5, U7) and the G6A-F07 [Bar89] line; the in-house
  module texts are unchanged and now stale (known slips). Is anything else changed?
- #368: no existing statement or docstring changes; is the `decrypt_eq_decode_errorSum` change confined to its proof body?

**3. Readers, promotions and API**
- **#360's 15 readers:** each the definition's body verbatim (or its equation lemma, D1)? Right binders, not `@[simp]`?
  Was a reader missing that a fill then worked around (U6's former private bridge was replaced by `vertexDepth_eq`)?
- **The six public lemmas of LE-gf3** (`TreeCircuit.maxDepth_le_of_forall`, `maxFaninL_le_of_forall` in `Basic`;
  `prefixVal_eq_of_false`, `prefixVal_testBit` in `Adder`; `FormulaArith.depth_getD_le`, `maxFanin_getD_le` in
  `CarrySave`): correct homes and namespaces, formula docstrings, "Glue." notes, binder style?
- **#368:** `decrypt_eq_decode_dotProduct` is placed after `decrypt_eq` and cites [GSW13, §3.1, `Dec`; BV14, §3.1,
  `NCCrypt.Dec`]. Is it a result (tag) or glue? `hybridPlant_eq` follows the file's reader style (`pkEncDist_eq`), with
  no formula line and no "Glue." (known slip): grade it.

**4. The landing edits**
- LE-gf1 (`Nat.pow_log_le_add_one 2 n` in C23 and C24), LE-gf3 (the promotions verbatim, 14 deletions, qualified uses),
  LE-gf4 (`Finset.sum_le_card_nsmul`), LE-g50 (below): correct, complete and proof-only? Do the sketches name the reused
  lemmas?
- LE-g50's proofs: U1's `refine TreeCircuit.maxDepth_le_of_forall (List.forall_mem_map.mpr …)` with
  `depth_le_maxDepth`; U2's re-pointed `toBinary_*`; U3's
  `IsCycle.isCycleOn`, its support set rewritten to `univ` (by `IsFiveCycle.apply_ne`), then
  `IsCycleOn.pow_apply_eq_pow_apply (Finset.mem_univ 0)` and `Finset.card_fin`.

**5. Docstrings, sources, sketches**
- Every helper has a formula docstring and "Glue." (phase 1: all 52 worker helpers; the in-house helpers were not
  externally reviewed). Every declaration block of 20+ lines has a `**Proof sketch.**`.
- Citations added by the fills: G6A-F07's [Bar89] line; #368's [GSW13]/[BV14] locators against `references/` in
  `sources-r1.zip`.
- Sizes: `NANDLayering` 948 lines (GF-W3), `Barrington` 895; all under 1,000.

**6. Duplication** (recent gates graded undisclosed re-proofs of public lemmas, and disclosed ones without a recorded
acceptance, as **majors**: G44-01, G48-01, G45-01, GF-F01, BS-F02)
- **Phase 1** (worker units) found GF-F01 (major, `Nat.pow_log_le_add_one`), GF-F02 (16 private copies), GF-F03 (near,
  `Finset.sum_le_card_nsmul`), all repaid by LE-gf1/3/4 under the rulings. Its table (`records/phase6/fills-final-r1/
  review.md` § *Duplication review*) lists every helper with its nearest relative.
- **Phase 2** swept the 6 public lemmas and the 75 private helpers by name and normalized body.
- **The pre-dispatch sweep of this gate** (names and statement shapes against TCSlib at the tip and Mathlib `029db123`;
  every inline `have` of a general fact in the in-house units read by hand; `checks/dup-sweep.txt`) stopped staging on
  three **unledgered** items, all in the maintainer's own code:
  - **U1:** in-house U8's `depth_subst_le`/`maxFanin_subst_le` had inline list inductions that #366's own public
    `maxDepth_le_of_forall`/`maxFaninL_le_of_forall` give.
  - **U2:** TreeNCAC's pre-existing private `maxDepth_map_le`/`maxFaninL_map_le` became the `cs.map f` case of those
    lemmas.
  - **U3 (borderline):** in-house U3's private `IsFiveCycle.pow_apply_eq_iff` re-derived the `s = univ` case of Mathlib's
    `Equiv.Perm.IsCycleOn.pow_apply_eq_pow_apply` by another route, and its docstring did not say so.
  - **Process note:** the phase-1 review had noted U1/U2 ("that goes on the dedup queue, not this landing") but no ledger
    row, queue entry or ruling was ever filed: the BS-F02 pattern. The pre-dispatch sweep found them. Seyoon ruled **fix
    now** (decision-log line 580); LE-g50 is the fix (line 582).
- **After LE-g50**, the staging re-swept the LE-g50 delta: it adds no declaration, removes two privates, and uses only
  public TCSlib lemmas and Mathlib (`List.forall_mem_map`, `IsCycle.isCycleOn`, `IsCycleOn.pow_apply_eq_pow_apply`,
  `Finset.card_fin`). Nothing new.
- **Left as notes, not duplicates:** U8's `depth_neg`/`maxFanin_neg` keep inline inductions in **equality** form
  (`maxDepth (cs.map neg) = maxDepth cs`), which no public lemma states; TreeDAG's pre-existing private
  `maxDepth_map`/`maxFaninL_map` (`TreeDAG.lean:417/430`, `foldr max` form); `prefixVal_testBit` is near Batteries'
  `Nat.ofBits_testBit` (different fold, no bridge; disclosed in its docstring; GF-W1); the in-house helpers
  `isFiveCycle_inv`/`_conj`, `IsFiveCycle.isCycle`/`.orderOf_eq`/`.apply_ne` are one- or two-step glue over Mathlib's
  `cycleType` lemmas; C6's inline `key` (a sum over a filter by a bijection) and C7's step-indexed fold induction have
  no single Mathlib/core lemma (C7's is disclosed in the in-house REPORT).
- **#368:** `decrypt_eq_decode_dotProduct` needs GSW's `secretVector`/`decryptColumn`; the step occurred only inside the
  private lemma it now serves. `hybridPlant_eq` has no counterpart (`distAdv_tuple_le_sum` inlines the lambda).

Is any declaration, or any inline step, of #366's in-scope parts or of #368 an undisclosed or unaccepted re-proof of a
public TCSlib or Mathlib lemma? Is LE-g50 a complete repair of U1–U3?

**7. Rule 10** (inner evidence ZIPs). Did any proof read a foreign definition other than through a published reader?
- Phase 1, statically: 300 distinct `simp`/`rw`/`unfold` names in the six worker files, **0 foreign definitions**; the
  `show`/`change` steps reduce only core `Nat.repeat`.
- Phase 2 (#6) and the #7 re-replay: canonical coe-A on **22 owners**, 0 errors in every 6a owner, only the pre-existing
  failures (Adder 3, DAGTransform 11, TreeNCAC 2, Hierarchy 2, TreeDAG 25; same declarations as their recorded runs);
  root coe-A 14,098 requests, 0 errors; paired controls for the 6 public lemmas ALL_OK (attempt 2); explicit-unfold
  scan 0 new foreign unfolds.
- LE-g50 (#8): 22 owners compared with the #7 records: 14 identical but `rev`; Barrington and Combinators same request
  sets and byte-equal logs; **TreeNCAC 2 → 0 errors**; five owners lose exactly the two deleted matchers; root coe-A
  **14,105 requests, 0 errors**. Paired controls and the unfold scan were not re-run (no new declaration, no new read).
- #368: coe-A at base and head, Scheme 101/0 and EnsembleSecurity 1268/6 (pre-existing: `bitwiseEncFun_poly`,
  `bitwise_enc_runAtL`, `singleBitSecure_iff`, `Secure.multiMessageSecure`), byte-equal on #8.
- Is that sufficient? The in-house units' reads were checked only by these seals.

**8. The evidence binding** (§ *Evidence binding*). Does each piece of evidence bind to the commit it is claimed for?
Does the replayed Lean equal the merge that will land? Is anything necessary missing? A missing necessary piece of
evidence is a **major**.

**9. Is anything undisclosed?** Among the commits, the two PR descriptions, the reviews, the in-house REPORT and the
records, is any change, claim or omission undisclosed? The known slips are below. Grade the review findings **GF-F01 to
GF-F09** and the sweep items **U1–U3** in a separate table (agree, or regrade with the reason).

## Evidence binding

| Evidence | Bound to | What it shows | Reaches the head / merge by |
|---|---|---|---|
| #360 review `readers-q3/review.md`, ZIP `1c828ee0…`; addendum `addendum-vertex-readers.md` | #360 `3ea428fd` (13 readers) on tip `8c5875fa`, snapshot #5; addendum `cc05f76c` | pure insertion (5/5 files), owners' closure rebuilt 6/6 rc 0, axioms, coe-A base = head, clash scan, lint; addendum: TreeDAG/DAGTransform rc 0, seals equal | #360's merge into #366 equals `git diff 8c5875fa cc05f76c` (hunk offsets aside); its full downstream is in #366's phase-2 replay (564 modules). The addendum's own evidence directory is not in the records (`POINTERS.md`) |
| Phase 1 `fills-final-r1/review.md`, ZIP `aaf8be4f…` | worker head `bb7efa82` on base `05999162`, exchange `60703442` | static: reproduction 7/7, integrity, scope, decls2 0/0/0, frozen check with controls, admissions, Rule 10 names, lint, the worker evidence recount (seals, liveness, axioms), the duplication table | the 7 cherry-picks: range-diff 7/7 `=`; after `bf8aef14` the six worker files are blob-equal to `bb7efa82` |
| `landing-edits-proposed.diff` (`01c07a11…`) | `bb7efa82` | LE-gf1..4 as proposed | applied verbatim; the 8 edited files at `ccca6f80` equal `bb7efa82` + the diff (`log/le-apply-equal.txt`, phase-2 ZIP) |
| Phase 2 `phase2.md`, ZIP `68d89dff…` | `ccca6f80` on tip `036d8239` (Lean = snapshot #6) | 564 modules rc 0, state 1445 OK, admissions 192 (0 in 6a), axioms (98 targets, 859 constants), decls2 289/1/0, coe-A 22 owners, root coe-A, controls ALL_OK, unfold scan, lint, dup sweep; reproduction of the worker patches; the U3/U8 three-way merges | superseded for adoption (tree deleted); its outputs are compared byte for byte by the #7 run |
| #7 re-replay (`phase2.md` § "Re-replay on snapshot #7"), ZIP `1799ff74…` | `e4d77a5e` (Lean = #7 + 6a) and `93ae671e` (+ #365), tree `c8ba8961` | 564 + 22 modules rc 0, state 1447 OK, #7 0/0/0; 256/256 same-key oleans byte-equal to #6; axiom log byte-equal; coe-A 22/22 identical but `rev`; decls2 byte-equal; lint | `93ae671e` is LE-g50's parent; its Lean is snapshot #8's plus the 6a change (`checks/lean-equality.txt`) |
| LE-g50 (`phase2.md` § LE-g50), ZIP `51151f44…` | **`597fb736`**, tree `df05652d`, replay `olean-replay-6a-land8` (`cp -al` of `-land7`) | 16 modules rc 0, 0 warnings, state 1447 OK, #8 and parent 0/0/0, map `963ddeb4…` (only the 3 edited modules differ from the parent); 0 `sorry` in 6a, admissions 192; axioms (853 constants); coe-A 22 owners vs #7; root coe-A 14,105/0; decls2 289/1/0; touched 5 CHANGED + 2 REMOVED; lint | the head. `merge-tree(tip, 597fb736)` is clean and Lean-equal to `df05652d` (`checks/mergetrees.txt`): the adoption condition |
| #368 replay on #7, `owner-prereqs-6b/evidence.zip` `77620ab8…` (no report file; the PR body is the report) | `1953898b` on `55f55371` (Lean = #7) | 67 modules rc 0, state 1434 OK, #7 0/0/0, admissions 192, axioms (7 constants), decls2 2/0/0, touched, coe-A base vs head, lint | superseded for adoption by the #8 run |
| #368 re-replay on #8, `evidence-s8.zip` `e97aed58…` | R = `merge-tree(tip, 1953898b)` = tree `ab098201` (Lean = #8 + the two files) | 67 modules rc 0, state 1434 OK, #8 0/0/0; all 67 oleans and logs byte-equal to the #7 run; admissions 192; axiom log byte-equal; coe-A byte-equal; map `5a88ccf5…` | `merge-tree(f19b8056, 1953898b)` at staging is Lean-equal to `ab098201`, and its Lean diff from #8's T equals the PR's own (`checks/lean-equality.txt`) |
| Snapshot #7 and #8 adoption records (`snapshots/`) | T `a1fa7b65` (#7), `2dd2e60e` (#8) | maps, manifests, basecheck, swap rehash 0/0/0 | the tip's Lean equals #8's T |
| In-house drafts (no separate evidence in the records) | `f31382a5`, `b65668a9` | their builds were draft checks only (decision-log lines 552, 554, 559) | their content is in #366 and is covered by phase 2, the #7 run and LE-g50 |

## Known dispositions and slips (not findings)

- **Review findings** (`fills-final-r1/review.md`): GF-F01 (major, LE-gf1), GF-F02 (major unless accepted, LE-gf3),
  GF-F03 (minor, LE-gf4), GF-F04 (minor, LE-gf2), GF-F05 (info, size, GF-W3), GF-F06 (U8 rebase), GF-F07 (REPORT
  recount exceptions), GF-F08 (NC1 sentence names the job), GF-F09 (process: Mathlib search for inline `have`s). **Grade
  them**, with the sweep items U1–U3.
- **The phase-1 dedup-queue sentence** (U1/U2) was never filed; see question 6. The phase-2 duplication sweep (name and
  normalized body only) did not catch U1–U3.
- **Stale in-house frozen docstrings**, left for a docstring follow-up like LE-g45b (#366 body, *Disclosed*):
  `BP/Defs.lean:32`, `BP/Eval.lean:35`, `BP/Barrington.lean:32` ("targets admitted with `sorry`"); `CC/NANDForm.lean:61`
  and `:455` ("While N2 is admitted, `sorryAx` reaches `toNANDForm`"). No ruling covers them yet.
- **Sizes:** `NANDLayering` 948 (GF-W3 accepted 947; LE-gf2 rewraps one line).
- **LE-gf3's size:** the review said +68/−154; the applied diff is +72/−168.
- **The in-house units had no external review** before this gate; the overnight ruling made them maintainer drafts.
- **#366's body** still carries its #6-era line "Duplication sweep (on #6): … No duplicate was found", above the LE-g50
  section that supersedes it.
- **#368's body** says "Gated with the 6b fills or the next small-items gate" (superseded by the Gate 50 ruling) and
  reports the #7 replay; the #8 re-replay is in the records only. Its sketch-level slips:
  `decrypt_eq_decode_errorSum`'s sketch and `decrypt_of_encrypts`'s sketch still describe the residual step inline
  instead of naming `decrypt_eq_decode_dotProduct` (docstrings left unchanged by design); `hybridPlant_eq` has no
  formula line or "Glue." (file style).
- **Evidence nits:**
  - `evidence-s8.zip`'s inner `SHA256SUMS` lists itself with the empty-file hash (`e3b0c442…`), so that one entry fails;
    the other 184 entries verify.
  - LE-g50's ZIP has `trial-compile/` (three single-file compiles before the commit, timing output only), which
    `phase2.md` § LE-g50 does not describe.
  - Phase 2's paired controls attempt 1 had a control-statement defect (kept); its unfold scan's first run lacked
    `lean-toolchain` (kept).
  - #368's #7 evidence has an `axioms-attempt1-probe-namespace/` run (kept).
- **Not re-run:** on #7, the paired controls, the unfold scan, root coe-A and the dup sweep (inputs unchanged); on LE-g50,
  the paired controls and the unfold scan.
- **Signatures and trailers:** all 22 first-parent commits of #366 and #368's commit are SSH-signed (BS-F08). The 7
  worker cherry-picks keep the worker's messages and session trailers; the worker's original commits are unsigned. No
  signature was cryptographically verified on the host (no allowed-signers file).
- **Authorship:** the external units are an external Claude worker's; the in-house units, #360, the addendum, the landing
  edits, LE-g50 and #368 are the maintainer's.
- **No Lean, no `lake`** was run for this staging. `checks/` are git-object reads; the rest is the recorded evidence.

## Merge interaction (maintainer merge conditions, not audit items)

`checks/mergetrees.txt`:
- #366 × the tip `f19b8056`: clean, Lean-equal to `df05652d`. **Adoption:** `olean-replay-6a-land8` at a #366 merge whose
  Lean equals `df05652d`.
- #368 × the tip: clean (tree `84a021f7…`), Lean-equal to the #8 replay's `ab098201`. **Adoption:** its #8 replay at a
  #368 merge whose Lean equals `ab098201`.
- #366 × #368: clean; the two PRs share no path. Whichever merges second re-replays (the replays are not stacked).
- Order: #366 then #368, or either order.

## Evidence files

- **`pack-r1.md`** (this file) and **`dispatch-r1.md`** (the Codex prompt; records only).
- **`pr366.diff.txt`**: `git diff 555f0fe1 597fb736`, the PR view (includes #358/#359, out of scope).
- **`pr366-360.diff.txt`** (`76efe1ba..32ec2ef5`), **`pr366-fills.diff.txt`** (`32ec2ef5..ccca6f80`: addendum, units,
  LE-gf1..4) and **`pr366-leg50.diff.txt`** (`93ae671e..597fb736`): the in-scope segments.
- **`pr368.diff.txt`**: `git diff 55f55371 1953898b`.
- **`pr366-description.md`**, **`pr368-description.md`**: the PR bodies at staging (REST `.body`, raw).
- **`source-head-r1.json`**: the pins, the segments, every first-parent commit (parents, tree, author, signature kind,
  files), and each file's SHA-256, line count, maximum width, over-width, tab and trailing-space counts at the merge base,
  at `d154c883` and at the head.
- **`sources-r1.zip`**: the files at the head, at the Gate-45 freeze `d154c883`, at the merge base and before LE-g50;
  #368's two files at base and head; the pinned Mathlib and Batteries files with the reused lemmas and nearest
  relatives; the [Bar89], [BV14], [BV11] and [GSW13] transcriptions. `README.md` gives every entry's SHA-256 and origin.
- **`verification-r1.zip`**: `MANIFEST.md` (provenance), `POINTERS.md`, and `SHA256SUMS` (every other entry). It holds:
  - `evidence/`: the seven evidence ZIPs and `landing-edits-proposed.diff`, nested unchanged, with the records' sums;
  - `snapshots/`: the #7 and #8 adoption folders;
  - `checks/` with `tools/`: series, Lean equality, merge-trees, the frozen check with controls, the LE-g50 diff check
    and the duplication sweep;
  - `records/`: the phase-1 and phase-2 records, the in-house REPORT, the #360 review and addendum, the 6b checkpoint-1
    review (Q-C1), the rulings, plan section r3, the issued fills brief, `targets.txt` and environment addendum, Gate
    45's findings and resolutions, `policy.md`, and the decision-log, ledger and snapshot-register extracts;
  - `pr/`: the REST fields.
- **`SHA256SUMS-r1`**: the files of this gate directory other than `dispatch-r1.md`.

## Findings delivery

Return `gate50-gsw-6a-fills-findings.md` as Markdown in this chat. If you have several evidence files, return a ZIP. The
user dispatches and merges.

| # | Severity | PR · file · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

Number the findings **G50-01, G50-02, …**. Grade GF-F01 to GF-F09 and U1–U3 in a separate table. Report the audited
heads, the records pin, the counts by severity, and a verdict **per PR** (#366, #368) and **overall**:
- **CLEAR:** zero blockers and zero majors.
- **HOLD:** otherwise.

**Severities**
- **blocker:** a false or unusable statement, a proof that does not establish its statement, or a scope violation.
- **major:** any of the following:
  - a changed frozen statement or statement prose (other than the ruled LE-gf2 exception and permitted sketch updates);
  - a forbidden read not covered by the rulings;
  - an undisclosed copied private lemma, or an undisclosed (or unaccepted) re-proof of a public one;
  - a fabricated source tag;
  - necessary evidence that cannot be verified or does not bind to the audited commit.
- **minor:** documentation or API defects, including an inaccurate formula docstring, glue note, proof sketch, citation
  or PR description.
- **note:** anything else.
