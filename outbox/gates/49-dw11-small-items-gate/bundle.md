## ===== pack-r1.md (this pack) =====

# Gate 49 · DW-11, the combined small-items gate: #351, #352 and the follow-up #365 · round 1

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews). This is the
combined gate of deferred-work item **DW-11** (Seyoon, 2026-11-17): small changes merged on the maintainer review ("merge
now, audit later") are audited together in one gate instead of separate gates. Stage 2 ruling Q5 (2026-11-17)
dispatches it now. Three PRs are audited:

- **#351** (merged): [PR #351](https://github.com/Shilun-Allan-Li/tcslib/pull/351), the bb1-sim **Games statements**:
  - the new module `Games/Relational.lean`, with the targets `expect_simulate_rel` and `expect_sample_rel` (both
    `sorry` at #351) and `prob_simulate_rel`, which is proved from the first;
  - the public averaging bound `ProbComp.abs_expect_sub_le_expect` in `Games/Probability.lean`;
  - one import and one `## Contents` entry in the `Games` facade.
  - Pins: head `dfacac356ff1225aca4c900d81bbf2cabce7b499` (branch `land/bb1-sim-games`), merge base
    `176cfd4a42ac3300d9b84f9045f7abcd0f52ef13`, merged as `cf7d28f7159b46033e8b8ae170954f9575e5d145` (first parent
    `7b154493384f9b163c2be492cf0b37a7dbfe4e93`). 3 files, +151/−0.
- **#352** (merged): [PR #352](https://github.com/Shilun-Allan-Li/tcslib/pull/352), the bb1-sim **group helpers** in
  `Pairing/Group.lean`: `BilinearGroup.pow_val_add`, `pow_val_neg`, `pow_val_bijective_of_ne_one` (ruling Q10, with the
  landing edit LE-grp1, which dropped a fourth helper).
  - **Correction:** #352 is the group-helper PR, not a reader follow-up of #351. An early description of DW-11's scope
    had it wrong; the decision log records the correction (row "DW-11 (Gate 49) pre-dispatch sweep"). The bb1-sim
    readers landed in #357 (Gate 48).
  - Pins: head `92dea4f8126747ea7e816984349b9dbb789f0065` (branch `land/bb1-sim-group`), merge base `176cfd4a`, merged as
    `463f224414ab7615e54104be353bfcda9dfceda7` (first parent `d99c97f147bd61c3d09a63e7e66b9b2c0c8ee69f`). 1 file,
    +27/−0.
- **#365** (open, draft): [PR #365](https://github.com/Shilun-Allan-Li/tcslib/pull/365), the **follow-up fix** that
  Seyoon ordered at this gate's pre-dispatch sweep (below). It is audited as a **proof/refactor PR**, before merge.
  - It adds the public `TCSlib.Cryptography.Pairing.pow_val_bijective_of_prime_card` (for `g ≠ 1` in a finite group
    of prime order `p`, `a ↦ g^{a.val}` is a bijection `ZMod p → M`).
  - It re-proves `pow_val_bijective` (frozen, Gate 40) and `pow_val_bijective_of_ne_one` (#352) from it.
  - It replaces the `Nat.mod_add_div` chains of `pow_val_add` (#352) and the frozen `pow_val_mul` and `pow_val_mul_GT`
    by Mathlib's `pow_mod_card`.
  - Pins: head `5eaddd171bceccee917929e7f319ff9202994c59` (branch `fix/pairing-group-dedup`), base
    `5aed99076d2bd4e5d6f831aed88739fc3ce475b6` (the REST `base.sha` and the merge base). Two SSH-signed commits,
    `6fc5f494` and `5eaddd17`. 1 file, +28/−19.
- **Records pin:** the commit that files this directory, `briefs/pairings/gates/49-dw11-small-items/`. `dispatch-r1.md`
  and the prompt name it. Its parent is the records tip at staging,
  `b31b77f7f4127d9c6c6c0d6a1390de0dc8d71d43` ("Records: #365 commit 2; report and evidence updated"), and the pin adds
  only this directory, so every record this pack cites reads the same at `b31b77f7` and at the pin.
  - The tip's Lean equals #365's base `5aed9907` (`checks/lean-equality.txt`).
  - `merge-tree b31b77f7 × 5eaddd17` is clean, with tree `319c9aa0…`. That tree differs from the tip in
    `Pairing/Group.lean` only, and it is Lean-equal to the head (`checks/mergetrees.txt`).
- **Post-merge context (#351, #352).** Both are on the records branch, and later work builds on them:
  - #357 (Gate 48, closed) proved both `Relational` targets, leaving their headers and docstrings unchanged.
  - The tip carries olean snapshots #3–#6 and cleanup Stage 1.

  **A HOLD on #351 or #352 means a follow-up fix PR, not a revert.** A HOLD on #365 holds that PR's merge.

Lean paths below are under `TCSlib/Cryptography/` unless they start with `TCSlib/`.

## Out of scope
- **Everything merged on top of #351 and #352:**
  - #357's bodies of `expect_simulate_rel` and `expect_sample_rel` (Gate 48, closed). Their sources at the tip are in
    `sources-r1.zip` (`context-b31b77f7/`) for reference only.
  - Cleanup Stage 1's `Games.lean` lines and `Games/Tapes.lean` (#355, Gate 47).
  - #340 and #346 (Gate 44), and the GSW 6a/6b work.
- Gate 40 (the pairing statements, including the frozen `Group.lean` declarations) is closed. Only #365's proof changes
  to three of them are in scope.
- The Stage 2 repayment of DL-40 (re-pointing the private ETT averaging copy onto #351's lemma), and the merge order
  and snapshot adoption of #365. These are maintainer merge conditions.

## What changed

| PR | File | What | Lines (base → head) |
|---|---|---|---:|
| #351 | `Games/Relational.lean` | new: module docstring (References [BGZ09], [Sho04]); `expect_simulate_rel` (target), `prob_simulate_rel` (proved), `expect_sample_rel` (target) | new, 134 |
| #351 | `Games/Probability.lean` | one `## Main results` bullet; `ProbComp.abs_expect_sub_le_expect` after `abs_expect_sub_le` | 409 → 423 |
| #351 | `Games.lean` | `import …Games.Relational`; one `## Contents` entry | 64 → 67 |
| #352 | `Pairing/Group.lean` | three `## Main results` bullets; `pow_val_add`, `pow_val_neg`, `pow_val_bijective_of_ne_one` after `pow_val_bijective` | 304 → 331 |
| #365 | `Pairing/Group.lean` | two `## Main results` lines; the new lemma before `namespace BilinearGroup`; five proof bodies | 331 → 340 |

Every line is at most 99 characters, with no tab and no trailing space (`source-head-r1.json`).

- **#351** is the two signed maintainer cherry-picks `02000ad4` and `dfacac35` of the worker's `912a343e` and
  `d742bf02`. The range-diff is 2/2 `=` (phase 2 P2-1).
- **#352** is `2cca41bc`, a pick of the worker's `fc9cf2f5`, followed by LE-grp1 `92dea4f8`.
  - LE-grp1 drops `natCast_inj_of_lt`, an iff wrapper of Mathlib's `CharP.natCast_injOn_Iio` (BS-F01, ruled
    2026-11-17), and its bullet.
- **The PR views equal the merges.** `git diff 176cfd4a..dfacac35` equals `git diff cf7d28f7^1 cf7d28f7` byte for byte,
  index lines included. The same holds for #352 against `463f2244`. Both PRs' REST `base.sha` is `4bc5bac4`, whose Lean
  equals `176cfd4a` (`checks/lean-equality.txt`).
- **#365 is proof-only apart from the new lemma**, by `checks/pr365-proof-only.txt`, an independent check written at
  staging:
  - with every declaration body masked, the head equals the base plus two pure insertions: the module-docstring lines
    and the new lemma's block (docstring, header, body);
  - the bodies that change are exactly `pow_val_mul`, `pow_val_mul_GT`, `pow_val_bijective`, `pow_val_add` and
    `pow_val_bijective_of_ne_one`;
  - no declaration is removed;
  - two negative controls fail as required (one header character, one docstring character).

  The job's own `decls2` gives 1 ADDED / 0 CHANGED / 0 REMOVED, and `touched.py` gives 1 ADDED and 5 CHANGED
  (`group-dedup-evidence.zip`, `run-commit2/statements/`).

## Rulings and records in force

1. **bb1-sim design rulings** (`records/…bb1-sim__rulings.md`, 2026-11-16):
   - Q1: a new `Games/Relational.lean`.
   - Q2: the names.
   - Q3: the inline-expectation form of the per-call hypothesis.
   - Q4: the companions `prob_simulate_rel` and `expect_sample_rel`.
   - **Q5: no query budget.**
   - **Q6 (changed): promote the averaging bound into `Games/Probability.lean`** as a public lemma. The private ETT copy
     re-points to it under DL-40.
   - Q8: one bb1-sim gate, **superseded for #351/#352 by DW-11**.
   - Q9: the Games statements as their own small PR.
   - **Q10 (changed): the group helpers go into the frozen `Pairing/Group.lean`** by an approved insertion, and should
     "reuse Mathlib's `orderOf`/`ZMod` API where it applies".
   - **Q11: cite [BGZ09] and [Sho04]** for the relational lemma.
2. **The frozen statements of #351** are design r1 §2.2's headers, issued verbatim in the statement brief
   (`records/…issued-stmt-r1__brief.md`). Permitted changes to them: the bodies (a later fill), and the
   citation/deviation prose that the brief's supersessions allow.
3. **BS-F01 / LE-grp1** (2026-11-17): drop `natCast_inj_of_lt`. The fill uses `CharP.natCast_injOn_Iio`.
4. **"Merge now, audit later"** (Seyoon, 2026-11-17) for #351 and for #352. Then **DW-11** (row "#352 merged"): one
   combined small-items gate, not the bb1-sim gate.
5. **DW-11 pre-dispatch sweep ruling** (Seyoon, 2026-11-17, decision-log row "DW-11 (Gate 49) pre-dispatch sweep"):
   - **The finding:** `pow_val_bijective_of_ne_one` (#352) restated the frozen `pow_val_bijective` on `G` instead of
     `G_T` with a 7-line proof clone. The phase-1 review had recorded this as BS-F02 with the disposition "ledger note",
     but no ledger row or ruling was ever made. In the same code, inline chains re-derived Mathlib's `pow_mod_card` and
     `pow_injOn_Iio_orderOf`.
   - **The ruling: fix now in a follow-up PR** (#365): one generic prime-order bijectivity lemma via Mathlib, both
     bijections re-proved from it, and the Mathlib facts used directly. Proof-only, with statements and frozen headers
     unchanged. Gate 49 audits it with #351 and #352. No ledger row results, because the duplication is removed rather
     than accepted.
6. **DL-40** (duplication ledger, open; `records/duplication-ledger-DL40.md`): the private
   `ETTGame.abs_expect_sub_le_expect` (`Encryption/PrivateKey/EncryptThenTag/Forgery.lean:515`) is the ETT copy of
   #351's public lemma. Stage 2 re-points it (the decision-log row of Q6).
   - Phase 2's resolution probe (BS-F03) shows that the call at `Forgery.lean:545` resolves to the private copy today
     and to the public lemma after the deletion.
7. **G44-01 and G48-01 precedents:** disclosure of a duplicate is not acceptance. An accepted duplicate needs Seyoon's
   recorded acceptance and a ledger row with its repayment. A local re-derivation of a Mathlib lemma is a re-proof
   (G48-01, graded major).
8. **Rule 10 rulings:**
   - `PolyExpr.eval` is notation (seal A canonical; seal B with `SEAL_EVAL=1`, attributed).
   - The `FinDist` coercion is notation (**DW-10 Q3**: strict-only failures it causes are recorded, not counted, not
     fixed).
   - A projection `CoeFun`/`Coe` instance is notation (**coe-A canonical**; the strict variants are run and
     attributed).
   - Inside a file, its own definitions may be read directly.
9. **BS-F08:** the account's Claude sessions share one commit-signing key. A signature attests a Claude session on the
   account, not the maintainer. Provenance rests on the pinned hashes and the maintainer's cherry-picks.

## Questions for the audit

**1. Correctness of the statements and proofs**
- **`expect_simulate_rel`** (#351, target):
  - Is the statement true, and is it the right generalization of `expect_simulate_congr` (the case `R = Eq`) and of
    the law form of `simulate_eq_of_abs` (`R s t ↔ s = f t`)?
  - Is the per-call hypothesis (equal expectations for every pair of test functions that agree at equal answers and
    `R`-related states) satisfiable in the intended uses, and not an assumption in disguise? Is it strong enough to
    compose through `simulate`?
  - Edge cases: an empty `R`; a query-free `c`; state types with no related pair; `G₀`/`G₁` that ignore the states.
  - (Its proof is #357's, Gate 48; the statement's truth is in scope here.)
- **`prob_simulate_rel`** (#351, proved at #351):
  - Does it follow from the target as written (`prob_eq_expect` twice, indicators agreeing at equal outputs)?
  - Is the `classical` use harmless?
- **`expect_sample_rel`** (#351, target):
  - Is the one-sample coupling statement true for every `U`, `V`, `e`, `f₀`, `f₁`, `g₀`, `g₁`?
  - Does it really discharge `expect_simulate_rel`'s per-call hypothesis for a call that draws one uniform sample?
- **`abs_expect_sub_le_expect`** (#351, proved):
  - Is the proof correct?
  - Is the statement the ETT copy's statement (`α` for `β`), with the same binder names `c f g h hb` that the Stage 2
    re-point relies on?
- **#352's helpers** (proved at #352, re-proved by #365):
  - `pow_val_add`: `x ^ (a + b).val = x ^ a.val * x ^ b.val`.
  - `pow_val_neg`: `x ^ (-a).val = (x ^ a.val)⁻¹`.
  - `pow_val_bijective_of_ne_one`: bijectivity of `a ↦ g ^ a.val` for `g ≠ 1`.

  Are they true for every bilinear group (`B.order` prime, `|G| = |G_T| = p`), and correctly stated at `ZMod B.order`
  exponents?
- **#365's lemma** `pow_val_bijective_of_prime_card {M} [Group M] [Fintype M] {p} [Fact p.Prime]
  (hM : Fintype.card M = p) {g} (hg : g ≠ 1) : Function.Bijective fun a : ZMod p => g ^ a.val`:
  - Is it true and correctly proved (`orderOf_eq_prime`, `pow_card_eq_one`, `pow_injOn_Iio_orderOf`,
    `Fintype.bijective_iff_injective_and_card`)?
  - Are the five re-proofs correct, and do the two one-line `exact`s instantiate it with the right card facts
    (`B.card_GT` with `pair_ne_one hx`, and `B.card_G`)?
  - Is the `Type*` generality right, and is the `[Fact p.Prime]` instance found at the two call sites
    (`BilinearGroup.factPrime`)?

**2. Frozen-statement fidelity**
- **#351 against design r1 §2.2** and the issued statement brief:
  - Phase 1 found the three `Relational` headers and two imports byte-identical to design §2.2, and the averaging lemma
    byte-identical to the brief's §1a block. Prose differs only by the brief's supersessions: the citations, the F4
    deviation note plus one permitted sentence, the References lines, and `prob_simulate_rel`'s sketch and [Sho04] tag
    (`review.md` § *Statements*; phase-1 ZIP `statements/`).
  - Do the merged headers equal the design's?
  - Has anything that is now frozen changed since #351? At the tip, `Relational.lean` differs from #351 only in the two
    bodies (#357; Gate 48's frozen check 12/12).
- **#352:** a pure insertion into the frozen `Group.lean` at the brief's anchors (phase 1 `insertion_check.py`, with
  five controls; LE-grp1's head passes the same check against the tip, phase 2 P2-1). Did #352 change any existing line?
- **#365:**
  - The statements and docstrings of the frozen `pow_val_bijective`, `pow_val_mul` and `pow_val_mul_GT`, and of #352's
    three helpers, are unchanged; only their bodies change (§ *What changed*).
  - Is that within the sweep ruling ("proof-only, with statements and frozen headers unchanged")?
  - Is the frozen `pow_val_bijective` docstring's proof sketch still an accurate description, now that the proof
    delegates to the generic lemma (the sketch itself may not change)?

**3. Readers and API**
- Neither PR adds a definition, so no `_eq` reader is owed.
- Does any statement read a foreign definition by unfolding (`simulate`, `expect`, `prob`, `sample`, the `BilinearGroup`
  fields)?
- Is #365's lemma in the right home and namespace? It is a generic finite-group fact, in `Pairing/Group.lean` under
  `TCSlib.Cryptography.Pairing`, outside `BilinearGroup`. Policy asks for modular placement.

**4. Docstrings, sources, sketches**
- Every new declaration needs a formula docstring, and every proof of 15 lines or more needs a `**Proof sketch.**`
  (none here exceeds 10 lines).
- Tags or glue notes. The known slips below list the declarations with neither:
  - `expect_sample_rel`;
  - `abs_expect_sub_le_expect`;
  - #352's three helpers.

  Policy §2 lets purely technical glue omit the tag ("anything a reader would recognize as a result may not"). Grade
  each.
- Are the [BGZ09] locators (§3.4, §4.1 lemma `(=⟦⟧)`, Def. 5, §4.2 `⊨_φ`, §5.2 Lemma 1) and the [Sho04] locators (§1.1
  bridging steps, §4.2 Game 2) right against `references/` in `sources-r1.zip`? Phase 1 read them against the ingest
  anchors.
- Is the **Deviation** note honest (BGZ09 has no rule for adversary calls with a relational invariant)?
- Is #365's glue note (no [BB04] counterpart; assembled from Mathlib; nearest `IsCyclic.unique_zpow_zmod`) accurate?

**5. Duplication** (recent gates graded undisclosed re-proofs of public lemmas, and disclosed ones without a recorded
acceptance, as **majors**)

The staging sweep is `checks/dup-sweep.txt`: exact names and statement shapes over TCSlib at the tip and at #365's
head, and over Mathlib `029db123`. Its result:
- `abs_expect_sub_le_expect` against the private ETT copy: **DL-40** (open; Q6). It generalizes the same file's
  `abs_expect_sub_le` (constant bound). The `uexp` relatives (`abs_uexp_sub_le`, `MultiMsg.abs_uexp_sub_le_uprob`) use
  another carrier.
- `expect_simulate_rel` and `prob_simulate_rel` against `expect_simulate_congr` (`Games/Hopping.lean:384`, the `R = Eq`
  case) and `simulate_eq_of_abs` (`Games/Simulate.lean:334`):
  - both are disclosed in the module docstring;
  - the budgeted ETT `expect_simulate_abs(_inv)` (now also the protected `Games.expect_simulate_abs` in
    `Games/Tapes.lean:72`, Stage 1) are **not** instances of either (budget; design r1 §2's near-relatives table; Q5);
  - the specific bisimulations listed in that table are relatives.
- `expect_sample_rel`: no statement of the same shape (design: "L3 is new"); it composes `expect_sample_equiv`.
- `pow_val_add` and `pow_val_neg`: no Mathlib or TCSlib statement. After #365 they use `pow_mod_card`.
- `pow_val_bijective_of_ne_one`: the overlap with the frozen `pow_val_bijective` was found by this sweep and fixed by
  #365 (ruling 5). Its Mathlib relative `IsCyclic.unique_zpow_zmod` is disclosed in the #352 body.
- `pow_val_bijective_of_prime_card` (#365): **no exact Mathlib statement.** The nearest are:
  - `IsCyclic.unique_zpow_zmod`: `∃!` over `ZMod (Fintype.card α)` for a generator;
  - `zmodCyclicMulEquiv` and `mulEquivOfPrimeCardEq`: non-canonical isomorphisms;
  - `finEquivPowers` and `finEquivZPowers`: `Fin (orderOf x)` onto a sub(mono)group;
  - `IsPrimitiveRoot.zmodEquivZPowers`: roots of unity in a ring.

  In TCSlib, the nearest are `DiscreteLogHardcore.expo_bijective` (the concrete `ZMod (p − 1) → (ZMod p)ˣ`, whose
  order is not prime) and DDH's `orderOf_eq_of_mem_QR`/`zpowers_eq_QR` (subgroup facts). Neither is a restatement.

Is any declaration of the three PRs, or any inline step of their proofs, an undisclosed or unaccepted re-proof of a
public TCSlib or Mathlib lemma? Inline steps include, for example, #351's lower-bound step or `pow_val_neg`'s rewrite
chain. Does #365 leave any re-derivation in `Group.lean` (`checks/dup-sweep.txt` § 6: no `Nat.mod_add_div` is left)?

**6. Rule 10** (inner evidence ZIPs). Did any proof read a foreign definition other than through a published reader?
- **#351 (phase 2 R1, at the head):**
  - Seals, requests per variant (strict A / strict B / coe A / coe B):
    - `Probability` 36/36/35/35: coe 0 errors. Strict A and B fail once each at `ProbComp.dist_apply`, the `FinDist`
      coercion, identically at the base (BS-F06, DW-10 Q3).
    - `Relational` 53/53/52/52: 0 errors.
  - Paired controls ALL_OK in strict and coe (6 sealed negatives per harness).
  - Explicit-unfold scan: 101 items, 0 foreign.
- **#352 (phase 2b, at the merge tree `3029d8c3`):**
  - Seals: `Group` 567/568/567/568 and the carrier `Assumptions` 644/645/643/644, 0 errors.
  - Controls: 34 sealed negatives per harness, ALL_OK.
  - Scan: 56 items, 0 foreign.
  - Every probe, sealsum and control verdict is byte-identical to phase 2 R2.
- **#365:** the canonical coe-A seal of `Group` at base and head:
  - 567 requests, rc 0, 0 errors;
  - every request row, `requested`, `term_names`, `term_readers` and `closure_modules` equal;
  - byte-identical seal logs;
  - stored constants 82 → 83.

  No strict/B variant, no paired control and no consumer re-seal was run (the request set is unchanged; the new lemma
  names no TCSlib definition). Is that sufficient evidence for a proof-only change plus one Mathlib-only lemma?

**7. The evidence binding** (§ *Evidence binding* below). Does each piece of evidence bind to the commit it is claimed
for? Is the merged Lean of #351 and #352 the replayed Lean? Is #365's replay at a tree Lean-equal to its merge with the
tip? Is anything necessary missing? A missing necessary piece of evidence is a **major**.

**8. Is anything undisclosed?** Among the six commits, the three PR descriptions, the reviews, #365's report and the
records, is any change, claim or omission undisclosed? The known slips are listed below. Grade the review findings
**BS-F01 to BS-F13** in a separate table (agree, or regrade with the reason).

## Evidence binding

| Evidence | Bound to | What it shows | Reaches the merged / merge state by |
|---|---|---|---|
| Phase-1 review `review.md`, ZIP `6e4cbadd…` | worker series `912a343e`→`d742bf02` (Games) and `fc9cf2f5` (group, **before** LE-grp1, with `natCast_inj_of_lt`), issue base `bdcadd85` | static: reproduction, scope and insertion checks, statements vs design §2.2, decls2 8/0/0, citations, Mathlib relatives, style; recount of the worker's sweeps, seals and controls at the base | range-diffs 2/2 and 1/1 `=` to the landing heads (phase 2 P2-1); LE-grp1 only removes |
| Phase 2 R1, `phase2.md`, ZIP `411338e9…` | #351 head `dfacac35`; prospective tree `c6d3bed3` on snapshot #2 | 181/181 rc 0, state 1422 OK, admissions +2 (the two targets), axioms and traces, seals, controls, scan, lint, BS-F03 resolution probe | `cf7d28f7`'s Lean = `c6d3bed3` (`checks/lean-equality.txt`); the replay was adopted as **snapshot #3** (`snapshots/olean-snapshot-3-adopt/`, empty step-3 diff, map `e9dfbfdd…`) |
| Phase 2 R2 (same ZIP) | #352 head `92dea4f8`, tree `863b2926` on snapshot #2 | 12/12 rc 0, +0, seals, controls 34/34 | **superseded**: not adoptable after #351 merged (shared `BonehBoyen*` downstream) |
| Phase 2 P2-7 (same ZIP) | tree `66fdaf95` (tip × #346 × both heads) | 18/18 rc 0, admissions −1 +2 | cross-build only, discarded |
| Phase 2b, `phase2b-352.md`, ZIP `13483b25…` | REV `3029d8c3` = merge-tree(`c0752b2e` [Lean = `cf7d28f7`], `92dea4f8`) on snapshot #3 | 12/12 rc 0, state 1422 OK, admissions +0, axioms, seals 0 errors, controls ALL_OK, scan, lint | `463f2244`'s Lean = `3029d8c3`; adopted as **snapshot #4** (`snapshots/olean-snapshot-4-adopt/`, empty step-3 diff, map `6607620d…`) |
| #365 `report.md`, ZIP `48d787d4…` | head `5eaddd17` (`run-commit2/`) and commit 1 `6fc5f494` (`run-commit1/`), base `5aed9907` (Lean = TS2 `13fc8060`) | 22/22 rc 0, state 1434 OK, admissions 192 = 192, 8 constants standard, `Group` census 83 standard, coe-A seal equal, lint 92/103 unchanged, decls2 1/0/0 | replay on `olean-replay-grpfix`, a `cp -al` copy of `olean-replay-cs1-s6` (the TS2 replay; snapshot #7 adoption pending, not yet a snapshot), map `28677767…`; `merge-tree tip × 5eaddd17` is Lean-equal to the head (`checks/mergetrees.txt`) |
| Later builds over #351/#352 (indirect; none audits them) | snapshot #4 → Gate 44 T44′ → snapshot #5 (`3f540c22`); Stage 1 TS1 on #5 (Gate 47); #357 on #5 (Gate 48) → snapshot #6 (`8060f6b7`); TS2 on #6 | each later replay built on these oleans (reused or rebuilt) with rc 0; #357 proved both `Relational` targets with frozen headers (Gate 48 CLEAR) | records only |

## Known dispositions and slips (not findings)
- **The review findings** (`review.md`, `phase2.md`):
  - BS-F01 (minor; closed by LE-grp1).
  - BS-F02 (info, "ledger note"). The note was never filed. This gate's sweep found it (ruling 5), and #365 fixes it.
  - BS-F03 (closed by the resolution probe).
  - BS-F04 and BS-F05 (closed in phase 2).
  - BS-F06 (pre-existing strict `dist_apply`).
  - BS-F07 (pre-existing: older [Sho04] References line in `Games.lean:62` and `Hopping.lean:53`).
  - BS-F08 (signing key).
  - BS-F09 (Stage 1 merge with the facade).
  - BS-F10 (evidence nits).
  - BS-F11 (commit message of `2cca41bc`).
  - BS-F12 (trailers and signatures).
  - BS-F13 (the maintainer's own first probe failed).

  **Grade them.**
- **Missing tags and glue notes** (#351, #352):
  - `expect_sample_rel`'s docstring carries neither a tag nor a glue note. The Gate 48 staging recorded it for DW-11.
  - Phase 1 also lists `abs_expect_sub_le_expect` and #352's three helpers without either.
  - `pow_val_bijective_of_ne_one` has no [BB04] anchor, whereas its `G_T` twin cites [BB04, §3.1].
  - #365 leaves every existing docstring unchanged by design, so these remain.
- **Stale PR descriptions** (`pr351-description.md`, `pr352-description.md`, as read at staging):
  - Both say "under Q8 the audit belongs to the bb1-sim gate". DW-11 superseded this.
  - #352's "Checks" cite phase 2 (snapshot #2, state 1421/1421), not phase 2b (`phase2b-352.md`, snapshot #3,
    1422/1422), which is the evidence for the merged tree.
  - #352's body names the Mathlib relative of `pow_val_bijective_of_ne_one` but not its in-file twin (the overlap that
    #365 fixes).
- **BS-F11:** `2cca41bc`'s message still lists `natCast_inj_of_lt` and says Mathlib states none of the helpers. The #352
  body discloses it.
- **#365's wording:** commit 1's message and the PR body call the change "proof-only" while it adds one public lemma.
  Both list the lemma.
- **#365's evidence scope:**
  - Rule 10 is the canonical coe-A seal of `Group` only (question 6).
  - The replay base is the TS2 replay, not an adopted snapshot.
  - The admissions census was derived with `censusderive.py`, because older record sets had been removed in a disk
    clean-up.
  - Deviations recorded in the report: one trial compile and one standalone probe before commit 1, and a failed base
    axioms attempt (no toolchain file; no Lean ran).
  - Commit 2 was made at the maintainer's request.
- **Relational docstring:** it does not cross-reference the budgeted `Games.expect_simulate_abs` that Stage 1 added
  later. The relation is recorded in design r1 §2 and ruling Q5.
- **Signatures:**
  - The picks and #365's commits are SSH-signed with the account key (BS-F08).
  - The merge commits `cf7d28f7` and `463f2244` carry GitHub's web-flow PGP signature (`checks/series.txt`).
  - The worker commits were unsigned.
- **Authorship:** the #351/#352 code is an external Claude worker's, delivered as patches and cherry-picked by the
  maintainer. LE-grp1 and #365 are the maintainer's.
- **No Lean, no `lake`** was run for this staging. `checks/` are git-object reads; the rest is the recorded evidence.

## Merge interaction (maintainer merge conditions for #365, not audit items)

`checks/mergetrees.txt`:
- #365 × the tip `b31b77f7`: clean, tree `319c9aa0…`, Lean-equal to the head.
- #365 × the open GSW 6a PRs #358 (`a616adca`), #359 (`d154c883`) and #360 (`cc05f76c`): all clean, with no shared path.
- **Adoption:** if #365 merges onto a tip whose Lean is still TS2's, `olean-replay-grpfix` is the replay at the merge
  tree (the step-3 diff against `5eaddd17` must be empty). Otherwise, re-replay (22 modules).

## Evidence files
- **`pack-r1.md`** (this file) and **`dispatch-r1.md`** (the Codex prompt; records only).
- **`pr351.diff.txt`**, **`pr352.diff.txt`**, **`pr365.diff.txt`**: `git diff` from each merge base to each head. For
  #351 and #352 this equals the merge commit's first-parent diff byte for byte.
- **`pr351-description.md`**, **`pr352-description.md`**, **`pr365-description.md`**: the PR bodies at staging (REST
  `.body`, raw).
- **`source-head-r1.json`**: the pins; each commit (parents, tree, author, signature kind, files); the merge commits;
  and each file's SHA-256, line count, maximum width, over-width, tab and trailing-space counts at base and head.
- **`sources-r1.zip`**: each PR's files at base and head; context at the tip (the relatives, the ETT copy, the helper
  consumers, `Relational.lean` with #357's bodies); the two Mathlib files with the nearest relatives; and the [BGZ09],
  [Sho04] and [BB04] transcriptions. `README.md` gives every entry's SHA-256 and origin.
- **`verification-r1.zip`**: `MANIFEST.md` (provenance), `POINTERS.md`, and `SHA256SUMS` (every other entry). It holds:
  - `evidence/`: the four evidence ZIPs, nested unchanged, with the records' sums;
  - `snapshots/`: the #3 and #4 adoption folders;
  - `checks/`, with its tools;
  - `records/`: the reviews, #365's report, the rulings, the design note and issued statement brief, `policy.md`,
    Gate 44/47/48 findings, and the decision-log, ledger, deferred-work, Stage 2 and snapshot-register extracts;
  - `pr/`: the REST fields.
- **`SHA256SUMS-r1`**: the files of this gate directory other than `dispatch-r1.md`.

## Findings delivery

Return `gate49-dw11-findings.md` as Markdown in this chat. If you have several evidence files, return a ZIP. The user
dispatches and merges.

| # | Severity | PR · file · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

Number the findings **G49-01, G49-02, …**. Grade BS-F01 to BS-F13 in a separate table. Report the audited heads and
merges, the records pin, the counts by severity, and a verdict **per PR** (#351, #352, #365) and **overall**:
- **CLEAR:** zero blockers and zero majors.
- **HOLD:** otherwise.

For the merged #351 and #352, a HOLD means a follow-up fix PR, not a revert.

**Severities**
- **blocker:** a false or unusable statement, a proof that does not establish its statement, or a scope violation.
- **major:** any of the following:
  - a changed frozen statement or statement prose;
  - a forbidden read not covered by the rulings;
  - an undisclosed copied private lemma, or an undisclosed (or unaccepted) re-proof of a public one;
  - a fabricated source tag;
  - necessary evidence that cannot be verified or does not bind to the audited commit.
- **minor:** documentation or API defects, including an inaccurate formula docstring, glue note, proof sketch, citation
  or PR description.
- **note:** anything else.

## ===== briefs/pairings/fills/bb1-sim/statements-final-r1/review.md (records, at ab17e37feb00a677d69f6abd5ff7e427e3b9ef3c) =====

# bb1-sim-statements · maintainer delivery review (r1)

**Verdict (interim, phase 1 of 2): ACCEPT WITH ONE OPTIONAL LANDING EDIT, pending one ruling and the phase-2 Lean checks.**
- Both series reproduce hash for hash, and every change is a pure insertion or the new module, inside the brief's scope tables.
  - **Series 1** (Games): `expect_simulate_rel` and `expect_sample_rel` are `sorry`'d with design r1 §2.2's headers verbatim. `prob_simulate_rel` is proved from the target, and `ProbComp.abs_expect_sub_le_expect` is proved and public.
  - **Series 2** (group helpers): the four Q10 helpers are proved.
- decls2 gives exactly the 8 expected ADDED, with 0 CHANGED and 0 REMOVED. Admissions are +2 (the two targets) for series 1 and +0 for series 2.
- Phase 1 found 0 blockers, 0 majors, 2 minors (BS-F01, BS-F08) and 8 infos.
- **BS-F01 needs Seyoon's ruling.** `natCast_inj_of_lt` is an iff wrapper of Mathlib's `CharP.natCast_injOn_Iio`, and the brief's Mathlib-first rule says not to insert it.
  - Recommended: the landing edit **LE-grp1**, which drops the helper and its bullet. Group.lean stays a pure insertion.
  - If Seyoon keeps it, the group PR lands as delivered, with a ledger note.
- The verdict becomes final only after phase 2 (`PHASE2-PLAN.txt`, below).

## Delivery and landing
- **Delivery:** Claude, a lead with one sub-agent (`probe`).
  - Final: exchange `a3cb45f6a83c7308db5f2c5fcf95d25fc7f3fef9` ("stmt bb1-sim: final").
  - Checkpoint 1: `8899115b8292b0ff001dd325bea9a8054074d279`. It holds the probe and series 2.
  - Both commits touch only `inbox/fills/bb1-sim-statements/`. Nothing on the exchange changes that path after the final.
  - The final keeps checkpoint 1's `probe/` (tree `7f2578fa…`), `patches/group-helpers/` and `src/group-helpers/` unchanged. Seyoon has already ruled on the probe (Q7 follow-up: ten readers, which land in the fill PR, not here).
- **Issue base:** `bdcadd858cbe043e8c41e465a96e81feb1eecda1`. Series heads:
  - `stmt/games-relational`: `912a343e538f9b5d9306561a35100f5490a6a11b` (`Probability.lean` only), then `d742bf025d471c3ba0ef889bd4e8986ff9062aeb` (`Relational.lean` and the facade);
  - `stmt/pairing-group-helpers`: `fc9cf2f510622a6a1027c14a614c1d453da5d520`.
- **Files** against the base:

  | File | Lines (base → head) | Change |
  |---|---|---|
  | `Games/Relational.lean` | new, 134 | the module of design §2.2, citations per Q11 |
  | `Games/Probability.lean` | 409 → 423 | bullet after line 48; lemma after line 403 |
  | `Games.lean` (facade) | 64 → 67 | import after line 9; `## Contents` entry after line 42 |
  | `Pairing/Group.lean` | 304 → 338 | four bullets after line 62; helper block after line 232 (`pow_val_bijective`) |

  Nothing else changes. `Defs.lean`, `BonehBoyen.lean`, `Forgery.lean`, `Hopping.lean`, `Simulate.lean`, `TCSlib.lean` and `blueprint/` are untouched.
- **Records tip** after the container restart: `7486e401c5a274c2f67590eb3ea264fdf209186c`. It is records-only since the start of this review (`e6734ef4`). Its Lean equals snapshot #2's `T` (`a6d01b1b`, 0 files differ).
- **Merge checks** (`git merge-tree --write-tree`; all clean, 0 conflicts; the series files are blob-equal in every result):
  - tip × series 1 → `fe093214d79ca1ca312540d7d137e8e32e4bf186`;
  - tip × series 2 → `dd8d3efcbd6415dabc29a58ef5ed133306964c3d`;
  - #346 head `89a18a8225be1b76166af12a15179da291747783` × series 1 → `851e83b1…`;
  - #346 head × series 2 → `d475bcf0…`;
  - tip × #346 × series 1 × series 2 → `21c1aa45bdbd34fd0db085688f25f17471463315`.

  #346 and the tip leave all four series files unchanged. The dry-run cherry-picks onto the tip are clean, and their trees equal the merge-tree trees.
- **Evidence:** `bb1-sim-statements-r1-phase1-evidence.zip`, SHA-256 `6e4cbadd51e8478fb9093172e42dc6fd4da7b1a1e8ed1408047d9c60bb86c960`, 68 entries under `bb1-sim-statements-r1/` (53 files with its own `SHA256SUMS`); `evidence-SHA256SUMS` sits beside it.

## Checks (phase 1)
- **Integrity.**
  - **Manifests,** streamed from git, with exact path sets and no `./`:
    - final: top-level 1639/1639 and `evidence/` 1622/1622;
    - checkpoint 1: 1149/1149 and 1138/1138.
  - **Issue package:** 8/8. The design, policy and ingest hashes equal the brief's pins.
- **Reproduction.** I ran `git am` at the base in new sparse worktrees on the local branches `review/bb1sim-games` and `review/bb1sim-group`, never pushed. I used `COMMITS.tsv`'s committer data and no signing.
  - All 3 hashes reproduce.
  - `COMMITS.tsv` has the signing column, `none` in all rows, and the commits really are unsigned.
  - `src/` equals the changed path set of each series byte for byte (3 + 1 files).
  - After the restart, both worktrees were checked: clean, with no `am` in progress and the heads as reproduced.
- **Scope** (my `insertion_check.py`, independent of the worker's):
  - Every difflib opcode against the base is `equal` or `insert`. Each block is at the brief's anchor: `Probability` 48 and 403, `Games` 9 and 42, `Group` 62 and 232.
  - Removing the blocks restores the base byte for byte (`a7d79d12…`, `dd67d695…`, `ae72aa9c…`, the brief's pins).
  - Head hashes: `ddbe55e9…`, `1ee49c04…` and `235b0646…`.
  - Commit 1 alone also passes for `Probability`.
  - Five controls per file all behave as required: a changed character, a deleted line, an extra line, a moved block, and the unchanged file.
- **Statements.**
  - The three `Relational` headers and its two imports are byte-identical to design §2.2. Its prose differs only by the brief's supersessions:
    - the citation placeholders are replaced;
    - the F4 deviation note, plus one permitted sentence;
    - the References lines;
    - a sketch and an [Sho04] tag on `prob_simulate_rel`.
  - The averaging lemma is byte-identical to the brief's §1a block. It is the ETT copy with `α` for `β`.
  - The facade entry and the `Probability` bullet are the brief's text.
  - **decls2** (the maintainer copy, run in the reproduced worktrees) gives exactly the expected declarations, with empty `.err` files. Its output equals the delivered TSVs.
    - Series 1 ADDED: `expect_simulate_rel`, `prob_simulate_rel`, `expect_sample_rel` and `abs_expect_sub_le_expect`.
    - Series 2 ADDED: `pow_val_add`, `pow_val_neg`, `pow_val_bijective_of_ne_one` and `natCast_inj_of_lt` (the identity-injectivity form).
    - 0 CHANGED and 0 REMOVED in both.
  - The delivered `StmtDump` types match the source headers.
- **Admissions.**
  - Source level: series 1 adds exactly 2 `sorry` (`Relational:93`, `:130`) and series 2 adds 0.
  - The delivered admission checks pass against `base-sorries.txt`: 28 → 30 for series 1, 28 for series 2.
  - In the raw sweep logs, `Relational` has exactly 2 `sorry` warnings (lines 85 and 124), and `prob_simulate_rel` has none.
- **Docstrings, sketches and sources.**
  - Every new declaration has a formula docstring. Both targets and `prob_simulate_rel` carry a `**Proof sketch.**`. Every new declaration with its proof is under 15 lines (2–10).
  - Every bracketed citation is one of the seven approved strings (`citations_check.py`).
    - `expect_simulate_rel` has all seven.
    - `prob_simulate_rel` has `[Sho04, §1.1, bridging steps]`.
    - `expect_sample_rel`, the averaging bound and the helpers carry no tag.
  - The F4 note is verbatim after `**Deviation:**`. There is no "adversary rule" wording and no `[BGZ09, rule`.
  - The module References are the review §4 lines verbatim.
  - I read each cited claim against the ingest anchors (`p006-b001` "free to call oracles", `p007-b002`, `p007-b005`, `p008-b003` `⊨_φ`, `p009-b002`/`p009-b003`/`p010-b001`, Sho04 `p003-b002` and `p013-b001`). All are faithful.
- **Style.**
  - Widths are at most 99, and sizes are at most 423 lines.
  - The new code has no `@[simp]`, `attribute`, `open`, tab, trailing space or micro sign. The base's own `@[simp]` and `attribute` lines only shift.
  - `style_lint` gives 0 findings on the 4 files.
  - `campaign_style_lint --check8b` gives 92 FAIL / 103 WARN at the base and at both heads, over 450 → 451 / 450 files. The FAIL/WARN line sets are identical; only INFO size lines change. My runs equal the delivered outputs.
- **Clashes and name resolution.**
  - The 8 names on all 279 ref tips: the only other declaration is the private `ETTGame.abs_expect_sub_le_expect` (`Forgery.lean:515`), and no Mathlib declaration shares a name.
  - Resolution and protection: see BS-F03.
- **Duplication and reuse.**
  - All 15 `path:line` citations I checked in the REPORT's added rows hold at the base.
  - The averaging bound is the disclosed, ruled duplicate of the ETT copy (Q6); the Stage 2 re-point is a pure deletion.
  - In Mathlib (sources at the pinned `029db123`):
    - `natCast_inj_of_lt` restates `CharP.natCast_injOn_Iio` (BS-F01);
    - `pow_val_bijective_of_ne_one` has an undisclosed near relative, `IsCyclic.unique_zpow_zmod`, which is not usable as is (BS-F02);
    - `pow_val_add` and `pow_val_neg` have no Mathlib statement.
  - No library lemma restates any helper: Schnorr, MatchingMath and Primality only inline the laws.
- **Rule 10, by source reading.** The new proofs use only published lemmas (`expect_sub`, `expect_mono`, `expect_const_mul`, `prob_eq_expect`, the `B.pow_order`/`card_G` fields, and the Mathlib `ZMod`/`orderOf` API). There is no `unfold`, `delta`, `change` or `show` of a definition.
- **Delivered evidence, recounted from the raw logs** (`recount.py`, `sweepbind.py`, `seal_recount.py`, `ctl_recount.py`; regex `^\S+\.lean:\d+:\d+: error[:(]`):
  - **Run directories:** 73, with 1091 records and every log hash matching. Each record's error and `sorry` counts equal my recount. The only nonzero-rc runs are the expected ones:
    - the Mathlib `exact?` probe;
    - the strict `dist_apply` seals;
    - the sealed control probes;
    - scan attempt 1;
    - the probe's refuted alternatives.
  - **Sweeps** (all with every source bound to its head, and the module set equal to the expected one):
    - series 1: 151/151 rc 0, 0 errors in both forms; the expected 150 modules + `Relational`;
    - series 2: 11/11 rc 0, 0 errors; equal to `DOWN-GROUP`;
    - bootstrap S: 612/612 against `order.txt`, 28 `sorry` warnings;
    - bootstrap P: 189/189, bound to `c90273fa`, equal to T4's `order-final.txt` (`f17ade1e…`);
    - commit-1 check: 1/1.

    The warning lines of every swept module equal its bootstrap log.
  - **Seals:** 16 at the heads and 8 at the base. Each probe is the owner's source plus the harness only, and has install and EOF records with `requested = verified`. Counts (strict A / strict B / coe A / coe B):

    | Owner | Counts | Errors |
    |---|---|---|
    | `Relational` | 53/53/52/52 | 0 |
    | `Probability` | 36/36/35/35 | 0 in coe; strict 1 each, `dist_apply` (BS-F06) |
    | `Group` | 567/568/567/568 | 0 |
    | `Assumptions` (control carrier) | 644/645/643/644 | 0 |

    The base seals are identical: `dist_apply` is at base line 402 and head line 403. The request name sets of `Probability` and `Group` equal the base's in all four variants. Strict minus coe is exactly `FinDist.instCoeFunForallReal`.
  - **Controls:** in both variants, every sealed negative fails exactly once (series 1: 6/6, series 2: 34/34), 0 positives fail, unsealed probes have 0 errors, there are 0 stray errors, and the result is ALL_OK. The pretest has 0 errors.
  - **Axioms:**
    - `abs_expect_sub_le_expect` and the four helpers use `[propext, Classical.choice, Quot.sound]`;
    - the three `Relational` lemmas use those plus `sorryAx`;
    - the census: `Relational` and `Probability` 60 constants, non-standard only in those three; `Group` 83 constants, 0 non-standard;
    - the trace: each target reaches only itself, so each is the only `sorryAx` user in its closure; `prob_simulate_rel` reaches exactly `expect_simulate_rel`.
  - **Unfold scan:** 0 foreign in both series (101 and 59 items).
  - **Gaps:** none blocking. The sweeps ran at the issue base, so the 27 modules #341 added downstream of `Probability` and the two `audits/*/Checks` are not covered (BS-F04, BS-F05); phase 2 covers them.

## Findings

| # | Severity | Finding | Disposition |
|---|---|---|---|
| BS-F01 | minor, undisclosed relative | `BilinearGroup.natCast_inj_of_lt` (`Group.lean:262–267`) is an `iff` wrapper of Mathlib's `CharP.natCast_injOn_Iio`. With `ZMod.charP`, `CharP.natCast_injOn_Iio (ZMod B.order) B.order hm hn : (m : ZMod B.order) = n → m = n` is the substantive direction, and the converse is `congrArg`. The fill needs only the injective direction (`idToZ ID ≠ idToZ ID*`), so Mathlib states the helper "in a form the fill can use directly", and the brief says not to insert it. The worker posed the `iff` to `exact?` (which cannot find it) and grepped only `Data/ZMod/`; the REPORT says "Mathlib states none of them in a directly usable form". Q10 lists "identity injectivity on good coins" among the approved helpers, subject to "reuse Mathlib … where it applies". | **Ruling needed.** Recommended: **LE-grp1** (`landing/LE-grp1-proposed.diff`) deletes the helper and its bullet (−7 lines). `Group.lean` stays a pure insertion (`59c605e1…`, 331 lines, insertion check PASS), and the fill uses `CharP.natCast_injOn_Iio`. If Seyoon prefers the `iff` convenience, keep it, name the Mathlib lemma in its docstring at the fill, and add a ledger row. |
| BS-F02 | info, undisclosed near relative | `pow_val_bijective_of_ne_one`: Mathlib's `IsCyclic.unique_zpow_zmod` states `∃! n : ZMod (Fintype.card α), x = a ^ n.val` for a generator `a`. It is indexed by `ZMod (Fintype.card B.G)`, not `ZMod B.order`, and needs a generator hypothesis, so it is not a restatement. The proof repeats `pow_val_bijective`'s seven lines with `G` for `G_T`, which the REPORT discloses. | Ledger note: a generic prime-order lemma could carry both later. Re-proving the frozen `pow_val_bijective` needs a frozen-file ruling. No action here. |
| BS-F03 | info | Name resolution and protection of `ProbComp.abs_expect_sub_le_expect`. It is not `protected`, which is consistent with `Probability.lean`, where no lemma is protected. Inside `namespace …ETTGame`, Lean resolves a bare name through the current namespace before open declarations, so the call at `Forgery.lean:545` resolves to the private copy; the two statements are identical anyway. The worker's sweep built `Forgery.lean` with rc 0, bound to the head. No other declaration of the name exists on any ref. After the Stage 2 deletion of the private copy, the call resolves to the public lemma through `open … ProbComp`, with the same binder names (`c f g h hb`). | Phase 2 (P2-2) adds a resolution probe. |
| BS-F04 | info, pack | The issued `closures.txt` and `order.txt` omit the two modules `audits/pass-shelat/Checks` and `audits/garg-ch1-3/Checks`, which are downstream of `Probability`. `base-sorries.txt` lists 13 modules where the README and brief say 14; the worker disclosed this. | Phase 2 rebuilds both `Checks`. Fix the pack template. |
| BS-F05 | info | The sweeps ran at the issue base, as the brief asked. At the tip, `Probability`'s downstream has 27 more modules (`Yao/HybridProof/*`, #341). | Phase-2 replay R1: 181 modules, root and both `Checks` included. |
| BS-F06 | info, pre-existing | The strict seals of `Probability` fail once, at `ProbComp.dist_apply` (`FinDist` `CoeFun` request), identically at the base. The canonical coe seals pass. | DW-10 / Stage 2. No action here. |
| BS-F07 | info, pre-existing | The frozen `Games.lean:62` and `Hopping.lean:53` carry an older [Sho04] References line (sentence-case title, "IACR ePrint"), not the review §4 string that `Relational.lean` now uses. | Docstring-only, for the Stage 2/3 citation pass. Out of scope here. |
| BS-F08 | minor, process | The final exchange commit `a3cb45f6` carries an SSH signature by key `SHA256:32dP45eSMmVSt/G/CGvcxl/P+MO3Nwj9xeTh/GSA2wc`, the key that signs the maintainer's staging and records commits (`a6a21775`, `66419662`, `7486e401`). Checkpoint 1 is unsigned. `workflow.md` §4.1 says workers commit with signing off. The series commits themselves are unsigned and reproduce, so the content is unaffected; the signature does not attest maintainer authorship. | Record it, and check the worker environment's signing configuration before the next dispatch. |
| BS-F09 | info | Cleanup Stage 1 inserts into `Games.lean` after lines 11 and 47 (its issued brief). A simulated three-way merge with series 1 (after 9 and 42) is clean (`git merge-file` rc 0). | Merge the Games PR first, as the stage preconditions say. |
| BS-F10 | info, evidence nits | Evidence nits:<br>• Scan attempt 1 stopped with a `KeyError`; this is disclosed.<br>• Between checkpoint 1 and the final, 14 tool copies gained header lines only, and `rule10_b.sh` gained its recorded `R10DIR`/`TOUCHED` change.<br>• The group-helpers `insertion-check.out` changed only in its base path label (same hashes).<br>• `current.pid` files were removed.<br>• The series commits carry the standard attribution trailers, as #346's landed commits do. | None. |

## Landing plan
Two PRs, each cherry-picked onto the records tip. Authors are kept, the committer is Claude, and each commit is SSH-signed with the Co-Authored-By and Claude-Session trailers.
- **PR 1, the Games statement PR** (Q9: its own small PR on the records tip). Branch `land/bb1-sim-games` from `7486e401`, cherry-picking `912a343e` and `d742bf02`.
  - Dry run: both picks are clean, with tree `fe093214…` (= merge-tree tip × `d742bf02`). The expected range-diff is 2/2 identical.
  - No landing edit. Its diff against the tip is the 3 files.
  - Draft on `cryptography/pass-shelat-ch2-4`. Q8 puts its audit in the bb1-sim gate after Gate 44.
  - The cleanup stages need it merged before Stage 1, and it frees `Probability.lean` for CS1-Q9 and the Stage 2 re-point. So merge it on Seyoon's approval once phase 2 passes, ahead of the gate.
- **PR 2, the group-helper PR.** Branch `land/bb1-sim-group` from `7486e401`, cherry-picking `fc9cf2f5` (clean, tree `dd8d3efc…`), then **LE-grp1** as one signed commit if Seyoon rules for it (BS-F01).
  - Its diff against the tip is `Group.lean` only.
  - Its downstream overlaps #346 (`BonehBoyen*`), so it goes with the bb1-sim gate and the fill. It may merge before #346; after #346 merges, re-replay it.
- **Order** (`workflow.md` §6.1 step 4): the Games PR has the largest rebuild (181 modules), so merge it first. Then re-replay #346 and the group PR on the new tip; each rebuilds only its own closure (12, or 17 after #346).
- **Merge conditions:** the phase-2 checklist passes, and BS-F01 is ruled.

## Phase-2 checklist (merged-tree replays per `snapshots.md`; `PHASE2-PLAN.txt` has the exact steps)
- **P2-0 Tip and snapshot.** Re-fetch the tip. If any Lean or lake file changed since `7486e401`, redo `landing/`. Verify snapshot #2 (`95493449…`, `T` `a6d01b1b`) at 0/0/0 before and after.
- **P2-1 Landing branches.** Build both as above, with range-diff 2/2 and 1/1 and the trees `fe093214`/`dd8d3efc`. Apply LE-grp1 only on the ruling. Check the export against `src/`.
- **P2-2 Replay R1 (Games PR).** Use `cp -al` of the snapshot, the overlay, `stateplan`/`downorder`/`fullorder`, then `runner.py`.
  - Rebuild at least the 181 modules of `landing/down-games-pr-merged.txt`: `Probability`, `Relational`, the downstream, root, and both `Checks`.
  - Require rc 0 and 0 `error:`/`error(`, a state check that is OK, and link count 1.
  - `Relational` has exactly 2 `sorry` warnings, and other warnings are unchanged. Admissions go from the tip by +2, exactly the targets.
  - Name-resolution probes (BS-F03).
- **P2-3 Axioms.**
  - The averaging bound: standard three.
  - The three `Relational` lemmas: those plus `sorryAx`.
  - Census: non-standard only in those three.
  - Trace: each target reaches only itself, and `prob_simulate_rel` reaches only `expect_simulate_rel`.
- **P2-4 Rule 10 on R1.**
  - Seals of `Probability` 36/36/35/35 and `Relational` 53/53/52/52. Coe gives 0 errors; strict gives only `dist_apply` in `Probability`.
  - Controls are ALL_OK in both variants, and the unfold scan finds 0 foreign.
- **P2-5 Replay R2 (group PR).**
  - Rebuild 12 modules, or 17 if #346 has merged.
  - Admissions +0. The helpers use the standard three, and the census has 0 non-standard.
  - Seals: `Group` 567/568/567/568 and the carrier `Assumptions` 644/645/643/644, with 0 errors.
  - Controls 34/34 per harness, ALL_OK; the scan finds 0 foreign.
  - With LE-grp1, the request sets are unchanged.
- **P2-6 Lint.** Tip against each head: no new FAIL/WARN line, `style_lint` 0, and `sk15` none.
- **P2-7 (recommended)** Cross-build tree `21c1aa45` (tip × #346 × both series). Expect admissions −1 (T4) +2 against the tip; `bb1_sidSecure` reaches exactly T2/T3.
- **P2-8 Order, adopt and record.**
  - Merge the Games PR first. On each merge, the prospective-tree diff must be empty, and then the replay output is adopted (recipe step 6), with a new `snapshots.md` row. Otherwise, discard it and replay again.
  - Then zip the phase-2 evidence, finalize this review, add the decision-log row, and open the draft PRs.

## Evidence (`bb1-sim-statements-r1-phase1-evidence.zip`, under `bb1-sim-statements-r1/`)
- `PROVENANCE.txt`, `PHASE2-PLAN.txt`, `SHA256SUMS`.
- `integrity/`, `scope/`, `statements/`, `admissions/`, `citations/`, `style/`, `lint/`, `clash/` and `overlap/` (including `mathlib-relatives.txt`).
- `rule10/`: request sets against the base; source reading.
- `delivered-evidence/`: recounts of every run, the sweeps, seals and controls.
- `landing/`: the merge-tree runs (at `7486e401`, and the pre-restart run at `e6734ef4`), closures, the facade merge with Stage 1, and `LE-grp1-proposed.diff` with its insertion check.
- `tools/`: `manifest_check.py`, `insertion_check.py`, `style_scan.py`, `citations_check.py`, `decl_scan.py`, `closures.py`, `recount.py`, `sweepbind.py`, `seal_recount.py`, `ctl_recount.py`, and an unmodified copy of `decls2.py`.

**Not yet clear to merge — BS-F01 needs Seyoon's ruling (LE-grp1 recommended), and phase 2 (the Lean replays) is pending; no PR is opened yet**

## Ruling (2026-11-17)
- **BS-F01: drop the helper (Seyoon).** The group-helper PR lands `fc9cf2f5` plus **LE-grp1**, which removes `natCast_inj_of_lt` and its docstring bullet (−7 lines). `Group.lean` remains a pure insertion. Phase 2 builds and seals the LE-grp1 head.

## Final verdict (phase 2, 2026-11-17): ACCEPT
Phase 2 (`phase2.md`, evidence zip `411338e9…`) passes P2-0 to P2-7 on both landing heads; 0 blockers, 0 majors, 0 minors, 3 new infos (BS-F11–BS-F13). BS-F03, BS-F04 and BS-F05 are closed.
- **`land/bb1-sim-games` `dfacac356ff1225aca4c900d81bbf2cabce7b499`:** 181/181 rebuilt rc 0 (root and both `audits/*/Checks` included), state 1422/1422, admissions +2 (the targets), axioms as planned, seals `Probability` 36/36/35/35 and `Relational` 53/53/52/52 with coe 0 errors (the strict `dist_apply` failure is pre-existing and, by DW-10 Q3, notation), controls ALL_OK, 0 foreign unfolds, lint line sets unchanged. Replay output kept as `$SP/olean-replay-bb1sim-games`.
- **`land/bb1-sim-group` `92dea4f8126747ea7e816984349b9dbb789f0065` (LE-grp1):** 12/12 rc 0, state 1421/1421, admissions +0, standard axioms only, seals `Group` 567/568/567/568 and `Assumptions` 644/645/643/644 with 0 errors, controls ALL_OK, 0 foreign unfolds.
- **Cross-build** tip × #346 × both heads (tree `66fdaf95…`): 18 modules rc 0, state 1427/1427; `bb1_sidSecure` reaches exactly T2 and T3.
- **Order:** the Games PR merges first (adopt its replay as snapshot #3 when the merge commit's Lean equals tree `c6d3bed3`); then the group PR and #346 re-replay on the new tip (12 or 17 modules).

## ===== briefs/pairings/fills/bb1-sim/statements-final-r1/phase2.md (records, at ab17e37feb00a677d69f6abd5ff7e427e3b9ef3c) =====

# bb1-sim-statements · maintainer delivery review (r1), phase 2: merged-tree Lean replays

**Verdict.**
- **`land/bb1-sim-games`** (`dfacac35`): **PASS**. It is ready for its PR.
- **`land/bb1-sim-group`** (`92dea4f8`, with LE-grp1): **PASS**. It is ready for its PR, which merges after the Games PR
  and a 12-module re-replay on the new snapshot (§ P2-8).
- Phase 2 found 0 blockers, 0 majors, 0 minors and 3 new infos (BS-F11–BS-F13).
- BS-F03, BS-F04 and BS-F05 are closed. BS-F06 is reconfirmed as pre-existing at the tip.
- Every check in `PHASE2-PLAN.txt` P2-0 to P2-7 holds:

  | Check | Games head | Group head |
  |---|---|---|
  | Range-diff (landing commits against the reproduced series) | 2/2 `=` | 1/1 `=`, plus LE-grp1 |
  | Rebuilt modules | 181 | 12 |
  | Every rebuilt module | rc 0, 0 `error:`/`error(` | the same |
  | Admissions against the tip | +2, exactly the two targets | +0 |
  | Axioms and census | as expected | as expected |
  | Seals (strict A/B, coe A/B) | as expected; strict `dist_apply` failure identical at the tip | as expected, 0 errors |
  | Controls | ALL_OK | ALL_OK |
  | Explicit-unfold scan | 0 foreign | 0 foreign |
  | Lint | no new FAIL/WARN | no new FAIL/WARN |

  The cross-build of tip × #346 × both heads gives rc 0 and admissions −1 +2.
- The snapshot rehashed 0/0/0 four times: before the replays, after R1, after R2, and at the end.

Run on 2026-11-17, 01:55–02:55 UTC. `$SP` is `/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`.
- **Evidence:** `bb1-sim-statements-r1-phase2-evidence.zip`, under `bb1-sim-statements-r1-phase2/`. It has
  `PROVENANCE.txt` and `SHA256SUMS`, and its own SHA-256 is in `evidence-SHA256SUMS`.
- **Not done:** nothing was committed, pushed or `git add`ed, no PR was opened, and the landing branches stay local.
- **Builds:** there was no `lake build` and no cache get, and this job ran one Lean process at a time.
- **#346's job:** its directories (`$SP/p346`, `$SP/olean-replay-346`) and processes were not touched.

## P2-0 Tip and snapshot
- `git fetch` gave the records tip **`f472accd5e000a53d0fbe02b5414435429ce4a70`** ("Records: bb1-sim landing branches
  built; phase 2 started").
  - It is records-only since `7486e401`.
  - It has the same `TCSlib/`, `TCSlib.lean`, `audits/`, `scripts/`, lakefile, toolchain and manifest as:
    - `7486e401`;
    - the landing parent `176cfd4a42ac3300d9b84f9045f7abcd0f52ef13`;
    - snapshot #2's T `a6d01b1b`.

    In each case 0 files differ, so `landing/` did not need to be redone.
  - The landing branches sit on `176cfd4a`, an ancestor of the tip.
  - `merge-tree` of the current tip with each head (`787cd003`, `b293ebff`) is Lean-equal to that head's own tree.
- **Snapshot #2** (`$SP/olean-snapshot`) was rehashed with `snapmap.py verify` against map `95493449…c111`.
  - Each run had 1452 files and gave **0 extra / 0 changed / 0 missing**, with no symlinks and no empty directories.
  - It ran before R1, after R1, after R2, and after the P2-7 discard (`snapshot/`).
  - The snapshot was never written to, and was read only as the source of `cp -al`.

## P2-1 Landing branches
- **Range-diffs** (`landing/p2-1-landing.txt`):
  - `bdcadd85..d742bf02` against `176cfd4a..land/bb1-sim-games` gives **2/2 `=`**: `912a343e`→`02000ad4` and
    `d742bf02`→`dfacac35`.
  - `bdcadd85..fc9cf2f5` against `176cfd4a..land/bb1-sim-group` gives **1/1 `=`** (`fc9cf2f5`→`2cca41bc`), and
    `> 2: 92dea4f8` is LE-grp1, the only other commit.
- **Trees** (`landing/p2-1-trees.txt`):
  - The games head's tree is `c6d3bed3`. It equals `merge-tree 176cfd4a × d742bf02`, and it is Lean-equal to phase 1's
    `fe093214`: 0 Lean/lake paths differ. The 5 paths that do differ are the records files the tip gained since `7486e401`.
  - `land/bb1-sim-group~1` has tree `8740ccb6`, which is Lean-equal to `dd8d3efc` in the same way.
- **LE-grp1:**
  - Its hunks are byte-identical to `landing/LE-grp1-proposed.diff`, and its diff is −7 lines in `Group.lean` only.
  - `Group.lean` at the group head has SHA-256 `59c605e1…6213` and 331 lines, which is the pin.
- **Insertion checks against the tip** (`176cfd4a`; phase 1's `insertion_check.py`; `landing/insertion-check-vs-tip.txt`):
  - **PASS** for `Probability` (anchors 48 and 403; the head and `~1` both pass), `Games.lean` (9 and 42),
    `Group.lean` at `~1` (62 and 232), and `Group.lean` at the LE-grp1 head (62 and 232).
  - The LE-grp1 head also passes its five controls (ALL_OK). Removing the blocks restores the tip byte for byte.
  - `Relational.lean` is absent at the tip.
- **Export check** (`landing/export-check.txt`):
  - The three Games files at the head equal the delivery's `src/games-relational/` byte for byte.
  - `Group.lean` at the head differs from `src/group-helpers/` by exactly the LE-grp1 lines, and `~1` equals `src/` byte for byte.
- **`natCast_inj_of_lt`:**
  - At the group head, no Lean or blueprint file names it (`git grep` rc 1 over `TCSlib`, `TCSlib.lean`, `audits` and
    `blueprint`), and neither does any Lean file at the games head.
  - The only hits are records Markdown, which is history: the decision-log rows, the issued brief and `review.md`.
  - The R2 probe confirms that no constant of that name exists in `Group`'s import closure (§ P2-5).
- **Signatures** (`landing/signatures.txt`, `tools/sigkey.py`):
  - All four landing commits carry an SSHSIG with key `SHA256:32dP45eSMmVSt/G/CGvcxl/P+MO3Nwj9xeTh/GSA2wc`. That is the key
    of the records commits `176cfd4a` and `7486e401`.
  - The series commits are unsigned.
  - This is key identity only, not a cryptographic check (BS-F12).

## P2-2 Replay R1, the Games PR
- **Recipe:**
  - `cp -al $SP/olean-snapshot $SP/olean-replay-bb1sim-games`.
  - The overlay (`mloverlay.sh`: 3346 symlinks) and `mathlibextra.sh` NthRootLemmas, whose olean is `c0a9cff0…`.
  - `stateplan init`: 1421 modules at `a6d01b1b`.
  - `downorder.py`: changed 3, down 181.
  - `fullorder.py`: 1422 modules, the roots being `TCSlib` and both Checks.
  - `stateplan plan`: **181 to build, 1241 reused**.
  - The worktree is a `git archive` export of `dfacac35`. `exportcheck.py` gives 1574/1574 blobs, 0/0/0.
- **The queue equals `landing/down-games-pr-merged.txt` as a set** (181).
  - It is `Probability` and its downstream: the 150 modules of the issued DOWN-PROBABILITY and the 27 `Yao/HybridProof` modules.
  - It also has `Relational`, root `TCSlib`, **`audits/pass-shelat/Checks` and `audits/garg-ch1-3/Checks`** (BS-F04 and
    BS-F05 are closed).
- **Build** (`runner.py` through `scripts/lean_check_tree.sh`, 01:58:26–02:16:44, 1099 s of module time, max RSS 4.4 GB):
  - **181/181 rc 0.** `error:` 0, `error(` 0, the substring "error" 0, and there were no log/record mismatches (`permod.py`).
  - 17 warnings, of which 6 are `sorry`.
- **Accept:**
  - `stateplan update` took 181 modules, and `check` over the full order gives **1422/1422 OK, RESULT OK**. It held again
    at the end.
  - **All 181 rebuilt oleans have link count 1**, with object hash equal to the record. The other 1272 files stay hard links.
- **Warnings** (`r1-games/checks/warnings-vs-snapshot-build.tsv`): **181/181 SAME.**
  - Each module's warning lines equal the log of a build of the same source:
    - 173 against the snapshot's own build logs (advance 33, rebase 140);
    - 5 unchanged `Games/*` modules against the worker's bootstrap at `bdcadd85` (same source; snapshot #0 reused them,
      so the rebase evidence has no log);
    - `Probability`, `Relational` and the facade against the worker's series-1 head sweep (same source).
  - **`Relational` has exactly 2 `sorry` warnings**, at 85:8 (`expect_simulate_rel`) and 124:8 (`expect_sample_rel`).
  - `Probability` has 0.
- **Admissions** (`admissions/r1-delta.txt`, `admdelta.py`): against the tip, **+2**. Both are `Relational`, the two
  targets, and every other rebuilt module has delta 0. The source token census agrees: the tip has 792 `sorry`/`admit`
  tokens in 76 files, and the games head 794 in 77, the only change being `Relational.lean` +2.
- **Name resolution, BS-F03** (`probes/games/runs/mods/Bb1sProbe_ResolveGames.log`, attempt 2):
  - `Forgery` rebuilt with rc 0 and no warnings.
  - The value of `ETTGame.abs_ettAcc_rej_sub_le`, the theorem that calls the averaging bound at `Forgery.lean:545`, uses
    exactly one `*abs_expect_sub_le_expect`: `_private.…Forgery.0.…ETTGame.abs_expect_sub_le_expect`, the private
    copy, not the public lemma.
  - The import closure holds exactly two declarations of the name: that private copy and
    `TCSlib.Cryptography.Games.ProbComp.abs_expect_sub_le_expect`.
  - The two types are alpha-equivalent (`==`), and the binders are `c f g h hb`. Only the type binder is named
    differently, `α` against `β`.
  - With `open TCSlib.Cryptography.Games ProbComp`, `resolveGlobalConst` gives exactly one constant, the public lemma,
    and the no-overload form gives no ambiguity error.
  - Inside `namespace …ETTGame` with Forgery's own `open` line, the bare name resolves to the public lemma only. Outside
    `Forgery.lean` the private copy is invisible, which is the situation after the Stage 2 deletion.
  - Forgery's call shape `abs_expect_sub_le_expect (h := h) c hb` elaborates there.
  - BS-F03 is closed: the re-point is safe.

## P2-3 Axioms (R1; probe importing the facade `TCSlib.Cryptography.Games`)
- **`#print axioms`:**
  - `abs_expect_sub_le_expect` uses `[propext, Classical.choice, Quot.sound]`.
  - `expect_simulate_rel`, `prob_simulate_rel` and `expect_sample_rel` use those plus `sorryAx`.
- **Census:**
  - `Probability` has 57 stored constants, with 0 non-standard axioms.
  - `Relational` has 3, all with `sorryAx` (the three lemmas).
  - Together that is **60 constants, non-standard only in those three**, as the worker found.
- **Trace:**
  - `expect_simulate_rel` reaches only itself (closure 5009), and `expect_sample_rel` reaches only itself (5364).
  - `prob_simulate_rel` reaches exactly `expect_simulate_rel` (5012).
  - `abs_expect_sub_le_expect` reaches none (10759).
- The StmtDump types equal the delivered headers.

## P2-4 Rule 10 on R1
- **Method:**
  - The worker's `rule10_stmt.sh`, adapted to `tools/rule10_bb1s.sh`: an export worktree, the R1 output as the tree,
    and `touched.json` against the tip.
  - The archived Gate 06/10 harness.
  - Whole-file probes with `-DmaxErrors=0`, with install and EOF records.
- **Seals.** The table gives the requests per variant (strict A / strict B / coe A / coe B), with the base taken at the
  tip from the snapshot (see "Base seals" below):

  | Owner | Head | Base (tip) | Errors |
  |---|---|---|---|
  | `Probability` | 36/36/35/35 | 36/36/35/35 | coe A/B 0; strict A/B 1 each, `ProbComp.dist_apply` |
  | `Relational` | 53/53/52/52 | new file | 0 in all four |

  - The strict `dist_apply` failure is identical at the tip, so it is **pre-existing (BS-F06, DW-10/Stage 2), not new**.
  - The request name sets of `Probability` equal the tip's in all four variants, and the sealsum rows are identical.
  - Strict A minus coe A is exactly `FinDist.instCoeFunForallReal`, for both owners.
  - Every probe has install and EOF records.
- **Controls** (`mkctl_bb1s.py`, the covering subset; 8 probes per harness):
  - 6 sealed negatives per harness (the `expect` and `AllOutputs` rows), each failing exactly once.
  - 0 positives fail, and the unsealed probes give 0 errors.
  - **ALL_OK in strict and in coe.**
- **Explicit-unfold scan** of `Games.lean`, `Probability.lean` and `Relational.lean`: 101 items (85 THEOREM,
  14 LOCAL_OR_UNRESOLVED, 2 OWNED_DEFINITION), **0 foreign**.
- **Base seals** (`rule10/base`): at the tip, from a `cp -al` copy of the snapshot plus the overlay. It was read only by
  the probes and deleted afterwards.
  - `Probability` 36/36/35/35, with the same `dist_apply` failure in strict A/B.
  - `Group` 567/568/567/568, 0 errors.
  - `Assumptions` 644/645/643/644, 0 errors.

## P2-5 Replay R2, the group PR (LE-grp1 applied)
- **Recipe** as for R1: `$SP/olean-replay-bb1sim-group`, export `92dea4f8` (1573/1573 blobs, 0/0/0), and its own
  NthRootLemmas (`c0a9cff0…`).
  - The plan is **12 to build, 1409 reused**, exactly `landing/closures.txt`'s 12, because #346 has not merged.
  - Those 12 are `Group`, `Assumptions`, `Operations`, the `Pairing` facade, `Joux`, the `KeyExchange` facade,
    `BonehBoyen`, `BonehBoyenMachine`, `BonehBoyenSecurity`, the `IdentityBased` and `AdvancedEncryption` facades, and
    root `TCSlib`.
- **Build** (02:39:32–02:40:01): **12/12 rc 0**, with 0/0 errors.
  - The state check gives **1421/1421 OK**, and it held again at the end.
  - **All 12 rebuilt oleans have link count 1.**
  - Warnings: 11 SAME and `Group` NEWSRC with 0.
  - The `sorry` warnings are unchanged: `Assumptions` 1, `BonehBoyenMachine` 1 and `BonehBoyenSecurity` 2.
  - **Admissions delta 0** against the tip, and the source census is 792 = 792.
- **Axioms** (`probes/group`):
  - `pow_val_add`, `pow_val_neg` and `pow_val_bijective_of_ne_one` use `[propext, Classical.choice, Quot.sound]`.
  - The **`Group` census is 82 constants with 0 non-standard**. That is the worker's 83 minus `natCast_inj_of_lt`.
  - `natCast_inj_of_lt` is absent, and no constant `*natCast_inj_of_lt` exists in the closure.
- **Seals** (requests: strict A / strict B / coe A / coe B):

  | Owner | Requests | Errors |
  |---|---|---|
  | `Group` | 567/568/567/568 | 0 |
  | Carrier `Assumptions` | 644/645/643/644 | 0 |

  - **The request name sets equal the tip's** in all eight owner and variant pairs. LE-grp1 removes a theorem and
    changes no request.
  - Strict A minus coe A: `Group` none, `Assumptions` `FinDist.instCoeFunForallReal`.
  - Every probe has install and EOF records.
- **Controls:** **34/34 sealed negatives per harness**. The breakdown is `Assumptions` 12 (A) and 13 (B), and `Group`
  4 (A) and 5 (B).
  - Each fails exactly once, 0 positives fail, and the unsealed probes give 0 errors.
  - **ALL_OK in strict and in coe.**
- **Scan** of `Group.lean`: 56 items (41 THEOREM, 15 LOCAL_OR_UNRESOLVED), **0 foreign**. The worker's 59 included the
  dropped helper.

## P2-6 Lint (tip against each head; each run from its own export; `lint/`)
- **`campaign_style_lint.py TCSlib/Cryptography --check8b`:**
  - The tip gives 92 FAIL / 104 WARN over 518 files.
  - The games head gives 92 / 104 over 519, and the group head 92 / 104 over 518.
  - **The FAIL/WARN line sets are identical** to the tip's. Only the INFO size lines of the changed files change
    (`Games.lean` 64→67, `Probability` 409→423, `Relational` new at 134, `Group` 304→331).
  - Phase 1's 92/103 over 450 was at the issue base.
- **`style_lint.py`** on the 4 changed files: 0 findings.
- **`sk15`:** none at either head (or at the tip).

## P2-7 Cross-build (recommended; done)
- **Tree.** `git` 2.43's `merge-tree --write-tree` takes commits only, so the four-way tree was formed as follows
  (`p2-7/merge-trees.txt`):
  - `merge-tree 176cfd4a × 89a18a82` gives `ca0fad79`, Lean-equal to phase 1's `ac9e7958`.
  - `merge-tree` of the two landing heads gives `31c1b497`.
  - A 3-way `read-tree -m 176cfd4a ca0fad79 31c1b497` into a temporary index gives 0 unmerged entries. `write-tree`
    then gives **`66fdaf9566a6bd6c1a3786fe8e796ee3c26d4d0d`**.
  - Without LE-grp1 the same steps give `752fb43c`, which is Lean-equal to phase 1's `21c1aa45`.
  - `66fdaf95` differs from `21c1aa45` only by LE-grp1 (−7 lines).
- **Build.** The cross-build ran in a further `cp -al` of the R1 output, with R1's checked state.
  - The plan rebuilt only **18 modules**, the #346 closure and the `Group` closure, with 1409 reused.
  - **18/18 rc 0** and 0/0 errors.
  - The state check gives **1427/1427 OK**, and all 18 rebuilt oleans have link count 1.
- **Admissions against the tip:**
  - **−1** at `BonehBoyenMachine` (T4, #346).
  - **+2** at `Relational`, carried in the reused R1 olean.
  - The net is **+1**, as expected; the source census is 792 → 793.
- **Trace:**
  - `bb1_sidSecure` reaches exactly `bb1_sim_random` and `bb1_sim_real`.
  - `exists_bb1_distinguisher` reaches none.
  - The three `Relational` traces are as in P2-3, and `pow_val_bijective_of_ne_one` reaches none.
- The output and its export were **discarded** after their evidence was recorded, and the snapshot then rehashed 0/0/0.

## P2-8 Merge order and adoption (for the maintainer; nothing merged here)
1. **Merge the Games PR first.** It has the largest rebuild, 181 modules.
   - On merge, run `git diff --name-only <merge> c6d3bed311a83f217428576b08065b5743003ec1 -- '*.lean' lean-toolchain
     lake-manifest.json`. The tree `c6d3bed3` is Lean-equal to `merge-tree f472accd × dfacac35` = `787cd003`.
   - If the diff is empty, adopt `$SP/olean-replay-bb1sim-games` (recipe step 6), and add `snapshots.md` row #3.
2. **Then re-replay #346 and the group PR on the new snapshot.**
   - `BonehBoyen*` lies in both `Probability`'s downstream and theirs, so their current replay outputs
     (`olean-replay-346`, `olean-replay-bb1sim-group`) will not be adoptable after the Games merge. Their prospective trees
     change in the Games files.
   - Each re-replay rebuilds only its own closure: 12 modules for the group PR, or 17 if #346 has merged.
   - Expect the same results. P2-7 already built all four together with rc 0.
3. Cleanup Stage 1's `Games.lean` insertions merge cleanly with series 1 (phase 1, BS-F09).

## Findings (phase 2)
| # | Severity | Finding | Disposition |
|---|---|---|---|
| BS-F03 | info, closed | Resolution probe: the Forgery call uses the private copy now. After the Stage 2 deletion the bare name resolves to the public lemma uniquely, with alpha-equivalent types and the same value binders. | None. |
| BS-F04, BS-F05 | info, closed | Both `audits/*/Checks` and the 27 `Yao/HybridProof` modules rebuilt rc 0 at the merged tree (R1, 181 modules). | Fix the pack template (BS-F04) at the next issue. |
| BS-F06 | info, pre-existing (reconfirmed) | Strict A/B of `Probability` fail once at `ProbComp.dist_apply`, identically at the tip (request sets equal). Coe passes. | DW-10 / Stage 2. Not new. |
| BS-F11 | info | The cherry-picked commit `2cca41bc` keeps the worker's message: "four proved helpers … and `natCast_inj_of_lt` … Mathlib states none of them in a directly usable form". LE-grp1 (`92dea4f8`) in the same PR removes that helper, the message's claim is wrong for it (BS-F01), and the range-diff requires verbatim messages. | State it in the group PR body: "LE-grp1 drops the fourth helper (BS-F01); Mathlib's `CharP.natCast_injOn_Iio` is used instead". No rewrite. |
| BS-F12 | info, process | Trailers and signatures.<br>• The two Games picks and the group pick carry the worker session's `Claude-Session` trailer (`…VTjgrz…`) and no maintainer trailer. LE-grp1 carries this session's (`…VTiuDcj…`). This is consistent with #346's landed picks.<br>• All four commits are SSH-signed with the records key `SHA256:32dP45eS…` (BS-F08: an account-wide platform key).<br>• `ssh-keygen` is not installed and the configured `.pub` is empty, so the signatures were identified by key, not verified. | None. GitHub's verification on push is the check. |
| BS-F13 | info, my evidence | My first `ResolveGames` probe failed at elaboration (5 errors): it called `ConstantInfo.getUsedConstants`, which this Lean lacks. Attempt 2 uses `getUsedConstantsAsSet`, as the axioms probe does, and passes. Attempt 1 is kept (`probes/games/attempt1/`). | None. This is a defect of the probe, not of the module. |

## Replay outputs (kept; they become snapshots on merge)
- **`$SP/olean-replay-bb1sim-games`** (R1, REV `dfacac35`, prospective tree `c6d3bed3`):
  - 1454 files: 1453 TCSlib/audits/PFR oleans plus NthRootLemmas, and 3346 Mathlib overlay symlinks.
  - 181 rebuilt oleans, each with link count 1; the rest are hard links to the snapshot.
  - The state check over the full closure (1422) is OK.
  - Remove `Mathlib/` at adoption.
- **`$SP/olean-replay-bb1sim-group`** (R2, REV `92dea4f8`, tree `863b2926`):
  - 1453 files and 3346 symlinks.
  - 12 rebuilt oleans with link count 1.
  - The state check over 1421 is OK.
  - Adoptable only if it merges before the Games PR; otherwise re-replay (P2-8).
- **Disk:** 7530 MB free at the start, 6948 MB at the lowest point and about 6989 MB at the end. The export worktrees
  (`$SP/bb1p2/wt-*`) are scratch and can be deleted.

**Phase 2 done: both landing branches pass and are ready for their draft PRs. Order: Games PR first, then re-replay the
group PR (12 modules) before it merges.**

## ===== briefs/pairings/fills/bb1-sim/statements-final-r1/phase2b-352.md (records, at ab17e37feb00a677d69f6abd5ff7e427e3b9ef3c) =====

# bb1-sim-statements · phase 2b: #352 re-replay on olean snapshot #3

**Verdict: PASS. #352 (`land/bb1-sim-group`, head `92dea4f8126747ea7e816984349b9dbb789f0065`) is clear to merge.**
- The replay rebuilt 12 modules. Each has rc 0 with 0 `error:` and 0 `error(`.
- The state check gives 1422/1422 OK, and all 12 rebuilt oleans have link count 1.
- Snapshot #3 rehashes 0/0/0 before, during and after the replay.
- Admissions against the tip are +0.
- The three helpers use only the standard axioms. The `Group` census is 82 constants, 0 non-standard.
- Rule 10:
  - The seals (strict and coe, A and B) give 0 errors on `Pairing/Group` and on the carrier `Assumptions`.
  - The controls are ALL_OK in both harnesses, and the explicit-unfold scan finds 0 foreign items.
  - Every seal probe, control probe, sealsum row and control verdict is byte-identical to phase 2's R2 (§ R2b-4).
- Lint is unchanged against the tip.

Run on 2026-11-17, 03:04–03:23 UTC. `$SP` is `/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`.
- **Evidence:** `bb1-sim-statements-r1-phase2b-evidence.zip`, under `bb1-sim-statements-r1-phase2b/`. It has
  `PROVENANCE.txt`, `SHA256SUMS` and this file, and its own SHA-256 is in `evidence-SHA256SUMS`.
- **Not done:** nothing was committed, pushed or `git add`ed, and no PR was touched.
- **Builds:** there was no `lake build` and no cache get. This job ran one Lean process at a time.
- **#346's job:** its directories (`$SP/p346`, `$SP/olean-replay-346`, `$SP/olean-replay-346b`) and processes were not
  touched.

## R2b-0 Inputs
- **Records tip** (`git fetch`; `origin/cryptography/pass-shelat-ch2-4` = `HEAD`):
  `c0752b2e6442ca4985644195acc5d25cf83d85d0`.
  - Its Lean paths equal snapshot #3's T `cf7d28f7159b46033e8b8ae170954f9575e5d145`, the #351 merge. `git diff` over
    `*.lean`, `lean-toolchain`, `lake-manifest.json`, `lakefile.lean` and `scripts` lists nothing.
- **REV** = `git merge-tree --write-tree origin/cryptography/pass-shelat-ch2-4 92dea4f8…` =
  **`3029d8c36c00fd3a4ce27e864a2b43b46309d27f`**. The merge is clean (rc 0, no conflicts).
  - `git diff c0752b2e 3029d8c3`, over all paths, is exactly `TCSlib/Cryptography/Pairing/Group.lean | 27 +`.
  - That is the three helpers (`pow_val_add`, `pow_val_neg`, `pow_val_bijective_of_ne_one`) and their three docstring
    lines.
  - `Group.lean` at REV is blob `54e63b26`, the same blob as at the head. It has SHA-256 `59c605e1…6213` and 331 lines,
    which is phase 2's pin.
- **Snapshot #3:** `$SP/olean-snapshot`.
  - Map `olean-snapshot.map-cf7d28f7.tsv` has SHA-256 `e9dfbfdd…a53d`.
  - Files manifest `olean-snapshot.files-cf7d28f7.txt` has SHA-256 `1e9a3ba7…5733`.
- **Tools:**
  - `olean-rebase-evidence.zip` (SHA-256 `b662b7da…37ae`) → `olean-advance-a6d01b1b/tools-used/`, extracted into a fresh
    directory. It is identical to `$SP/snaptools3`.
  - The seal tools are phase 2's `tools/seal`, byte-identical, with the worker's `rule10_b.sh` and `mkctl_bb1s.py`.
  - The new scripts are `run-build.sh` and `rule10_352.sh`. They are phase 2's scripts with this job's paths, REV and tip.

## R2b-1 Replay (snapshots.md job recipe)
- **Export:** `git archive` of REV, restricted to `TCSlib`, `TCSlib.lean`, `audits`, `scripts`, `lakefile.lean`,
  `lean-toolchain` and `lake-manifest.json`, with `.lake/packages` symlinked.
  - `exportcheck.py` gives 1574/1574 blobs, 0/0/0.
- **Copy and overlay:**
  - `cp -al $SP/olean-snapshot $SP/olean-replay-352`.
  - `mloverlay.sh` made 3346 symlinks.
  - `mathlibextra.sh` built NthRootLemmas with rc 0, and its olean is **`c0a9cff0…`**.
- **Plan:**
  - `stateplan init` at `cf7d28f7` gives 1422 modules.
  - `downorder.py` gives changed 1 (`Group`) and down 12.
  - `fullorder.py` gives 1422 modules, the roots being `TCSlib`, `audits/garg-ch1-3/Checks` and `audits/pass-shelat/Checks`.
  - `stateplan plan` gives **12 to build and 1410 reused**.
  - **The queue equals `down.txt` as a set, and equals R2's `plan/queue.txt` byte for byte.** Those 12 are:
    - `Group`, `Assumptions`, `Operations` and the `Pairing` facade;
    - `Joux` and the `KeyExchange` facade;
    - `BonehBoyen`, `BonehBoyenMachine` and `BonehBoyenSecurity`;
    - the `IdentityBased` and `AdvancedEncryption` facades;
    - root `TCSlib`.
  - Neither `audits/*/Checks` is in `Group`'s downstream, as in R2.
- **Build** (`runner.py` through `scripts/lean_check_tree.sh`, `TCSLIB_OLEANS=$SP/olean-replay-352`, 03:07:14–03:07:45):
  - **12/12 rc 0.** `error:` 0, `error(` 0, the substring "error" 0, and there were no log/record mismatches (`permod.py`).
  - There are 4 warnings, all `sorry`: `Assumptions` 1, `BonehBoyenMachine` 1 and `BonehBoyenSecurity` 2.

## R2b-2 Accept (recipe step 5)
- `stateplan update` took 12 modules, with none left out.
- `check` over the full order gives **1422/1422 OK, RESULT OK**. It held again at the end.
- **All 12 rebuilt oleans have link count 1**, with object hash equal to the record. The other 1441 files are hard links
  to the snapshot.
- **Snapshot #3** `snapmap.py verify` gives **0 extra / 0 changed / 0 missing**, with no symlinks and 1453 files. It ran
  before the copy, after the build and at the end.
- **Warnings** (`warncmp.py`): **12/12 SAME** as a build log of the same source.
  - 10 match phase 2 R1, which is snapshot #3's own build.
  - `Group` and `Operations` match R2.

## R2b-3 Admissions and axioms
- **Admissions** (`admdelta.py` against the tip): **+0**. Every rebuilt module has delta 0.
  - `Group` has no tip build record in these baselines. Its head count is 0.
- **Source census** (`git grep -c -w -E 'sorry|admit'` over `TCSlib`, `TCSlib.lean` and `audits`): the tip has 794
  tokens in 77 files, and REV has the same.
  - The per-file lists are identical.
  - The same method reproduces phase 2's 792 at `176cfd4a` byte for byte. The +2 since then is `Relational`, from #351.
- **Axioms** (phase 2's `AxiomsGroup` probe, unchanged, run against the replay):
  - `pow_val_add`, `pow_val_neg` and `pow_val_bijective_of_ne_one` use **`[propext, Classical.choice, Quot.sound]`**.
  - The `Group` census is **82 constants with 0 non-standard**.
  - `natCast_inj_of_lt` is absent, and no `*natCast_inj_of_lt` constant exists in the closure.
  - The probe log is byte-identical to R2's.

## R2b-4 Rule 10 (`rule10_352.sh`: touched, collect, seals, scan)
- **Method:**
  - `touched.json` is computed against the tip `c0752b2e`: 3 ADDED and 39 UNCHANGED, identical to R2.
  - The collector log is byte-identical to R2's.
  - All four variants were run in full: strict A/B and coe A/B, each with paired controls.
- **Seals** (requests: strict A / strict B / coe A / coe B):

  | Owner | Requests | rc | Errors | Install / EOF records |
  |---|---|---|---|---|
  | `Pairing/Group` | 567/568/567/568 | 0 | 0 | present in all four |
  | Carrier `Assumptions` | 644/645/643/644 | 0 | 0 | present in all four |

  - **The request name sets equal both R2's and the phase-2 base's** (`176cfd4a`) in all eight owner and variant pairs.
  - Strict A minus coe A: `Group` none, `Assumptions` `FinDist.instCoeFunForallReal`.
- **Controls:** **34 sealed negatives per harness**. The breakdown is `Assumptions` 12 (A) and 13 (B), and `Group` 4 (A)
  and 5 (B).
  - The 8 sealed control probes fail with rc 1 and exactly the expected errors.
  - The 8 unsealed probes give rc 0 with 0 errors, and 0 positives fail.
  - **ALL_OK in strict and in coe.**
- **Explicit-unfold scan** of `Group.lean`: 56 items (41 THEOREM, 15 LOCAL_OR_UNRESOLVED), **0 foreign**.
- **Identity with R2** (`comparisons-vs-r2.txt`). The following are byte-identical to R2:
  - all 8 seal probe sources and all 16 control sources;
  - the four sealsum TSVs and both `ctlcheck` logs;
  - the scan `items-head.json` and `explicit-head.json`.

  The request sets are therefore provably identical to R2's. All variants were run anyway.

## R2b-5 Lint (tip against REV, each from its own export)
- **`campaign_style_lint.py TCSlib/Cryptography --check8b`:** both give 92 FAIL / 104 WARN over 519 files, and the
  **FAIL/WARN line sets are identical**.
  - The only changed line is `Group.lean`'s INFO size line, which goes from 304 lines and 24 public declarations to 331 and 27.
- **`style_lint.py Group.lean`:** 0 findings.
- **`sk15`:** none at REV or at the tip.

## Replay output (kept)
- **`$SP/olean-replay-352`** (REV `3029d8c36c00fd3a4ce27e864a2b43b46309d27f`):
  - 1453 TCSlib/audits/PFR oleans, of which 12 were rebuilt with link count 1 and the rest are hard links to snapshot #3.
  - It also holds the `Mathlib/` overlay (3346 symlinks plus the NthRootLemmas olean).
  - The state check over the full closure (1422) is OK.
  - Disk: 6993 MB free at the start, 6767 MB at the end.
- **Adopt on merge** (recipe step 6) if `git diff --name-only <merge> 3029d8c36c00fd3a4ce27e864a2b43b46309d27f --
  '*.lean' lean-toolchain lake-manifest.json` is empty.
  - That holds if #352 merges onto a branch whose Lean still equals `cf7d28f7`.
  - If #346 merges first, the replay is not adoptable, because `BonehBoyenMachine` is shared downstream. Re-replay
    instead, which costs about 17 modules.
  - Remove `Mathlib/` at adoption.
- The export worktrees `$SP/bb1p2b/wt-rev` and `wt-tip` are scratch and can be deleted.

**Clear to merge**

## ===== briefs/pairings/fixes/group-dedup/report.md (records, at ab17e37feb00a677d69f6abd5ff7e427e3b9ef3c) =====

# DW-11 follow-up · `Pairing/Group.lean`: one generic prime-order bijectivity lemma; reuse Mathlib

Filed by the maintainer from the job's returned report (the harness refuses report-file writes by sub-jobs). The full
logs, tools and diffs are in `group-dedup-evidence.zip` (`48d787d4dd9943be620620f1924c755e31162dcc05c5684a579a479502b88f9c`,
308 files with inner SHA256SUMS; `README.txt` maps the folders).

**Verdict: PASS, pushed, draft PR #365** (`fix/pairing-group-dedup` → `cryptography/pass-shelat-ch2-4`), two signed
commits on records tip `5aed99076d2bd4e5d6f831aed88739fc3ce475b6` (Lean = TS2 `13fc8060`).

| Commit | Hash | Tree | Diff | Content |
|---|---|---|---|---|
| 1 | `6fc5f49456507dab5901045356ea40acf42bdd67` | `ba10f0a2…` | +25/−17 | new generic lemma; the two bijections re-proved from it; `pow_mod_card` in `pow_val_add`, `pow_val_mul` |
| 2 (head) | `5eaddd171bceccee917929e7f319ff9202994c59` | `9710ac7d…` | +3/−2 | `pow_mod_card … B.card_GT` in `pow_val_mul_GT`; one `## Main results` line |

**Lemma** (public, `TCSlib.Cryptography.Pairing`, before `namespace BilinearGroup`; Mathlib has no exact statement —
nearest `IsCyclic.unique_zpow_zmod`, `zmodCyclicMulEquiv`, `finEquivPowers`/`finEquivZPowers`, different shapes):

```lean
theorem pow_val_bijective_of_prime_card {M : Type*} [Group M] [Fintype M] {p : ℕ}
    [Fact p.Prime] (hM : Fintype.card M = p) {g : M} (hg : g ≠ 1) :
    Function.Bijective fun a : ZMod p => g ^ a.val
```
proved from `orderOf_eq_prime`, `pow_card_eq_one`, `pow_injOn_Iio_orderOf` and `Fintype.bijective_iff_injective_and_card`.

**Checks at the head:** decls2 1 ADDED / 0 / 0 (against `5aed9907` and `bfa1f5a4`); `touched.py` 1 ADDED + 5 CHANGED
(proof bodies only; all headers, statements and docstrings byte-identical apart from the new lemma and the one added
module-docstring line); no `Nat.mod_add_div` left. Replay on `$SP/olean-replay-grpfix` (`cp -al` of `olean-replay-cs1-s6`):
22/22 rc 0, 0 errors/sorry/warnings, state 1434/1434 OK, link count 1, parent and snapshot #6 rehash 0/0/0, output map
`286777672d4e61f1be0ba98fca72b01d8cd9aa281eb811d100d7fe499679c49c` (only `Pairing/Group.olean` differs from the parent).
Admissions 192 = 192 per module (census derived with `censusderive.py`; older record sets had been removed in a disk
clean-up). Axioms: 8 constants standard (new lemma, the 5 touched, `bb1_sidSecure`, `jouxKeyIndist_of_dbdhAssumption`);
no `sorryAx` user in any trace; Joux's closure shrinks 10,316 → 8,589. coe-A on `Group.lean`: 567 requests at base and
head, 0 errors, identical rows, byte-identical seal logs. Lint 92 FAIL / 103 WARN, nothing new; `style_lint` 0.

**Deviations:** one trial compile and one standalone probe before commit 1 (single processes, slot-gated); a failed base
axioms attempt with no toolchain file (no Lean ran; rerun passed); commit 2 at the maintainer's request.

**Adoption:** if #365 merges onto a tip whose Lean is still TS2's, `olean-replay-grpfix` is the replay at the merge tree
(step-3 diff against `5eaddd17` must be empty); otherwise re-replay (22 modules, ~100 s).

## ===== briefs/pairings/fills/bb1-sim/rulings.md (records, at ab17e37feb00a677d69f6abd5ff7e427e3b9ef3c) =====

# bb1-sim · Seyoon's rulings on design note r1 (2026-11-16)

These rule on the eleven questions of `design-r1.md` §5. Eight are as recommended; Q6, Q10 and Q11 are changed.

| # | Ruling | |
|---|---|---|
| Q1 | A **new module `Games/Relational.lean`**, imported by the `Games` facade. | as recommended |
| Q2 | The names are `Games.ProbComp.expect_simulate_rel`, `prob_simulate_rel` and `expect_sample_rel`, beside `ProbComp.expect_simulate_congr`. | as recommended |
| Q3 | The **inline expectation form** of the per-call hypothesis: from `R s t`, test functions that agree at equal answers and related states have equal expectations after one call. | as recommended |
| Q4 | The statement phase includes the companions `prob_simulate_rel` and `expect_sample_rel` with the target. | as recommended |
| Q5 | **No query budget now.** DL-40's cleanup either promotes the budgeted ETT lemmas `expect_simulate_abs(_inv)` as they are, or adds a budgeted relational variant when it is needed. | as recommended |
| Q6 | **Promote the averaging bound `\|𝔼 f − 𝔼 g\| ≤ 𝔼 h` into `Games/Probability.lean`**, as a public lemma beside the constant-bound `ProbComp.abs_expect_sub_le`. It is part of the statement phase, so expect a larger rebuild and re-seal. The private ETT copy (`EncryptThenTag/Forgery.lean:515`, DL-40) is re-pointed to it in the cleanup. | **changed** (was: public in `Relational.lean`) |
| Q7 | **One reader, `IBEScheme.sidImpl_eq_oracleImpl`,** in `Defs.lean` after T4's `_onSpec` readers. It is carried by the bb1-sim PR as a pure insertion, under an advance scope ruling confirmed by a probe first, which also fixes any needed `encCT` reader. | as recommended |
| Q8 | **One bb1-sim gate after Gate 44.** It covers the Games statement phase (`Relational.lean` and the `Probability.lean` addition), the reader insertions and the T2/T3 fill. | as recommended |
| Q9 | The Games statement phase is **its own small PR on the records tip**. The fill is stacked on T4's PR, or based on the tip once T4 merges. | as recommended |
| Q10 | **The group helpers go into the frozen `Pairing/Group.lean`** by an approved reader-style insertion beside the published `G_T` bijection: `Z_p ≃ G` for `g ≠ 1`, the additive exponent laws in `G`, and identity injectivity on good coins. Reuse Mathlib's `orderOf`/`ZMod` API where it applies. | **changed** (was: public helpers in the fill) |
| Q11 | **Ingest and cite [BGZ09] and [Sho04]** for the relational simulation lemma. Seyoon sends the PDFs. As with Gen09, nothing waits: the statements proceed, and the citations are a docstring-only follow-up after the ingest. No Lean docstring cites either tag before then. | **changed** (was: framework lemma, no tags) |

Next:
- the probe that fixes the reader set (after T4's readers land);
- the Games statement-phase PR (`Relational.lean` with the targets; the averaging bound in `Probability.lean`);
- the bb1-sim fill.

## Q7 follow-up: the reader set (Seyoon, 2026-11-17)

The probe (`bb1-sim-statements` checkpoint 1, exchange `8899115b`, `probe/READERS-TO-INSERT.md`) showed that T2 needs
**ten** readers, not the one Q7 anticipated:
- six in `IdentityBased/Defs.lean`: `sidImpl_zero_onSpec`, `sidImpl_two_onSpec`, `sidImpl_one_onQuery`,
  `sidImpl_two_onQuery`, `sidImpl_keyGen_ne_onSpec` and `sidImpl_challenge_fresh_onSpec`;
- four in `BonehBoyen.lean`: `bb1Scheme_setup_eq`, `bb1Scheme_keyGen_bind`, `bb1Scheme_enc_bind` and
  `ofFn_bb1Scheme_encCT`.

**Ruling: all ten are approved, and they land in the bb1-sim fill PR**, inserted verbatim from `READERS-TO-INSERT.md`
as pure insertions after the anchors it names. This is T4's pattern. The bb1-sim gate checks that they are insertions
only, against the pinned post-insertion SHA-256s (`Defs.lean` `97ecb6e0…`, `BonehBoyen.lean` `88454d6f…`, both on top of
T4's head). They are theorems proved by `rfl` or in one line; no definition changes.

**Design point:** the fill uses the probe's `RealReads` interface and the existential `setup_out` for the real setup's
outputs (design §3.3).

## ===== pr351-description.md (this pack) =====

This PR adds the Games-layer statements of the bb1-sim unit of the pairing campaign (`PairingCryptographyPlan.md`). Seyoon ruled the design in Q1–Q11 (`briefs/pairings/fills/bb1-sim/rulings.md`). Under Q9, this phase lands as its own small PR on the records tip.

**Head:** `dfacac356ff1225aca4c900d81bbf2cabce7b499`. The base is the records tip, and the diff is 3 files (+151/−0), all additions. There are two maintainer-signed cherry-picks of the worker's series: `912a343e` (`Probability.lean`) and `d742bf02` (`Relational.lean` and the facade).

## Changes
- **`Games/Relational.lean` (new, 134 lines):**
  - `expect_simulate_rel`: relational simulation of two handlers on state types σ and τ, related by `R`. Each call has the same answer law and preserves `R`.
  - `expect_sample_rel`: one-sample bijection.
  - Both are **targets (`sorry`)**, with design r1 §2.2's headers verbatim and proof sketches.
  - `prob_simulate_rel` is proved from the first target.
- **`Games/Probability.lean`:** `ProbComp.abs_expect_sub_le_expect`, `|𝔼f − 𝔼g| ≤ 𝔼h`. It is public and proved (Q6). The private ETT copy is re-pointed in cleanup Stage 2 (DL-40).
- **`Games.lean` facade:** one import and one `## Contents` entry.

## Checks
These were run by the maintainer on this head merged onto the tip, from the olean snapshot (`statements-final-r1/phase2.md`):
- **Build:** 181/181 modules rebuilt with rc 0, including the root and both `audits/*/Checks`. The state check gives 1422/1422.
- **Admissions:** +2, exactly the two targets.
- **Axioms:** `abs_expect_sub_le_expect` uses the standard three only. `prob_simulate_rel` reaches exactly `expect_simulate_rel`.
- **Rule 10:**
  - Seals: `Probability` 36/36/35/35 and `Relational` 53/53/52/52. The coe variants have 0 errors.
  - The single strict failure at `ProbComp.dist_apply` is pre-existing. It is the `FinDist` coercion, which is notation under DW-10 Q3.
  - Paired controls are ALL_OK, and the explicit-unfold scan finds 0 foreign unfolds.
- **Name resolution:** after Stage 2 deletes the private copy, the call at `Forgery.lean:545` resolves to this public lemma (probe in the evidence).
- **Lint:** the FAIL and WARN line sets are unchanged.
- **Cross-build:** this head together with #346 and the group-helper PR merges cleanly. The joint tree rebuilds with rc 0, and `bb1_sidSecure` reaches exactly T2 and T3.

## Review
- Phase 1 (static) and phase 2 (Lean) give the verdict **ACCEPT**, with 0 blockers, 0 majors and 0 minors open (`briefs/pairings/fills/bb1-sim/statements-final-r1/review.md`).
- Under Q8, the audit belongs to the single bb1-sim gate after Gate 44, which also covers the reader insertions and the T2/T3 fill.

**Merge order:** this PR merges before the group-helper PR because its rebuild is the largest. The maintainer then re-replays the group PR and #346 on the new tip.

---
_Generated by [Claude Code](https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA)_

## ===== pr352-description.md (this pack) =====

This PR adds the group helpers of the bb1-sim unit of the pairing campaign to `Pairing/Group.lean`. They follow ruling Q10 (`briefs/pairings/fills/bb1-sim/rulings.md`) and are used by the T2/T3 fill.

**Head:** `92dea4f8126747ea7e816984349b9dbb789f0065`. The base is the records tip; the only file changed is `Pairing/Group.lean` (+27/−0, all additions). The PR has two commits:
- `2cca41bc`, a maintainer-signed cherry-pick of the worker's `fc9cf2f5`;
- `92dea4f8`, landing edit **LE-grp1** (BS-F01, Seyoon 2026-11-17).

**LE-grp1** drops `natCast_inj_of_lt` and its docstring bullet. The helper is an iff wrapper of Mathlib's `CharP.natCast_injOn_Iio`, so the fill uses Mathlib directly. The first commit's message still lists that helper and says Mathlib states none of the helpers directly (BS-F11); the second commit supersedes it.

## Added (all proved, with formula docstrings)
- `BilinearGroup.pow_val_add`: exponents add in `Z_p`.
- `BilinearGroup.pow_val_neg`: negating an exponent inverts.
- `BilinearGroup.pow_val_bijective_of_ne_one`: `a ↦ g^a` is a bijection `Z_p → G` for `g ≠ 1`. Mathlib has a relative, `IsCyclic.unique_zpow_zmod`, indexed by `ZMod (Fintype.card α)`, so this is not a restatement (BS-F02).

## Checks (maintainer, on this head merged onto the tip, from the olean snapshot; `statements-final-r1/phase2.md`)
- **Build:** 12/12 modules rebuild with rc 0; the state check gives 1421/1421.
- **Admissions:** +0.
- **Axioms:** standard axioms only.
- **Rule 10:**
  - seals give 567/568/567/568 for `Group` and 644/645/643/644 for the control carrier `Assumptions`, with 0 errors;
  - paired controls are ALL_OK;
  - the explicit-unfold scan finds 0 foreign unfolds.
- **Lint:** the line sets are unchanged.
- **Cross-build:** this PR merges cleanly with #346 and the Games statement PR, and the joint build is clean.

## Review and merge order
- **Verdict:** the review gives **ACCEPT** (`briefs/pairings/fills/bb1-sim/statements-final-r1/review.md`).
- **Gate:** under Q8, the audit belongs to the bb1-sim gate.
- **Merge order:** this PR merges **after** the Games statement PR. Its downstream (`BonehBoyen*`) overlaps that PR's, so the maintainer re-replays these 12 modules on the new tip before merge (17 if #346 merges first).

---
_Generated by [Claude Code](https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA)_

## ===== pr365-description.md (this pack) =====

## Problem
This is the DW-11 ruling (Seyoon, 2026-11-17, `PairingCryptographyPlan.md`). It concerns `TCSlib/Cryptography/Pairing/Group.lean`:
- `BilinearGroup.pow_val_bijective_of_ne_one`, added by #352, restates the frozen `pow_val_bijective` on `G` instead of `G_T`. Its 7-line proof is a copy.
- Three proofs re-derive Mathlib's `pow_mod_card` with a `← Nat.mod_add_div … pow_order` chain: `pow_val_add` (#352), and the frozen `pow_val_mul` and `pow_val_mul_GT`.
- The injectivity step of both bijectivity lemmas (`pow_eq_pow_iff_modEq` + `Nat.ModEq.eq_of_lt_of_lt`) is Mathlib's `pow_injOn_Iio_orderOf`.

## Change
Two signed commits on `5aed99076d2bd4e5d6f831aed88739fc3ce475b6`. Together they change 1 file, +28/−19.

**Commit 1: `6fc5f49456507dab5901045356ea40acf42bdd67`** (+25/−17, proof-only)
- **One new public lemma**, placed before `namespace BilinearGroup`. It has a formula docstring, a glue/source note and a proof sketch:
  ```lean
  theorem TCSlib.Cryptography.Pairing.pow_val_bijective_of_prime_card {M : Type*} [Group M] [Fintype M] {p : ℕ}
      [Fact p.Prime] (hM : Fintype.card M = p) {g : M} (hg : g ≠ 1) :
      Function.Bijective fun a : ZMod p => g ^ a.val
  ```
  It is proved from Mathlib's `orderOf_eq_prime`, `pow_card_eq_one` and `pow_injOn_Iio_orderOf`, plus a cardinality argument.
  - Mathlib at `029db123` has no statement of this form. The closest is `IsCyclic.unique_zpow_zmod`, an `∃!` over `ZMod (Fintype.card α)` for a generator.
- `pow_val_bijective` and `pow_val_bijective_of_ne_one` are now one-line `exact`s of the new lemma, with `B.card_GT` and `pair_ne_one` for the first and `B.card_G` for the second.
- `pow_val_add` and `pow_val_mul` are now `rw [ZMod.val_add/val_mul, …, ← pow_mod_card x _, B.card_G]`.

**Commit 2: `5eaddd171bceccee917929e7f319ff9202994c59`** (+3/−2, at the maintainer's request)
- `pow_val_mul_GT`: the remaining `Nat.mod_add_div` chain becomes `rw [ZMod.val_mul, ← pow_mod_card y (a.val * b.val), B.card_GT]`. Only the proof body changed.
- The module docstring's `## Main results` gains one line for `pow_val_bijective_of_prime_card`. These are 2 added lines; nothing is removed.

**What did not change:** every existing statement, declaration header and declaration docstring. In the module docstring, only those 2 lines were added.
- decls2 against the tip: 1 ADDED, 0 CHANGED, 0 REMOVED.
- touched.py: 1 ADDED and exactly the 5 intended CHANGED.

## Checks
These are for the head `5eaddd17`. Commit 1's checks were run the same way and also passed.
- **Method:** one `lean` process at a time behind a host-slot gate, no `lake build`, no cache get. Replay on `olean-replay-grpfix`, a hard-linked copy of `olean-replay-cs1-s6` (TS2 `13fc8060`, Lean-equal to the base). The records tip has since moved to `bfa1f5a4` with records only; `merge-tree` is clean, and the merged Lean equals this head.
- **Replay:** the plan rebuilt 22 modules (`Group.lean` and its whole downstream) and reused 1412. All 22 gave rc 0, with 0 `error:`/`error(`, 0 sorry and 0 warnings.
  - The state check gives 1434/1434, RESULT OK.
  - The 22 rebuilt oleans have link count 1.
  - The parent tree rehashes 0/0/0 before, after and at the end, and snapshot #6 also gives 0/0/0.
  - Output map SHA-256 `28677767…`. Only `Pairing/Group`'s olean differs from the parent.
- **Admissions:** 192 at both base and head, equal module by module. The diff adds or removes 0 `sorry`/`admit`/`native_decide` tokens.
- **Axioms:** the new lemma, the 5 touched lemmas, `bb1_sidSecure` and `jouxKeyIndist_of_dbdhAssumption` use only `[propext, Classical.choice, Quot.sound]`.
  - The `#sorry_trace` of each traced constant has no direct `sorryAx` user.
  - All 83 constants of `Pairing.Group` are standard.
  - The sorry control is reported NONSTANDARD, as it should be.
- **Rule 10, canonical coe-A seal on `Group.lean`:** base and head both give 567 requests, rc 0 and 0 errors.
  - The request rows, `requested`, `term_names`, `term_readers` and `closure_modules` are equal, and the seal logs are byte-identical.
  - The new lemma refers to no TCSlib definition.
  - Requests did not change, so no consumer seal was needed.
- **Lint:** `campaign_style_lint --check8b TCSlib/Cryptography` gives 92 FAIL / 103 WARN at both base and head, with no new or removed lines. `style_lint` on `Group.lean` gives 0 findings.
- **Consumers** rebuilt cleanly: Pairing/*, KeyExchange/Joux and AdvancedEncryption/IdentityBased/* (BonehBoyen, BonehBoyenMachine/*, BonehBoyenSecurity/*).

Records: `briefs/pairings/fixes/group-dedup/report.md` and `group-dedup-evidence.zip`, which covers both commits.

Gate 49 (DW-11) audits this with #351 and #352.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA

## ===== verification-r1.zip:records/decision-log-pairings.md (this pack) =====

# Decision-log extract: PairingCryptographyPlan.md at b31b77f7f4127d9c6c6c0d6a1390de0dc8d71d43, lines 383-384, 421, 427-435, 448, 455, 464-467 (verbatim)

| Date | Decision / evidence | Status |
|---|---|---|
| 2026-11-16 | **bb1-sim design rulings complete (Seyoon)** (`briefs/pairings/fills/bb1-sim/rulings.md`). Q1–Q5, Q7–Q9 as recommended. **Changed:** Q6 promotes the averaging bound `\|𝔼f−𝔼g\| ≤ 𝔼h` into `Games/Probability.lean` (public, beside `ProbComp.abs_expect_sub_le`; the ETT copy re-points under DL-40); Q10 puts the group helpers (`Z_p ≃ G` for `g ≠ 1`, exponent laws, identity injectivity) into the frozen `Pairing/Group.lean` by approved insertion; Q11 ingests and cites [BGZ09] and [Sho04] (PDFs from Seyoon; the citations are a docstring-only follow-up, non-blocking, as with Gen09). Next: the reader probe after T4, the Games statement PR, then the fill and one bb1-sim gate. | bb1-sim ruled |
| 2026-11-17 | **bb1-sim statements: phase-1 review done** (`fills/bb1-sim/statements-final-r1/review.md`, evidence zip `6e4cbadd…`). Interim verdict **accept**: both series reproduce (`912a343e`→`d742bf02` Games; `fc9cf2f5` group), decls2 = the 8 expected ADDED, 0 CHANGED/REMOVED, admissions +2/+0, and all merges are clean (tip, #346, four-way `21c1aa45`). 0 blockers, 0 majors, 2 minors, 8 infos. **BS-F01** (`natCast_inj_of_lt` wraps Mathlib `CharP.natCast_injOn_Iio`) awaits Seyoon; landing edit LE-grp1 recommended. **BS-F08** confirmed by the maintainer: the worker's final exchange commit `a3cb45f6` is signed by the same key as the records commits (`SHA256:32dP45eS…`). Claude cloud sessions on this account share the platform's commit-signing key, so a signature attests a Claude session on the account, not the maintainer; provenance rests on the pinned hashes and maintainer cherry-picks. No worker change is needed. Phase 2 (merged-tree replays) is queued for the Lean slot after #346's check. | bb1-sim P1 |
| 2026-11-17 | **BS-F01 ruled (Seyoon): drop `natCast_inj_of_lt`.** Landing edit **LE-grp1** removes the helper and its docstring bullet from `Pairing/Group.lean` (−7 lines); the group-helper PR carries `fc9cf2f5` plus LE-grp1. The T2/T3 fill uses Mathlib's `CharP.natCast_injOn_Iio` directly. | BS-F01 |
| 2026-11-17 | **bb1-sim landing branches built** (local, maintainer-signed): `land/bb1-sim-games` `dfacac35` (tip `176cfd4a` + `912a343e`, `d742bf02`) and `land/bb1-sim-group` `92dea4f8` (tip + `fc9cf2f5` + LE-grp1). **Phase 2 started** on them (merged-tree replays from snapshot #2, seals, controls, cross-build with #346), concurrently with #346's phase 2 on disjoint directories. Scratch cleanup freed about 4 GB (clean, pushed worktrees of merged work only). | bb1-sim P2 |
| 2026-11-17 | **bb1-sim statements: phase 2 passed, final verdict ACCEPT** (`statements-final-r1/phase2.md`, zip `411338e9…`; 0 blockers/majors/minors, infos BS-F11–F13). Games head `dfacac35`: 181/181 rc 0, admissions +2, seals coe 0 errors. Group head `92dea4f8` (LE-grp1): 12/12 rc 0, +0, seals 0 errors. Cross-build with #346 is clean. **Draft PRs opened:** #351 (Games statements, merges first) and #352 (group helpers, re-replay after #351). Replays kept at `$SP/olean-replay-bb1sim-{games,group}`. | #351, #352 |
| 2026-11-17 | **#351 ruling (Seyoon): merge now, audit later.** #351 is marked ready on the maintainer review (phase 1 + 2 ACCEPT); the bb1-sim gate (Q8) still audits it after merge, and any finding is fixed by a follow-up PR. On merge: check the merge commit's Lean equals tree `c6d3bed3`, adopt `$SP/olean-replay-bb1sim-games` as snapshot #3, then re-replay #352 and #346 on the new tip. | #351 ready |
| 2026-11-17 | **#351 merged (Seyoon)** as `cf7d28f7`. Its Lean equals the replayed head (step-3 diff empty), so its replay was **adopted as olean snapshot #3** (map `e9dfbfdd…`, 1453 entries; basecheck OK; rehash 0/0/0; `maintainer/olean-snapshot-3-adopt/`). The group replay is discarded; #352 and #346 re-replay on #3. The bb1-sim gate still audits #351 (merge-now ruling). | #351 merged |
| 2026-11-17 | **#352 re-replayed on snapshot #3: PASS** (`statements-final-r1/phase2b-352.md`, zip `13483b25…`). Merge tree `3029d8c3` (tip + `Group.lean` +27): 12/12 rc 0, state 1422/1422, admissions +0, standard axioms, seals `Group` 567/568/567/568 and `Assumptions` 644/645/643/644 with 0 errors, controls ALL_OK, 0 foreign unfolds, lint unchanged; seal and control outputs byte-identical to the snapshot-#2 run. Replay kept at `$SP/olean-replay-352`, adoptable if #352 merges before #346. | #352 P2b |
| 2026-11-17 | **#352 ruling (Seyoon): merge now, audit later** (as for #351). Marked ready. Merging before #346 keeps `$SP/olean-replay-352` adoptable as snapshot #4 (merge Lean must equal tree `3029d8c3`); #346 then re-replays on #4. The bb1-sim gate still audits #352. | #352 ready |
| 2026-11-17 | **#352 merged (Seyoon)** as `463f2244`; its replay adopted as **olean snapshot #4** (map `6607620d…`; `maintainer/olean-snapshot-4-adopt/`). **Ruling (Seyoon): #351 and #352 are too small for separate gates;** they are audited later in one combined gate with other similarly small items (DW-11), not in the bb1-sim gate, which keeps the readers and the T2/T3 fill. #346 re-replays on #4. | #352 merged; DW-11 |
| 2026-11-17 | **Gate 44 round 2 dispatched (Seyoon)** to Codex cloud, pinned to exchange `2e015254`, records `4f4a7592`, #340 `916afc25`, #346 `98cb0e52` (LE-g44), T44′ `bee027f0`. Findings return in chat as `gate44-pairing-fills-r2-findings.md`. | G44 r2 out |
| 2026-11-17 | **Gate 48 (the bb1-sim gate, design ruling Q8) staged for Codex**, round 1, auditing #357 only at head `7a98ba01` with records pin `e6cdf4d4` (`gates/48-bb1-sim-fill/pack-r1.md`, `dispatch-r1.md`; exchange `82706564`, `outbox/gates/48-bb1-sim-fill-gate/`). #351/#352 are out of scope (DW-11). Merge-tree: #357 is clean with #347, #355 and the local 6a branches, with no shared path. **Merge-order note:** #355 extends `Games/Bridges/Experiments`, which #357's `Chain` imports, so whichever of #357 and #347+#355 merges second needs a re-replay before its snapshot can be adopted. Records slips found at staging: DL-57's line refs (`:78`/`:85` → `:77`/`:84`), and the ledger's DL-30–DL-57 rows, which had five cells under a four-column header; both fixed now (new header). `expect_sample_rel`'s docstring lacks a tag (it is #351's text, so it goes to DW-11). `rulings.md` Q8 is superseded by DW-11 for #351/#352. | G48 staged |
| 2026-11-17 | **#357 merged (Seyoon)** as `8060f6b7`. **Boneh–Boyen BB1 selective-ID security is complete on the records branch.** The merge's Lean equals `dfdc56f2` (step-3 diff empty), so `olean-replay-bb1sim-g48` (map `0858dccb…`) is adoptable as **olean snapshot #6**. Adoption waits until the running LE-g45 job finishes, because it rehashes snapshot #5. The other open replays (#347/#355 TS1, the 6a trees, #360) are built on #5 without #357, so each re-replays on #6 before its merge-time adoption; the audit evidence stands. | #357 merged |
| 2026-11-17 | **DW-11 (Gate 49) pre-dispatch sweep, ruling (Seyoon): fix now in a follow-up PR.** #352's `pow_val_bijective_of_ne_one` (`Pairing/Group.lean:252`) restates the frozen `pow_val_bijective` on `G` instead of `G_T`, with a 7-line proof clone. The review had noted a "generic prime-order lemma"; there was no ledger row or ruling (the G44-01 pattern). Inline re-derivations of Mathlib's `pow_mod_card`/`pow_mod_natCard` (in `pow_val_add`, and the frozen `pow_val_mul`) and `pow_injOn_Iio_orderOf` are in the same code. Fix: a small in-house PR adds one generic prime-order bijectivity lemma via Mathlib, re-proves both lemmas from it, and uses the Mathlib facts directly. It is proof-only, with statements and frozen headers unchanged. Gate 49 then audits #351, #352 and the fix PR together. Correction: #352 is the group-helper PR (`Group.lean` +27), not a reader follow-up. | DW-11 fix |
| 2026-11-17 | **DW-11 follow-up: draft PR #365** (`fix/pairing-group-dedup` `6fc5f494` on tip `5aed9907`). New public `pow_val_bijective_of_prime_card` (prime-order bijectivity, from Mathlib's `orderOf_eq_prime`/`pow_card_eq_one`/`pow_injOn_Iio_orderOf`; Mathlib has no exact statement). `pow_val_bijective` and `pow_val_bijective_of_ne_one` are re-proved from it; `pow_val_add` and `pow_val_mul` now use `pow_mod_card`. Proof-only, +25/−17. decls2 1/0/0. Replay of 22 modules on a copy of `olean-replay-cs1-s6`: rc 0, state 1434 OK. Admissions 192. Standard axioms, with empty traces for `bb1_sidSecure` and Joux. coe-A on Group: 567 requests, 0 errors, identical. Lint unchanged. A second commit (`pow_val_mul_GT` → `pow_mod_card`, plus a `## Main results` line) is in progress. Then Gate 49 stages #351, #352 and #365. | #365 |
| 2026-11-17 | **#365 commit 2** (`5eaddd17`): `pow_val_mul_GT` now uses `pow_mod_card`, so no `Nat.mod_add_div` chain is left; one `## Main results` line added. Re-checked on 22 modules: rc 0, state OK, map `28677767…`, admissions 192, 8 constants standard (Joux's closure 10,316 → 8,589), coe-A identical, lint unchanged (`fixes/group-dedup/report.md`, zip `48d787d4…`). Next: Gate 49 (DW-11) on #351, #352 and #365. | #365 c2 |

## ===== verification-r1.zip:records/duplication-ledger-DL40.md (this pack) =====

# Duplication-ledger extract (table header and DL-40): briefs/pass-shelat-ch5-8/duplication-ledger.md at b31b77f7f4127d9c6c6c0d6a1390de0dc8d71d43, lines 60-61, 72 (verbatim)

| Id | New declaration (where) | Existing copy (where) | Status | Resolution |
|---|---|---|---|---|
| DL-40 | cca2-ett fill (delivery review 2026-11-14): undisclosed `ETTGame.eval_toOracleAdversary_len` (`EncryptThenTag/Machines.lean`) generalizes public `PRFGame.eval_toOracleAdversary_width` (`OracleFromPRF/Reduction.lean`, its `ℓ = n` case); disclosed `ETTGame.zipWith_xor_cancel` = four private `zipWith_xor_xor_self` copies (`FromPRF`, `FromPRG`, `SpecialEncryption`, owned `zipWith_xor_xor_self'`; public relative `zipWith_xor_cancel_left`, other orientation); Gate 23 (G23-01, Seyoon 2026-11-14: debt now, fold in cleanup): private `length_le_length_encodeLog` (`EncryptThenTag/Machines.lean`) = the private copy in `NonMalleability/Indistinguishability/Forward.lean:108`; `ETTGame.prfAdv_eq_expect` re-derives private `prfAdv_prfReduction` (public relative `prfAdv_eq`, uprob form); generic forms `ETTGame.tapeImpl`/`simulate_tapeImpl_congr`/`expect_simulate_tapeImpl` (AdaptiveCPA), `recBits` family and `ovr` (PRFGame), `expect_simulate_abs` (`Games.simulate_eq_of_abs_bounded`), private `abs_expect_sub_le_expect` (`ProbComp.abs_expect_sub_le`). | `Foundations/BitLists`, `Pseudorandom/Functions`, `Games/*`, the general ETT forms | Open (deferred) | Promote the general forms (worker requested most) and re-derive the specialised copies from them; fold the private XOR copies; publish `length_le_length_encodeLog` in `Games/Efficiency/Strings.lean` beside `length_encodeLog_le` and delete both private copies (cleanup job). |

## ===== verification-r1.zip:records/deferred-work-DW11.md (this pack) =====

# Deferred-work extract (header and DW-11): briefs/pass-shelat-ch5-8/deferred-work.md at b31b77f7f4127d9c6c6c0d6a1390de0dc8d71d43, lines 7-8, 19 (verbatim)

| # | Item | Ruled | Source | Scope and starting point | Status |
|---|---|---|---|---|---|
| DW-11 | **Combined small-items gate** | Seyoon, 2026-11-17 | #351 and #352 (bb1-sim Games statements and group helpers) were merged on the maintainer review ("merge now, audit later") | One gate, later, auditing #351, #352 and any other similarly small merged changes together, instead of separate gates. #351 and #352 leave the bb1-sim gate (Q8), which keeps the reader insertions and the T2/T3 fill. Add further small items here as they arise. | Open (collecting: #351, #352) |

## ===== verification-r1.zip:records/cleanup-stages-stage2-rulings.md (this pack) =====

# Cleanup Stage 2 rulings extract: briefs/pass-shelat-ch5-8/cleanup-stages.md at b31b77f7f4127d9c6c6c0d6a1390de0dc8d71d43, lines 125-148 (verbatim)

## Stage 2 rulings (Seyoon, 2026-11-17; plan `cleanup-stage2/plan-r1.md`)
- **Q1 (changed): four jobs.** **S2-A in-house** (the maintainer): plan jobs J0 foundations + J1 Complexity hosts +
  J2 Asymptotic layer (~1,770 lines), merged first. Then **S2-B, S2-C, S2-D to Codex in a local checkout, in parallel**
  (file-disjoint): S2-B = J3 Pseudorandom/secure computation + J4 Encryption/authentication (~1,680); S2-C = J5 ZK graph
  isomorphism with the `GI`/`GIZK` shadow retirements (~1,500); S2-D = J6 ZK three-colouring with the
  `ColProofs`/`ColSimMachine` shadow retirements + J7 closer (`blocks` alias removal, ledger closure) (~1,480). One Codex
  gate per job; the Stage 2 gate (full seal sweep incl. seal B, combined statement-change list, ledger closure) rides
  with S2-D. Local-host Lean rule applies to the Codex jobs (at most 3 Lean processes on the machine across all jobs).
  Codex-local delivery per `workflow.md` worker routes: push the payload to `inbox/fills/<unit>/` on the exchange (or a
  ZIP in chat). Supersedes the stage plan's "one or two jobs" and Q13 (J1 is inside S2-A).
- **Q2:** the 51 statement-level seal-B-only fixes go in their owner jobs; each gate checks them one by one.
- **Q7:** the 14 duplicate public definitions get the promoted forms as their bodies, each checked by its gate.
- **Q8:** widen `Games.extTape` to `Type*`; keep `AdaptiveCPA.extTape` and `extendStream` as aliases (IBE uses the name);
  LazySampling imports `Games.Tapes`.
- **Q9:** shadow retirement by moving each canonical definition verbatim into a new lower module, restating the shadow
  lemmas over it, and deleting the shadows.
- **Q3–Q5, Q10–Q12, Q14, Q15 as recommended:** PS10 Tier A fixes in the owner jobs; apply all 21 Tier B advisories + the
  6 related notes; DW-11 (#351/#352) is dispatched now (J0 is no longer its third member, being inside S2-A); the seal-B
  ruling supersedes `lamport_oneTimeSecure`'s separate gate (DL-43); DL-38's six small folds, the five loops recorded as
  notes; the closer reconciles DL-1–DL-29 statuses; base after snapshot #7 and the 6a merges; `padTo` gets a `takeD`
  bridge reader (proof-only).
- **Q6 (changed): the lattice campaign is ours** (Seyoon: "any issues on the lattice side are also our responsibility").
  DL-54 (`reidx` move into `Combinators`) is done by us, after the 6a landing merges; it is tracked with the lattice
  campaign, not handed off.

## ===== verification-r1.zip:records/cleanup-stage2-plan-DW11.md (this pack) =====

# Stage 2 plan r1 extract (DW-11 rows and Q5): briefs/pass-shelat-ch5-8/cleanup-stage2/plan-r1.md at b31b77f7f4127d9c6c6c0d6a1390de0dc8d71d43, lines 296-302, 364, 399-403 (verbatim)

W6 retirement can be split out (W6-GI alone is about 700 lines) as a predecessor job on the same files.

### 2.3 Waves and merge order

1. **Wave 0.**
   - DW-11's gate is dispatched now (Q5).
   - J0 is in-house, on the tip after the snapshot-#7 adoption.
| **DW-11** (combined small gate: #351, #352) | #351 `Games/Probability.lean` (`ProbComp.abs_expect_sub_le_expect`), `Games/Relational.lean`; #352 `Pairing/Group.lean` | J0 adds `mul_prob_le_expect` to `Games/Probability.lean` and re-points `Pairing/Assumptions` (DL-55). J4 re-points the ETT averaging copy onto #351's lemma | DW-11 must clear before J0 merges and before J4 is issued (a DW-11 landing edit to `Games/Probability` would otherwise race J0 or J4). Recommended: fold J0 into DW-11 as its third member (Q5a). |
- **Q5. DW-11 timing.**
  - **(a) Recommended:** dispatch DW-11 now and add J0 to it as a third small member. J0 touches #351's file
    (`Games/Probability`) and is additive. J0 merges when DW-11 clears, and J4 is issued after that.
  - (b) Dispatch DW-11 now, separately; J0 gets its own small gate.
  - (c) DW-11 after Stage 2. Not recommended: J0 and J4 edit #351's file, and J4 re-points onto #351's lemma.

## ===== verification-r1.zip:records/snapshots-entries.md (this pack) =====

# Olean snapshot register extract: briefs/pass-shelat-ch5-8/maintainer/snapshots.md at b31b77f7f4127d9c6c6c0d6a1390de0dc8d71d43, lines 16-26 (verbatim)

## Entries

| # | T (records commit) | Map SHA-256 | Modules (files) | Date (UTC) | Status |
|---|---|---|---|---|---|
| 0 | `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9` (old base) | none: snapshot manifest `457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f` | 1199 (1230) | before 2026-11-16 | retired; manifest kept as `$SP/dl-oleans-2.snapshot-457ba704….txt` |
| 1 | `cd6070091380f2270568af850e3dda1081ca802e` | `73fac35ee25818653bdee00cf1a4d3b521ec1bdf4be4682109091502b7b57f84` | 1353 (1384) | 2026-11-16 23:42 | superseded; oleans deleted at adoption of #2; map and manifest kept |
| 2 | `a6d01b1bd1a92e2ac0be9999689467fea7e4e77b` (merge of #341) | `954934494925e1c32d2fca23fe3250e5ae838f63b57a71ff0ad54c7ff039c111` | 1421 (1452) | 2026-11-17 00:21 | superseded; oleans deleted at adoption of #3; map and manifest kept |
| 3 | `cf7d28f7159b46033e8b8ae170954f9575e5d145` (merge of #351) | `e9dfbfddfd6ca253f9fd5ee6c3efe868f8614083794312c89d32032564fea53d` | 1422 (1453) | 2026-11-17 03:02 | superseded; oleans deleted at adoption of #4; map and manifest kept; evidence `olean-snapshot-3-adopt/` |
| 4 | `463f224414ab7615e54104be353bfcda9dfceda7` (merge of #352) | `6607620d725049c90b34a51a2ab891f1520fd0f576aaf3f9d51301222cee41e7` | 1422 (1453) | 2026-11-17 | superseded; oleans deleted at adoption of #5; evidence `olean-snapshot-4-adopt/` |
| 5 | `3f540c22360c869069a0fba684e23ce6f3cb20db` (merges of #340, #346) | `fca1b6a308ac1585fb5897fae95e8294b54be55e160119e4eca1702692b41ef9` | 1427 (1458) | 2026-11-17 | superseded; oleans deleted at adoption of #6; map and manifest kept; evidence `olean-snapshot-5-adopt/` |
| 6 | `8060f6b767da9e43d1c1f6d32c55b97758b80bd8` (merge of #357) | `0858dccbee016da1da450f2b2ca0d1f5094ee42646b9496d5278f2b45cb07caf` | 1432 (1463) | 2026-11-17 | **current**; evidence `olean-snapshot-6-adopt/` |

## ===== verification-r1.zip:MANIFEST.md (this pack) =====

# verification-r1.zip · Gate 49 (DW-11: #351, #352, #365) round 1

Provenance of every entry. `SHA256SUMS` (this directory) lists every entry other than itself; verify with
`sha256sum -c SHA256SUMS` from a fresh extract. Nothing here was produced by a Lean run at staging: the evidence ZIPs are
the maintainer reviews' recorded evidence, copied byte for byte from the records; `checks/` are git-object reads made at
staging with the scripts in `checks/tools/`.

- **`evidence/statements-final-r1/`** (records `briefs/pairings/fills/bb1-sim/statements-final-r1/`, at the records tip
  `b31b77f7` before this pack; unchanged at the pin):
  - `bb1-sim-statements-r1-phase1-evidence.zip` (`6e4cbadd…`): the phase-1 review of #351's and #352's worker series
    (static checks, statements vs design §2.2, decls2, citations, Mathlib relatives, the worker's evidence recounted).
  - `bb1-sim-statements-r1-phase2-evidence.zip` (`411338e9…`): phase 2, the merged-tree replays R1 (#351 head
    `dfacac35`) and R2 (#352 head `92dea4f8`) on snapshot #2, axioms, Rule 10 (seals, controls, scan), lint, the
    cross-build P2-7.
  - `bb1-sim-statements-r1-phase2b-evidence.zip` (`13483b25…`): phase 2b, #352's re-replay on snapshot #3 (REV
    `3029d8c3`).
  - `evidence-SHA256SUMS`: the records' own sums of the three ZIPs.
- **`evidence/group-dedup/group-dedup-evidence.zip`** (`48d787d4…`; records `briefs/pairings/fixes/group-dedup/`): #365's
  evidence for both commits (`README.txt` maps `run-commit1/`, `run-commit2/`; inner `SHA256SUMS`).
- **`snapshots/olean-snapshot-3-adopt/`, `snapshots/olean-snapshot-4-adopt/`** (records
  `briefs/pass-shelat-ch5-8/maintainer/`): the adoptions of the #351 and #352 replays as olean snapshots #3 and #4
  (README, empty `step3-diff.txt`, `basecheck.out`, maps, files manifests, state init, rehash outputs).
- **`checks/`** (staging, git objects only): `series.txt` (commits, parents, trees, signature kind, numstat),
  `lean-equality.txt` (merges vs replayed trees, PR views vs merge diffs, base equalities), `mergetrees.txt` (#365 with
  the tip and the open PRs), `pr365-lines.txt` and `pr365-proof-only.txt` (#365 is proof-only apart from the new lemma;
  two negative controls), `dup-sweep.txt` (name and shape greps over TCSlib and Mathlib `029db123`); `tools/` holds the
  scripts (`checks.sh`, `dupsweep.sh`, `p365check.py`, `srchead.py`, `extract.py`, `gitput.sh`, `mkzip.py`).
- **`records/`** (at the tip `b31b77f7`, unchanged at the pin): the two statement reviews (`review.md`, `phase2.md`) and
  `phase2b-352.md`; #365's `report.md`; the bb1-sim `rulings.md`, `design-r1.md` and issued statement brief
  (`issued-stmt-r1/brief.md`); `policy.md`; Gate 44's, Gate 47's and Gate 48's findings (the G44-01 and G48-01
  precedents; what later gates said about these files); and extracts with a header naming file and lines: the decision
  log (`decision-log-pairings.md`), the duplication ledger (DL-40), the deferred-work register (DW-11), the cleanup
  Stage 2 rulings and plan lines on DW-11, and the snapshot register.
- **`pr/`**: the REST fields of #351, #352 and #365 at staging (`gh api repos/…/pulls/N`; #365's `merge_commit_sha` is
  GitHub's test merge and moves).

## ===== verification-r1.zip:POINTERS.md (this pack) =====

# POINTERS · what is not copied

- **Raw logs inside the evidence ZIPs** are copied whole (the ZIPs are nested unchanged); nothing was dropped from them.
- **The olean trees** (snapshot #2–#6, the replay outputs `olean-replay-bb1sim-games`, `olean-replay-352`,
  `olean-replay-grpfix`) are on the maintainer host only; their maps' SHA-256 are in the snapshot register extract, the
  adoption folders and #365's `run-commit2/output-map/map.out`.
- **Later gates' packs** (Gate 44, 47, 48) are not copied; only their findings files are, under `records/`.
- **Mathlib** is cited at `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e` (`lake-manifest.json`); the two files holding the
  nearest relatives are in `sources-r1.zip` (`mathlib-029db123/`).

## ===== verification-r1.zip:checks/series.txt (this pack) =====

# series.txt: commits, parents, trees, signatures (git objects; read-only)
records tip at staging (before this pack): b31b77f7f4127d9c6c6c0d6a1390de0dc8d71d43

== 176cfd4a42ac3300d9b84f9045f7abcd0f52ef13
tree b082d230b4124406dd00f7c5b60ec8731f34e1fb
parent 25575e276034289ad156a8a3078a2dad2d620a6d
author Claude <noreply@anthropic.com> 1794880193 +0000
committer Claude <noreply@anthropic.com> 1794880193 +0000
gpgsig: SSH
subject: Records: BS-F01 ruled (drop natCast_inj_of_lt via LE-grp1)
1	0	PairingCryptographyPlan.md
3	0	briefs/pairings/fills/bb1-sim/statements-final-r1/review.md

== 02000ad432b9d88e45ee109d3290c4be816a05b8
tree 5e1d13b19246f7cbdd0c41e0aec96ab541f2ebde
parent 176cfd4a42ac3300d9b84f9045f7abcd0f52ef13
author Claude <noreply@anthropic.com> 1794874633 +0000
committer Claude <noreply@anthropic.com> 1794880261 +0000
gpgsig: SSH
subject: stmt games-relational: public averaging bound in Games/Probability (Q6)
14	0	TCSlib/Cryptography/Games/Probability.lean

== dfacac356ff1225aca4c900d81bbf2cabce7b499
tree c6d3bed311a83f217428576b08065b5743003ec1
parent 02000ad432b9d88e45ee109d3290c4be816a05b8
author Claude <noreply@anthropic.com> 1794874633 +0000
committer Claude <noreply@anthropic.com> 1794880261 +0000
gpgsig: SSH
subject: stmt games-relational: Games/Relational, the relational simulation statements (Q1-Q4)
3	0	TCSlib/Cryptography/Games.lean
134	0	TCSlib/Cryptography/Games/Relational.lean

== cf7d28f7159b46033e8b8ae170954f9575e5d145
tree d72636c35ba880e73a764f5bff31aec1f4cc7fd6
parent 7b154493384f9b163c2be492cf0b37a7dbfe4e93
parent dfacac356ff1225aca4c900d81bbf2cabce7b499
author sragavan99 <33005360+sragavan99@users.noreply.github.com> 1794884428 -0800
committer GitHub <noreply@github.com> 1794884428 -0800
gpgsig: PGP
subject: Merge pull request #351 from Shilun-Allan-Li/land/bb1-sim-games
3	0	TCSlib/Cryptography/Games.lean
14	0	TCSlib/Cryptography/Games/Probability.lean
134	0	TCSlib/Cryptography/Games/Relational.lean
3	0	PairingCryptographyPlan.md
2	0	PassShelatChapter5-8Plan.md
-	-	briefs/pairings/fills/bb1-sim/statements-final-r1/bb1-sim-statements-r1-phase2-evidence.zip
1	0	briefs/pairings/fills/bb1-sim/statements-final-r1/evidence-SHA256SUMS
279	0	briefs/pairings/fills/bb1-sim/statements-final-r1/phase2.md
7	0	briefs/pairings/fills/bb1-sim/statements-final-r1/review.md
101	0	briefs/pass-shelat-ch5-8/cleanup-dw10/handoff-complexity/README.md
609	0	briefs/pass-shelat-ch5-8/cleanup-dw10/handoff-complexity/items.tsv
55	0	briefs/pass-shelat-ch5-8/cleanup-dw10/handoff-complexity/prompt.md
75	0	briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/README.md
21	0	briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/SHA256SUMS
613	0	briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/SOURCE-SHA256SUMS
10	0	briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/base-sorries.txt
378	0	briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/brief.md
461	0	briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/closures.txt
266	0	briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/derivation/derive.py
161	0	briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/derivation/finalize.py
48	0	briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/derivation/graph.py
66	0	briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/derivation/handoff.py
120	0	briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/derivation/leanindex.py
53	0	briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/derivation/origins.py
1454	0	briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/derivation/origins.tsv
111	0	briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/dispatch.md
180	0	briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/fill-environment-addendum.md
814	0	briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/ledger-current.tsv
765	0	briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/ledger-historical.tsv
29	0	briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/list-only.txt
79	0	briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/named-findings.tsv
613	0	briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/order.txt
521	0	briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/owners.txt
125	0	briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/provider-pairs.tsv
119	0	briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/roots.txt
7	0	briefs/pass-shelat-ch5-8/cleanup-stages.md
1	1	briefs/pass-shelat-ch5-8/deferred-work.md

== 2cca41bc4f4828c18c26cce7da7ca718cc00c2ac
tree 8740ccb6fe6f5072e4e086e64b91f4437e5a112d
parent 176cfd4a42ac3300d9b84f9045f7abcd0f52ef13
author Claude <noreply@anthropic.com> 1794874594 +0000
committer Claude <noreply@anthropic.com> 1794880401 +0000
gpgsig: SSH
subject: stmt pairing-group-helpers: group helpers in Pairing/Group (Q10)
34	0	TCSlib/Cryptography/Pairing/Group.lean

== 92dea4f8126747ea7e816984349b9dbb789f0065
tree 863b2926d896f45ca34061620985b45ae34d1edf
parent 2cca41bc4f4828c18c26cce7da7ca718cc00c2ac
author Claude <noreply@anthropic.com> 1794880407 +0000
committer Claude <noreply@anthropic.com> 1794880407 +0000
gpgsig: SSH
subject: LE-grp1: drop natCast_inj_of_lt (BS-F01; Mathlib's CharP.natCast_injOn_Iio suffices)
0	7	TCSlib/Cryptography/Pairing/Group.lean

== 463f224414ab7615e54104be353bfcda9dfceda7
tree e70ff1c962b64498899baed4b8f418eba0261405
parent d99c97f147bd61c3d09a63e7e66b9b2c0c8ee69f
parent 92dea4f8126747ea7e816984349b9dbb789f0065
author sragavan99 <33005360+sragavan99@users.noreply.github.com> 1794885951 -0800
committer GitHub <noreply@github.com> 1794885951 -0800
gpgsig: PGP
subject: Merge pull request #352 from Shilun-Allan-Li/land/bb1-sim-group
27	0	TCSlib/Cryptography/Pairing/Group.lean
6	0	PairingCryptographyPlan.md
3	0	PassShelatChapter5-8Plan.md
3	0	TCSlib/Cryptography/Games.lean
14	0	TCSlib/Cryptography/Games/Probability.lean
134	0	TCSlib/Cryptography/Games/Relational.lean
-	-	briefs/pairings/fills/bb1-sim/statements-final-r1/bb1-sim-statements-r1-phase2-evidence.zip
-	-	briefs/pairings/fills/bb1-sim/statements-final-r1/bb1-sim-statements-r1-phase2b-evidence.zip
2	0	briefs/pairings/fills/bb1-sim/statements-final-r1/evidence-SHA256SUMS
279	0	briefs/pairings/fills/bb1-sim/statements-final-r1/phase2.md
140	0	briefs/pairings/fills/bb1-sim/statements-final-r1/phase2b-352.md
7	0	briefs/pairings/fills/bb1-sim/statements-final-r1/review.md
101	0	briefs/pass-shelat-ch5-8/cleanup-dw10/handoff-complexity/README.md
609	0	briefs/pass-shelat-ch5-8/cleanup-dw10/handoff-complexity/items.tsv
55	0	briefs/pass-shelat-ch5-8/cleanup-dw10/handoff-complexity/prompt.md
75	0	briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/README.md
21	0	briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/SHA256SUMS
613	0	briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/SOURCE-SHA256SUMS
10	0	briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/base-sorries.txt
378	0	briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/brief.md
461	0	briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/closures.txt
266	0	briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/derivation/derive.py
161	0	briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/derivation/finalize.py
48	0	briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/derivation/graph.py
66	0	briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/derivation/handoff.py
120	0	briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/derivation/leanindex.py
53	0	briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/derivation/origins.py
1454	0	briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/derivation/origins.tsv
111	0	briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/dispatch.md
180	0	briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/fill-environment-addendum.md
814	0	briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/ledger-current.tsv
765	0	briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/ledger-historical.tsv
29	0	briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/list-only.txt
79	0	briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/named-findings.tsv
613	0	briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/order.txt
521	0	briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/owners.txt
125	0	briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/provider-pairs.tsv
119	0	briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/roots.txt
7	0	briefs/pass-shelat-ch5-8/cleanup-stages.md
1	1	briefs/pass-shelat-ch5-8/deferred-work.md
11	0	briefs/pass-shelat-ch5-8/maintainer/olean-snapshot-3-adopt/README.md
5	0	briefs/pass-shelat-ch5-8/maintainer/olean-snapshot-3-adopt/basecheck.out
1453	0	briefs/pass-shelat-ch5-8/maintainer/olean-snapshot-3-adopt/olean-snapshot.files-cf7d28f7.txt
1453	0	briefs/pass-shelat-ch5-8/maintainer/olean-snapshot-3-adopt/olean-snapshot.map-cf7d28f7.tsv
-	-	briefs/pass-shelat-ch5-8/maintainer/olean-snapshot-3-adopt/state-init-cf7d28f7.json.gz
0	0	briefs/pass-shelat-ch5-8/maintainer/olean-snapshot-3-adopt/step3-diff.txt
0	0	briefs/pass-shelat-ch5-8/maintainer/olean-snapshot-3-adopt/v2-final/changed.txt
0	0	briefs/pass-shelat-ch5-8/maintainer/olean-snapshot-3-adopt/v2-final/extra.txt
0	0	briefs/pass-shelat-ch5-8/maintainer/olean-snapshot-3-adopt/v2-final/missing.txt
0	0	briefs/pass-shelat-ch5-8/maintainer/olean-snapshot-3-adopt/v3/changed.txt
0	0	briefs/pass-shelat-ch5-8/maintainer/olean-snapshot-3-adopt/v3/extra.txt
0	0	briefs/pass-shelat-ch5-8/maintainer/olean-snapshot-3-adopt/v3/missing.txt
2	1	briefs/pass-shelat-ch5-8/maintainer/snapshots.md

== 5aed99076d2bd4e5d6f831aed88739fc3ce475b6
tree a7ce6ecc7695d37ca3e98bdd4ecca97411e58a7e
parent 7d2ec2fc80b111efdd6f246f8488361d1aff14b0
author Claude <noreply@anthropic.com> 1794939915 +0000
committer Claude <noreply@anthropic.com> 1794939915 +0000
gpgsig: SSH
subject: Records: DW-11 sweep ruling (fix #352 overlap in a follow-up PR)
1	0	PairingCryptographyPlan.md

== 6fc5f49456507dab5901045356ea40acf42bdd67
tree ba10f0a2038991393c5721f3bf00ad3c4d90e59e
parent 5aed99076d2bd4e5d6f831aed88739fc3ce475b6
author Claude <noreply@anthropic.com> 1794940184 +0000
committer Claude <noreply@anthropic.com> 1794940184 +0000
gpgsig: SSH
subject: Pairing: one generic prime-order bijectivity lemma; reuse Mathlib in Group.lean (DW-11 follow-up)
25	17	TCSlib/Cryptography/Pairing/Group.lean

== 5eaddd171bceccee917929e7f319ff9202994c59
tree 9710ac7d02e95c73cf7ae7715713aa8defcda526
parent 6fc5f49456507dab5901045356ea40acf42bdd67
author Claude <noreply@anthropic.com> 1794940785 +0000
committer Claude <noreply@anthropic.com> 1794940785 +0000
gpgsig: SSH
subject: Pairing: pow_mod_card in pow_val_mul_GT; list the generic lemma in Main results (DW-11 follow-up)
3	2	TCSlib/Cryptography/Pairing/Group.lean

== ancestry
merge-base(dfacac35, 92dea4f8) = 176cfd4a42ac3300d9b84f9045f7abcd0f52ef13
merge-base(4bc5bac4, dfacac35) = 176cfd4a42ac3300d9b84f9045f7abcd0f52ef13  (REST base.sha of #351/#352 is 4bc5bac4)
#351 commits on 176cfd4a: 2; #352: 2; #365 on 5aed9907: 2
is cf7d28f7 ancestor of tip b31b77f7f4127d9c6c6c0d6a1390de0dc8d71d43: yes
is 463f2244 ancestor of tip b31b77f7f4127d9c6c6c0d6a1390de0dc8d71d43: yes
is 5aed9907 ancestor of tip b31b77f7f4127d9c6c6c0d6a1390de0dc8d71d43: yes

## ===== verification-r1.zip:checks/lean-equality.txt (this pack) =====

# lean-equality.txt: merge commits against the replayed trees (paths: *.lean lean-toolchain lake-manifest.json lakefile.lean)
## #351 merge cf7d28f7 vs phase-2 R1 prospective tree c6d3bed3 (adopted as snapshot #3):
(end; empty = equal)
## #351 merge cf7d28f7 vs PR head dfacac35:
(end)
## #352 merge 463f2244 vs phase-2b REV 3029d8c3 (adopted as snapshot #4):
(end; empty = equal)
## #352 merge 463f2244 vs cf7d28f7 (should be Group.lean only):
 TCSlib/Cryptography/Pairing/Group.lean | 27 +++++++++++++++++++++++++++
 1 file changed, 27 insertions(+)
(end)
## #351 first-parent diff equals the PR view (176cfd4a..dfacac35)? (compare patch bodies without index lines)
EQUAL
EQUAL incl. index lines
## #352 first-parent diff equals the PR view (176cfd4a..92dea4f8)?
EQUAL
EQUAL incl. index lines
## base Lean of #365 (5aed9907) vs the tip b31b77f7f4127d9c6c6c0d6a1390de0dc8d71d43:
(end; empty = records-only since the base)
## changes to the audited files from the merges to the tip (out of scope; shown for context):
 TCSlib/Cryptography/Games.lean            |  3 +++
 TCSlib/Cryptography/Games/Relational.lean | 16 ++++++++++++++--
 2 files changed, 17 insertions(+), 2 deletions(-)
a1fa7b652 Merge pull request #355 from Shilun-Allan-Li/land/cleanup-stage1
2845f1002 fill bb1-sim: prove expect_simulate_rel and expect_sample_rel
c502027cf cleanup stage1: Games forms of simulation in law, coin tapes and tables (DL-40, DL-41, DL-42)

## Lean-equality of bases (paths as above)
176cfd4a42ac3300d9b84f9045f7abcd0f52ef13..4bc5bac4aad70eed9733e8311a63fd12bd974802: [] (empty = Lean-equal)
176cfd4a42ac3300d9b84f9045f7abcd0f52ef13..7b154493384f9b163c2be492cf0b37a7dbfe4e93: [] (empty = Lean-equal)
cf7d28f7159b46033e8b8ae170954f9575e5d145..d99c97f147bd61c3d09a63e7e66b9b2c0c8ee69f: [] (empty = Lean-equal)
13fc8060d5b8d08a8f9e80244242118acaa679e2..5aed99076d2bd4e5d6f831aed88739fc3ce475b6: [] (empty = Lean-equal)

## ===== verification-r1.zip:checks/mergetrees.txt (this pack) =====

# mergetrees.txt: git merge-tree --write-tree (git 2.43.0)
#365 head 5eaddd17 x b31b77f7f4127d9c6c6c0d6a1390de0dc8d71d43: rc=0 tree=319c9aa00884e38c4f4f73f7f98a718bf496186c
  diff tip..merged (all paths):
     TCSlib/Cryptography/Pairing/Group.lean | 47 ++++++++++++++++++++--------------
     1 file changed, 28 insertions(+), 19 deletions(-)
  merged vs head over Lean paths:
    (end; empty = Lean-equal to the head)
## #365 head x the other open PRs into cryptography/pass-shelat-ch2-4 (REST list at staging: #358, #359, #360; #364 targets main). 'shared' = paths changed on both sides since their merge base
land/gsw-6a-readers cc05f76c43cd2d2f565ff0dfaec1c85b47e06d25 merge-base=8c5875fa268a622e4e166da5f7a992715097c2c7 rc=0 tree=1420ac6c5135a81e6f244d138318e81abbad6a43 shared=[] group-differs-from-land/gsw-6a-readers-in-merge=[TCSlib/Cryptography/Pairing/Group.lean]
land/gsw-6a-statements d154c8830fc8ffc52671b41992e7dbef61e30959 merge-base=e1d39836ed4a69a34914c35f4c73c71de853dcc6 rc=0 tree=54f8023b0c37dcf3c32ab7ea8d6ed24b3fdd1d23 shared=[] group-differs-from-land/gsw-6a-statements-in-merge=[TCSlib/Cryptography/Pairing/Group.lean]
land/gsw-6a-o1 a616adcac0760ab56b1b0a2a4869f4763843f9ab merge-base=e1d39836ed4a69a34914c35f4c73c71de853dcc6 rc=0 tree=4c43a414940e653c9eb0198224d995b0239e1511 shared=[] group-differs-from-land/gsw-6a-o1-in-merge=[TCSlib/Cryptography/Pairing/Group.lean]

## ===== verification-r1.zip:checks/pr365-proof-only.txt (this pack) =====

HEAD:
  insert blocks: 2; inserted lines: 20
   ---
   + * `pow_val_bijective_of_prime_card` — `a ↦ g^a` is a bijection `Z_p → M` for `g ≠ 1` in any finite
   +   group `M` of prime order `p` (the generic form of the two bijections above).
   ---
   + 
   + /-- **`a ↦ g^a` is a bijection `Z_p → M`** for every `g ≠ 1` in a finite group `M` of prime order
   + `p`: if `|M| = p` is prime and `g ≠ 1`, then `Function.Bijective fun a : ZMod p => g ^ a.val`.
   + The one statement behind `BilinearGroup.pow_val_bijective` (on `G_T`) and
   + `BilinearGroup.pow_val_bijective_of_ne_one` (on `G`).
   + 
   + Glue lemma, with no counterpart in [BB04]: elementary group theory, assembled from Mathlib
   + (`orderOf_eq_prime`, `pow_injOn_Iio_orderOf`). Mathlib's closest statement,
   + `IsCyclic.unique_zpow_zmod`, gives the unique exponent in `ZMod (Fintype.card M)` of each element
   + for a generator `g`, not this bijectivity on `ZMod p`.
   + 
   + **Proof sketch.** By Lagrange, `g^p = 1`, so `g ≠ 1` has order exactly `p`. Hence `n ↦ g^n` is
   + injective on `{0, …, p - 1}`, which contains every `a.val`, so `a ↦ g^{a.val}` is injective on
   + `Z_p`. Both sides have `p` elements, so it is a bijection. -/
   + theorem pow_val_bijective_of_prime_card {M : Type*} [Group M] [Fintype M] {p : ℕ}
   +     [Fact p.Prime] (hM : Fintype.card M = p) {g : M} (hg : g ≠ 1) :
   +     Function.Bijective fun a : ZMod p => g ^ a.val := by
   +   <BODY pow_val_bijective_of_prime_card>
  bodies changed: ['pow_val_add', 'pow_val_bijective', 'pow_val_bijective_of_ne_one', 'pow_val_mul', 'pow_val_mul_GT']
  declarations removed: []
RESULT PASS
control header char FAIL (as required)
control docstring char FAIL (as required)

## ===== verification-r1.zip:checks/dup-sweep.txt (this pack) =====

# dup-sweep.txt (staging greps; the judgement is in pack-r1.md, question 5)
tip: b31b77f7f4127d9c6c6c0d6a1390de0dc8d71d43   #365 head: 5eaddd171bceccee917929e7f319ff9202994c59   Mathlib: 029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e   (lake-manifest inputRev: "inputRev":"029db123ddaa")

## 1. exact names, declarations at the tip and at the #365 head (TCSlib/, audits/)
-- b31b77f7f4127d9c6c6c0d6a1390de0dc8d71d43
TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Forgery.lean:515:private theorem abs_expect_sub_le_expect {β : Type} (c : ProbComp β) {f g h : β → ℝ}
TCSlib/Cryptography/Games/Probability.lean:409:theorem abs_expect_sub_le_expect (c : ProbComp α) {f g h : α → ℝ}
TCSlib/Cryptography/Games/Relational.lean:85:theorem expect_simulate_rel (impl₀ : QueryImpl spec σ unifSpec)
TCSlib/Cryptography/Games/Relational.lean:111:theorem prob_simulate_rel (impl₀ : QueryImpl spec σ unifSpec)
TCSlib/Cryptography/Games/Relational.lean:130:theorem expect_sample_rel {U V β : Type} [Fintype U] [Nonempty U] [Fintype V] [Nonempty V]
TCSlib/Cryptography/Pairing/Group.lean:239:theorem pow_val_add (x : B.G) (a b : ZMod B.order) :
TCSlib/Cryptography/Pairing/Group.lean:246:theorem pow_val_neg (x : B.G) (a : ZMod B.order) : x ^ (-a).val = (x ^ a.val)⁻¹ := by
TCSlib/Cryptography/Pairing/Group.lean:252:theorem pow_val_bijective_of_ne_one {g : B.G} (hg : g ≠ 1) :
-- 5eaddd171bceccee917929e7f319ff9202994c59
TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Forgery.lean:515:private theorem abs_expect_sub_le_expect {β : Type} (c : ProbComp β) {f g h : β → ℝ}
TCSlib/Cryptography/Games/Probability.lean:409:theorem abs_expect_sub_le_expect (c : ProbComp α) {f g h : α → ℝ}
TCSlib/Cryptography/Games/Relational.lean:85:theorem expect_simulate_rel (impl₀ : QueryImpl spec σ unifSpec)
TCSlib/Cryptography/Games/Relational.lean:111:theorem prob_simulate_rel (impl₀ : QueryImpl spec σ unifSpec)
TCSlib/Cryptography/Games/Relational.lean:130:theorem expect_sample_rel {U V β : Type} [Fintype U] [Nonempty U] [Fintype V] [Nonempty V]
TCSlib/Cryptography/Pairing/Group.lean:154:theorem pow_val_bijective_of_prime_card {M : Type*} [Group M] [Fintype M] {p : ℕ}
TCSlib/Cryptography/Pairing/Group.lean:254:theorem pow_val_add (x : B.G) (a b : ZMod B.order) :
TCSlib/Cryptography/Pairing/Group.lean:260:theorem pow_val_neg (x : B.G) (a : ZMod B.order) : x ^ (-a).val = (x ^ a.val)⁻¹ := by
TCSlib/Cryptography/Pairing/Group.lean:266:theorem pow_val_bijective_of_ne_one {g : B.G} (hg : g ≠ 1) :

## 2. exact names in Mathlib (expect none)
(end)

## 3. averaging-bound shapes in TCSlib at the tip
TCSlib/BooleanAnalysis/Hypercontractivity/Products/Applications.lean:270:private theorem product_boolean_residual_abs_expect {n : ℕ}
TCSlib/BooleanAnalysis/ThresholdFunctions/Gaussian.lean:87:theorem rademacher_abs_expectation :
TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Draws.lean:448:theorem abs_expect_draws_sub_le (κ : ℕ) (d : List Bool) (cap : ℕ)
TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Oracles.lean:324:theorem abs_expect_bb1Sim_sub_distinguisherL_le (H : ArithmeticFP) (O : G.Ops) (A A' : NUPPT)
TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Reduction.lean:229:theorem abs_expect_runAccept_sub_le :
TCSlib/Cryptography/Asymptotic/Sampling.lean:239:theorem abs_uexp_sub_le {α : Type*} [Fintype α] {f g : α → ℝ} {c : ℝ} (hc : 0 ≤ c)
TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Forgery.lean:515:private theorem abs_expect_sub_le_expect {β : Type} (c : ProbComp β) {f g h : β → ℝ}
TCSlib/Cryptography/Encryption/PrivateKey/FromPRF/HybridLemmas.lean:49:theorem abs_uexp_le_uexp_abs {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) :
TCSlib/Cryptography/Encryption/PrivateKey/FromPRF/HybridLemmas.lean:61:theorem abs_uexp_sub_le_uprob {Ω : Type*} [Fintype Ω] (a b : Ω → ℝ) (E : Ω → Prop)
TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF/Collision.lean:375:theorem abs_expect_fImpl_sub_le (hatk : FixedLengthScheme.decOpen atk true = false)
TCSlib/Cryptography/Games/Probability.lean:393:theorem abs_expect_sub_le (c : ProbComp α) {f g : α → ℝ} {ε : ℝ}
TCSlib/Cryptography/Games/Probability.lean:409:theorem abs_expect_sub_le_expect (c : ProbComp α) {f g h : α → ℝ}
TCSlib/Cryptography/SecureComputation/ComposeSecurity/Probability.lean:83:theorem exists_abs_uexp_sub_le [Nonempty σ] (f g : σ → ℝ) :
TCSlib/Cryptography/ZeroKnowledge/CommitmentLemmas.lean:79:theorem exists_abs_uexp_le {κ : Type*} [Fintype κ] [Nonempty κ] (f : κ → ℝ) :

## 4. simulation lemmas in Games/ and the ETT tools at the tip (relational/abstraction relatives)
TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Tools.lean:65:theorem expect_simulate_abs (impl₁ : QueryImpl spec σ₁ unifSpec)
TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Tools.lean:88:theorem expect_simulate_abs_inv (impl₁ : QueryImpl spec σ₁ unifSpec)
TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Tools.lean:145:theorem simulate_tapeImpl_congr (K : ∀ i, spec.dom i → σ → τ → ProbComp (spec.rng i × σ))
TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Tools.lean:167:theorem expect_simulate_tapeImpl [Fintype τ] [Nonempty τ]
TCSlib/Cryptography/Games/BitCodec.lean:415:theorem simulate_castImpl_toCompOn {ins ins' outs outs' : Fin k → ℕ} {d d' : ℕ}
TCSlib/Cryptography/Games/BitCodec.lean:430:theorem expect_simulate_castImpl_toCompOn {ins ins' outs outs' : Fin k → ℕ} {d d' : ℕ}
TCSlib/Cryptography/Games/Bridges/QueryTree.lean:83:theorem simulate_ofComp_pure {ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
TCSlib/Cryptography/Games/Bridges/QueryTree.lean:124:theorem simulate_eq (π : I → I') (ans : I → O' → O) (t : TCSlib.Cryptography.QueryTree I O α)
TCSlib/Cryptography/Games/Hopping.lean:179:theorem simulate_allOutputs_bad {spec : OracleSpec ι} {impl : QueryImpl spec σ unifSpec}
TCSlib/Cryptography/Games/Hopping.lean:384:theorem expect_simulate_congr {ι : Type} {spec : OracleSpec ι} {σ α : Type}
TCSlib/Cryptography/Games/Hopping.lean:469:private theorem simulate_eq_of_used (O O' : QueryImpl spec σ unifSpec) (used : σ → Prop)
TCSlib/Cryptography/Games/Hopping.lean:494:theorem expect_simulate_eager (O : QueryImpl spec σ unifSpec) (OE : T → QueryImpl spec σ unifSpec)
TCSlib/Cryptography/Games/Relational.lean:85:theorem expect_simulate_rel (impl₀ : QueryImpl spec σ unifSpec)
TCSlib/Cryptography/Games/Relational.lean:111:theorem prob_simulate_rel (impl₀ : QueryImpl spec σ unifSpec)
TCSlib/Cryptography/Games/Simulate.lean:107:theorem simulate_bind (c : OracleComp spec α) (f : α → OracleComp spec β) (s : σ) :
TCSlib/Cryptography/Games/Simulate.lean:114:theorem simulate_call (i : ι) (x : spec.dom i) (s : σ) :
TCSlib/Cryptography/Games/Simulate.lean:199:theorem simulate_comp {ι'' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
TCSlib/Cryptography/Games/Simulate.lean:241:theorem simulate_withLog {spec : OracleSpec ι} {spec' : OracleSpec ι'}
TCSlib/Cryptography/Games/Simulate.lean:264:theorem simulate_costBoundedBy {spec : OracleSpec ι} {spec' : OracleSpec ι'}
TCSlib/Cryptography/Games/Simulate.lean:290:theorem simulate_costBoundedBy_once {spec : OracleSpec ι} {spec' : OracleSpec ι'}
TCSlib/Cryptography/Games/Simulate.lean:334:theorem simulate_eq_of_abs {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
TCSlib/Cryptography/Games/Simulate.lean:357:theorem simulate_eq_of_abs_bounded {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
TCSlib/Cryptography/Games/Tapes.lean:72:protected theorem expect_simulate_abs (impl₁ : QueryImpl spec σ₁ unifSpec)
TCSlib/Cryptography/Games/Tapes.lean:96:protected theorem expect_simulate_abs_inv (impl₁ : QueryImpl spec σ₁ unifSpec)
TCSlib/Cryptography/Games/Tapes.lean:185:protected theorem simulate_tapeImpl_congr
TCSlib/Cryptography/Games/Tapes.lean:209:protected theorem expect_simulate_tapeImpl [Fintype τ] [Nonempty τ]

## 5. one-sample couplings: (sample _).bind fun _ => .pure in statements at the tip
TCSlib/Cryptography/Encryption/PublicKey/AdaptiveCPA/Hybrid.lean:84:`hybImpl κ E sel 1 mm h = (sample C).bind fun r => pure (padFin (outs 1) ⟦c⟧, c :: h)`. -/
TCSlib/Cryptography/Encryption/PublicKey/AdaptiveCPA/Hybrid.lean:138:`tapeImpl κ E sel T kst 1 mm h = (sample C).bind fun r => pure (padFin (outs 1) ⟦c⟧, c :: h)`
TCSlib/Cryptography/Games/Hopping.lean:156:    prob (c.bind fun L => (sample T).bind fun t => .pure (L, t)) (fun p => p.2 ∈ p.1) ≤
TCSlib/Cryptography/Games/Hopping.lean:160:  calc expect c (fun L => prob ((sample T).bind fun t => .pure (L, t)) (fun p => p.2 ∈ p.1))
TCSlib/Cryptography/Games/Relational.lean:134:    expect ((sample U).bind fun u => .pure (f₀ u)) g₀ =
TCSlib/Cryptography/Games/Relational.lean:135:      expect ((sample V).bind fun v => .pure (f₁ v)) g₁ := by

## 6. bijections ZMod -> group, exponent laws (TCSlib at the #365 head)
TCSlib/Cryptography/Candidates/DDH.lean:92:  orderOf_eq_prime ((mem_QR_iff_pow_eq_one hpq x).1 hx) hx1
TCSlib/Cryptography/Candidates/DiscreteLog.lean:473:    exact orderOf_eq_prime (by decide) (by decide)
TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean:133:theorem expo_bijective {g : (ZMod p)ˣ} (hg : IsGenerator g) : Function.Bijective (expo g) :=
TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean:612:  rw [hsplit, hB, ht, ← Nat.cast_add, Nat.mod_add_div' x.val s, ZMod.natCast_zmod_val]
TCSlib/Cryptography/NumberTheory/Euclid.lean:197:        have hmod := Nat.mod_add_div a b
TCSlib/Cryptography/Pairing/Group.lean:142:`p`: if `|M| = p` is prime and `g ≠ 1`, then `Function.Bijective fun a : ZMod p => g ^ a.val`.
TCSlib/Cryptography/Pairing/Group.lean:147:(`orderOf_eq_prime`, `pow_injOn_Iio_orderOf`). Mathlib's closest statement,
TCSlib/Cryptography/Pairing/Group.lean:156:    Function.Bijective fun a : ZMod p => g ^ a.val := by
TCSlib/Cryptography/Pairing/Group.lean:157:  have ho : orderOf g = p := orderOf_eq_prime (by rw [← hM]; exact pow_card_eq_one) hg
TCSlib/Cryptography/Pairing/Group.lean:160:  exact pow_injOn_Iio_orderOf (ho ▸ ZMod.val_lt a) (ho ▸ ZMod.val_lt b) hab
TCSlib/Cryptography/Pairing/Group.lean:219:  rw [ZMod.val_mul, ← pow_mod_card x (a.val * b.val), B.card_G]
TCSlib/Cryptography/Pairing/Group.lean:224:  rw [ZMod.val_mul, ← pow_mod_card y (a.val * b.val), B.card_GT]
TCSlib/Cryptography/Pairing/Group.lean:237:    orderOf_eq_prime (B.pow_order_GT _) B.pair_gen_ne_one
TCSlib/Cryptography/Pairing/Group.lean:249:    Function.Bijective fun a : ZMod B.order => B.pair x x ^ a.val := by
TCSlib/Cryptography/Pairing/Group.lean:256:  rw [ZMod.val_add, ← pow_add, ← pow_mod_card x (a.val + b.val), B.card_G]
TCSlib/Cryptography/Pairing/Group.lean:264:`Function.Bijective fun a : ZMod B.order => g ^ a.val` (the identification `Z_p ≃ G` of the
TCSlib/Cryptography/Pairing/Group.lean:267:    Function.Bijective fun a : ZMod B.order => g ^ a.val := by
TCSlib/Cryptography/ZeroKnowledge/Encoding.lean:585:      (Nat.mod_add_div m n).symm
TCSlib/Cryptography/ZeroKnowledge/Encoding.lean:636:      (Nat.mod_add_div m n).symm
TCSlib/Cryptography/ZeroKnowledge/Encoding.lean:717:      (Nat.mod_add_div m n).symm
TCSlib/Cryptography/ZeroKnowledge/EncodingMachines.lean:653:  exact (Nat.eq_sub_of_add_eq (Nat.mod_add_div' a m)).symm
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ColRepWitness.lean:193:(→) A set position `j < N²` is the edge `(j / N, j % N)` (`Nat.mod_add_div`), whose colours
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ColRepWitness.lean:212:      have : j % N + N * (j / N) = j := Nat.mod_add_div j N

## 7. Mathlib relatives (declaration lines)
Mathlib/NumberTheory/MulChar/Basic.lean:527:protected lemma pow_card_eq_one [Fintype Mˣ] (χ : MulChar M R) : χ ^ (Fintype.card Mˣ) = 1 := by
Mathlib/GroupTheory/SpecificGroups/Cyclic.lean:394:theorem IsCyclic.unique_zpow_zmod (ha : ∀ x : α, x ∈ zpowers a) (x : α) :
Mathlib/GroupTheory/SpecificGroups/Cyclic.lean:771:noncomputable def zmodCyclicMulEquiv [Group G] (h : IsCyclic G) :
Mathlib/GroupTheory/SpecificGroups/Cyclic.lean:788:noncomputable def mulEquivOfPrimeCardEq {p : ℕ} [Group G] [Group G']
Mathlib/GroupTheory/OrderOfElement.lean:248:lemma pow_mod_orderOf (x : G) (n : ℕ) : x ^ (n % orderOf x) = x ^ n :=
Mathlib/GroupTheory/OrderOfElement.lean:268:lemma pow_injOn_Iio_orderOf : (Set.Iio <| orderOf x).InjOn (x ^ ·) := by
Mathlib/GroupTheory/OrderOfElement.lean:490:theorem orderOf_eq_prime (hg : x ^ p = 1) (hg1 : x ≠ 1) : orderOf x = p :=
Mathlib/GroupTheory/OrderOfElement.lean:510:noncomputable def finEquivPowers {x : G} (hx : IsOfFinOrder x) : Fin (orderOf x) ≃ powers x :=
Mathlib/GroupTheory/OrderOfElement.lean:545:theorem pow_eq_pow_iff_modEq : x ^ n = x ^ m ↔ n ≡ m [MOD orderOf x] := by
Mathlib/GroupTheory/OrderOfElement.lean:716:noncomputable def finEquivZPowers (hx : IsOfFinOrder x) :
Mathlib/GroupTheory/OrderOfElement.lean:999:theorem pow_card_eq_one' {G : Type*} [Group G] {x : G} : x ^ Nat.card G = 1 :=
Mathlib/GroupTheory/OrderOfElement.lean:1003:theorem pow_card_eq_one : x ^ Fintype.card G = 1 := by
Mathlib/GroupTheory/OrderOfElement.lean:1012:lemma pow_mod_card (a : G) (n : ℕ) : a ^ (n % card G) = a ^ n := by
Mathlib/GroupTheory/OrderOfElement.lean:1021:lemma pow_mod_natCard {G} [Group G] (a : G) (n : ℕ) : a ^ (n % Nat.card G) = a ^ n := by
Mathlib/RingTheory/RootsOfUnity/PrimitiveRoots.lean:428:def zmodEquivZPowers (h : IsPrimitiveRoot ζ k) : ZMod k ≃+ Additive (Subgroup.zpowers ζ) :=

## 8. Mathlib: any statement 'Bijective fun _ : ZMod _ => _ ^ _.val' (expect none)
(end)

## 9. Mathlib: ZMod-indexed exponent statements '^ (_ + _).val', '^ (-_).val' (expect none)
(end)

## ===== verification-r1.zip:snapshots/olean-snapshot-3-adopt/README.md (this pack) =====

# Olean snapshot #3: adoption at the #351 merge (2026-11-17)

- **New T:** `cf7d28f7159b46033e8b8ae170954f9575e5d145` (merge of #351, bb1-sim Games statements).
- **Source:** the phase-2 replay R1 of `land/bb1-sim-games` `dfacac35` (`briefs/pairings/fills/bb1-sim/statements-final-r1/phase2.md`): a `cp -al` of snapshot #2 with 181 modules rebuilt (rc 0, 0 errors), state 1422/1422 OK.
- **Step-3 diff** (`git diff --name-only <merge> <head> -- '*.lean' lean-toolchain lake-manifest.json`): empty (`step3-diff.txt`).
- **Snapshot #2 at retirement:** rehash 0/0/0 against map `95493449…` (`v2-final/`).
- **Adoption:** `Mathlib/` overlay removed; `snapmap.py make` → map `olean-snapshot.map-cf7d28f7.tsv`, SHA-256 `e9dfbfddfd6ca253f9fd5ee6c3efe868f8614083794312c89d32032564fea53d`, 1453 entries (TCSlib 1420, audits 2, PFR 31); `snapshot.py` → files manifest `olean-snapshot.files-cf7d28f7.txt`, SHA-256 `1e9a3ba7c0dd8b18c2d38d498fff30b5ee88a48f8c560673484fb1049cb85733`.
- **basecheck:** `stateplan.py init` at `cf7d28f7` (1422 modules) against R1's checked state over its full order: 0 key/olean disagreements, RESULT OK (`basecheck.out`, `state-init-cf7d28f7.json.gz`).
- **Swap:** #2's oleans deleted, R1 moved to `$SP/olean-snapshot`; rehash 0/0/0 against the new map (`v3/`).
- **Discarded:** R2 (`land/bb1-sim-group` replay), no longer adoptable after #351 (shared `BonehBoyen*` downstream); its evidence is in the phase-2 zip. #352 and #346 re-replay on #3.
- Tools: `olean-rebase-dl-oleans-2/olean-rebase-evidence.zip`, `olean-advance-a6d01b1b/tools-used/`.

## ===== verification-r1.zip:snapshots/olean-snapshot-4-adopt/README.md (this pack) =====

# Olean snapshot #4: adoption at the #352 merge (2026-11-17)

- **New T:** `463f224414ab7615e54104be353bfcda9dfceda7` (merge of #352, bb1-sim group helpers).
- **Source:** the re-replay of #352 on snapshot #3 (`$SP/olean-replay-352`; `briefs/pairings/fills/bb1-sim/statements-final-r1/phase2b-352.md`): merge tree `3029d8c3`, 12 modules rebuilt (rc 0, 0 errors), state 1422/1422 OK.
- **Step-3 diff** against `3029d8c3`: empty (`step3-diff.txt`).
- **Snapshot #3 at retirement:** rehash 0/0/0 against map `e9dfbfdd…` (`v3-final/`).
- **Adoption:** `Mathlib/` overlay removed; map `olean-snapshot.map-463f2244.tsv`, SHA-256 `6607620d725049c90b34a51a2ab891f1520fd0f576aaf3f9d51301222cee41e7`, 1453 entries (TCSlib 1420, audits 2, PFR 31); files manifest `olean-snapshot.files-463f2244.txt`, SHA-256 `4364054c7f864102947e807f4da9606a0630479044849b8cdb962c98a3fbccc0`.
- **basecheck:** init at `463f2244` (1422 modules) against the replay's checked state: 0 disagreements, RESULT OK (build revs: `cf7d28f7` 1410, `3029d8c3` 12).
- **Swap:** #3's oleans deleted, the replay moved to `$SP/olean-snapshot`; rehash 0/0/0 (`v4/`).
- #346's replay on #3 (`olean-replay-346b`) is no longer adoptable (shared `BonehBoyen*` downstream); #346 re-replays on #4.

## ===== pr351.diff.txt (this pack) =====

diff --git a/TCSlib/Cryptography/Games.lean b/TCSlib/Cryptography/Games.lean
index fb3115e91..ce4a9f308 100644
--- a/TCSlib/Cryptography/Games.lean
+++ b/TCSlib/Cryptography/Games.lean
@@ -7,6 +7,7 @@ import TCSlib.Cryptography.Games.Probability
 import TCSlib.Cryptography.Games.Simulate
 import TCSlib.Cryptography.Games.Advantage
 import TCSlib.Cryptography.Games.Hopping
+import TCSlib.Cryptography.Games.Relational
 import TCSlib.Cryptography.Games.Protocols
 import TCSlib.Cryptography.Games.Forwarding
 
@@ -40,6 +41,8 @@ the interaction model `Strategy`.
   advantages, the hybrid argument.
 * `TCSlib.Cryptography.Games.Hopping`: the difference lemma, identical until bad, the collision
   bound.
+* `TCSlib.Cryptography.Games.Relational`: simulations of two implementations on related states
+  (the relational form of simulation congruence).
 * `TCSlib.Cryptography.Games.Protocols`: parties, the message exchange, executions in a
   coroutine model that contains D8's (bridge B4), and traced executions recording received
   messages and coin draws.
diff --git a/TCSlib/Cryptography/Games/Probability.lean b/TCSlib/Cryptography/Games/Probability.lean
index c27939a16..b7e8d3d10 100644
--- a/TCSlib/Cryptography/Games/Probability.lean
+++ b/TCSlib/Cryptography/Games/Probability.lean
@@ -46,6 +46,7 @@ information-theory layer, so statistical distance and closeness (`EpsClose`) app
 * `ProbComp.expect_sample_equiv`, `expect_sample_comm`, `expect_sample_unique`,
   `expect_sample_update`, `expect_sample_coord`: reindexing, exchanging and resampling uniform
   samples; `expect_sub`, `abs_expect_sub_le`: subtraction and pointwise closeness.
+* `ProbComp.abs_expect_sub_le_expect`: averaging a pointwise bound.
 * `ProbComp.expect_expect_sample`: exchanging an expectation with a uniform sample (Fubini).
 
 ## References
@@ -402,6 +403,19 @@ theorem abs_expect_sub_le (c : ProbComp α) {f g : α → ℝ} {ε : ℝ}
   rw [abs_le]
   constructor <;> linarith
 
+/-- **Averaging a pointwise bound:** expectations of functions within a pointwise bound of each
+other are within the expectation of the bound:
+`(∀ x, |f x - g x| ≤ h x) → |𝔼_c f - 𝔼_c g| ≤ 𝔼_c h`. -/
+theorem abs_expect_sub_le_expect (c : ProbComp α) {f g h : α → ℝ}
+    (hb : ∀ x, |f x - g x| ≤ h x) : |expect c f - expect c g| ≤ expect c h := by
+  rw [← expect_sub, abs_le]
+  constructor
+  · have := expect_mono c fun x => (neg_le_of_abs_le (hb x))
+    rw [show (fun x => -h x) = fun x => (-1) * h x from funext fun x => by ring,
+      expect_const_mul] at this
+    linarith
+  · exact expect_mono c fun x => le_of_abs_le (hb x)
+
 end Sampling
 
 end ProbComp
diff --git a/TCSlib/Cryptography/Games/Relational.lean b/TCSlib/Cryptography/Games/Relational.lean
new file mode 100644
index 000000000..eee8e19f1
--- /dev/null
+++ b/TCSlib/Cryptography/Games/Relational.lean
@@ -0,0 +1,134 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Games.Simulate
+import TCSlib.Cryptography.Games.Probability
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Simulations on related states
+
+Two implementations of the same oracles may keep states of different types: in a security proof
+the real game and its simulation often record different data for the same history (for BB1, the
+committed identity with a group element `h`, or with an exponent `α_1`). If a relation `R`
+between the two kinds of state holds at the start, and every call from related states answers
+alike and leads to related states, then the two simulations of any computation answer alike and
+end in related states (`ProbComp.expect_simulate_rel`). "Alike" is measured by expectations: a
+call, or a run, from related states gives the same expectation to any two functions of the
+answer and the state that agree at equal answers and related states.
+
+With one state type and `R` the equality this is `ProbComp.expect_simulate_congr`
+(`Games.Hopping`); with `R s t ↔ s = f t` it is the law form of `simulate_eq_of_abs`
+(`Games.Simulate`), without a query budget.
+
+## Main definitions
+
+None.
+
+## Main results
+
+* `ProbComp.expect_simulate_rel`: implementations on related states simulate alike.
+* `ProbComp.prob_simulate_rel`: events on the output have the same probability, so games that
+  return a bit computed from the output have the same acceptance probability.
+* `ProbComp.expect_sample_rel`: a call that draws one uniform sample meets the hypothesis of
+  `expect_simulate_rel` when a bijection of the samples matches the answers and relates the new
+  states.
+
+## References
+
+* [BGZ09] G. Barthe, B. Grégoire, S. Zanella Béguelin, *Formal Certification of Code-Based
+  Cryptographic Proofs*, POPL 2009.
+* [Sho04] V. Shoup, *Sequences of Games: A Tool for Taming Complexity in Security Proofs*,
+  Cryptology ePrint Archive 2004/332, revision of 18 January 2006.
+-/
+
+namespace TCSlib.Cryptography.Games
+
+namespace ProbComp
+
+variable {ι : Type} {spec : OracleSpec ι} {σ τ α : Type}
+
+/-- **Implementations on related states simulate alike.** Let `impl₀` keep states in `σ` and
+`impl₁` in `τ`, related by `R : σ → τ → Prop`. Suppose that every call from related states
+`R s t` gives the same expectation to any function `g₀` of the answer and the new `σ`-state and
+any function `g₁` of the answer and the new `τ`-state that agree at equal answers and related
+states:
+`(∀ y s' t', R s' t' → g₀ (y, s') = g₁ (y, t')) → 𝔼[g₀] (impl₀ i x s) = 𝔼[g₁] (impl₁ i x t)`.
+Then from related states the simulations of every computation `c` do the same for functions of
+the output and the final state: if `R s t`, and `G₀ (a, s') = G₁ (a, t')` whenever `R s' t'`,
+then `𝔼[G₀] (simulate impl₀ c s) = 𝔼[G₁] (simulate impl₁ c t)`.
+
+The conclusion has the form of [BGZ09, §4.1, lemma (=⟦⟧)]: runs from related states give equal
+expectations to test functions that agree along the relation. The relation is carried as pre-
+and postcondition of every call, as the invariant `φ` of [BGZ09, §4.2, ⊨_φ] (judgments in the
+sense of [BGZ09, §4.1, Def. 5]). The computation `c` is an arbitrary context that reaches the
+two implementations only through its oracle calls, like a well-formed adversary, which is free
+to call oracles [BGZ09, §3.4]; [BGZ09, §5.2, Lemma 1] proves an equivalence inside an arbitrary
+context, and §5.2 applies it to replace one oracle by another. A run of `c` against `impl₁` in
+place of `impl₀` is a bridging step, `Pr[S_i] = Pr[S_{i+1}]` [Sho04, §1.1, bridging steps], as
+in the replacement of a random function by a lazily tabulating oracle [Sho04, §4.2, Game 2].
+
+**Deviation:** [BGZ09] states no rule for adversary calls with a relational invariant. This lemma
+generalizes its `(=⟦⟧)` and `⊨_φ` (§4.1–§4.2) to oracle simulations whose states are related by
+an invariant, in the arbitrary-context style of §5.2. The per-call hypothesis (equal
+expectations of test functions that agree along `R`) is the library's formulation.
+
+**Proof sketch.** Induction on `c`, generalizing the two states. At a return `a`, `R s t` gives
+`G₀ (a, s) = G₁ (a, t)`. At a query, both sides are the expectation over the call of the
+continuation's expectation (`simulate_query`, `expect_bind`); by the induction hypothesis the two
+continuation values agree at equal answers and related new states, so the hypothesis on the call
+equates them. -/
+theorem expect_simulate_rel (impl₀ : QueryImpl spec σ unifSpec)
+    (impl₁ : QueryImpl spec τ unifSpec) (R : σ → τ → Prop)
+    (h : ∀ i x s t, R s t → ∀ (g₀ : spec.rng i × σ → ℝ) (g₁ : spec.rng i × τ → ℝ),
+      (∀ y s' t', R s' t' → g₀ (y, s') = g₁ (y, t')) →
+        expect (impl₀ i x s) g₀ = expect (impl₁ i x t) g₁)
+    (c : OracleComp spec α) (G₀ : α × σ → ℝ) (G₁ : α × τ → ℝ)
+    (hG : ∀ a s' t', R s' t' → G₀ (a, s') = G₁ (a, t')) {s : σ} {t : τ} (hst : R s t) :
+    expect (simulate impl₀ c s) G₀ = expect (simulate impl₁ c t) G₁ := by
+  sorry
+
+/-- **Events on the output, from related states:** under the hypothesis of
+`expect_simulate_rel`, from related states `R s t` every event `P` on the output of `c` has the
+same probability under the two simulations:
+`Pr[P (simulate impl₀ c s).1] = Pr[P (simulate impl₁ c t).1]`. For a game that returns a bit
+computed from the output this equates the acceptance probabilities (`accept_eq`): a bridging
+step [Sho04, §1.1, bridging steps].
+
+**Proof sketch.** Both probabilities are expectations of the indicator of `P` on the output
+(`prob_eq_expect`); the two indicators agree at equal outputs whatever the final states, so
+`expect_simulate_rel` equates them. -/
+theorem prob_simulate_rel (impl₀ : QueryImpl spec σ unifSpec)
+    (impl₁ : QueryImpl spec τ unifSpec) (R : σ → τ → Prop)
+    (h : ∀ i x s t, R s t → ∀ (g₀ : spec.rng i × σ → ℝ) (g₁ : spec.rng i × τ → ℝ),
+      (∀ y s' t', R s' t' → g₀ (y, s') = g₁ (y, t')) →
+        expect (impl₀ i x s) g₀ = expect (impl₁ i x t) g₁)
+    (c : OracleComp spec α) (P : α → Prop) {s : σ} {t : τ} (hst : R s t) :
+    prob (simulate impl₀ c s) (fun p => P p.1) = prob (simulate impl₁ c t) (fun p => P p.1) := by
+  classical
+  rw [prob_eq_expect, prob_eq_expect]
+  exact expect_simulate_rel impl₀ impl₁ R h c _ _ (fun _ _ _ _ => rfl) hst
+
+/-- **A sampling call, coupled by a bijection:** let `c₀` draw `u ∈ U` and return `f₀ u`, and
+`c₁` draw `v ∈ V` and return `f₁ v`. If a bijection `e : U ≃ V` gives equal answers and related
+states, `(f₀ u).1 = (f₁ (e u)).1` and `R (f₀ u).2 (f₁ (e u)).2`, then `c₀` and `c₁` give the same
+expectation to any `g₀`, `g₁` that agree at equal answers and related states,
+`𝔼[g₀] c₀ = 𝔼[g₁] c₁`: the hypothesis of `expect_simulate_rel` for such a call.
+
+**Proof sketch.** Both sides are uniform averages (`expect_bind`, `expect_pure`); reindex the
+average over `V` along `e` (`expect_sample_equiv`) and compare the two averages pointwise. -/
+theorem expect_sample_rel {U V β : Type} [Fintype U] [Nonempty U] [Fintype V] [Nonempty V]
+    (R : σ → τ → Prop) (e : U ≃ V) (f₀ : U → β × σ) (f₁ : V → β × τ)
+    (hf : ∀ u, (f₀ u).1 = (f₁ (e u)).1 ∧ R (f₀ u).2 (f₁ (e u)).2)
+    (g₀ : β × σ → ℝ) (g₁ : β × τ → ℝ) (hg : ∀ y s' t', R s' t' → g₀ (y, s') = g₁ (y, t')) :
+    expect ((sample U).bind fun u => .pure (f₀ u)) g₀ =
+      expect ((sample V).bind fun v => .pure (f₁ v)) g₁ := by
+  sorry
+
+end ProbComp
+
+end TCSlib.Cryptography.Games

## ===== pr352.diff.txt (this pack) =====

diff --git a/TCSlib/Cryptography/Pairing/Group.lean b/TCSlib/Cryptography/Pairing/Group.lean
index b6464ece3..54e63b263 100644
--- a/TCSlib/Cryptography/Pairing/Group.lean
+++ b/TCSlib/Cryptography/Pairing/Group.lean
@@ -60,6 +60,9 @@ only by the results whose reductions compute in the group.
 * `BilinearGroup.exists_pow_eq` — every element of `G^*` generates `G`.
 * `BilinearGroup.pair_ne_one` — every element of `G^*` pairs non-trivially with itself.
 * `BilinearGroup.pow_val_bijective` — `a ↦ e(g, g)^a` is a bijection `Z_p → G_1` for `g ∈ G^*`.
+* `BilinearGroup.pow_val_add` — exponents add in `Z_p`: `x^{(a+b).val} = x^{a.val} x^{b.val}`.
+* `BilinearGroup.pow_val_neg` — negating an exponent inverts: `x^{(-a).val} = (x^{a.val})⁻¹`.
+* `BilinearGroup.pow_val_bijective_of_ne_one` — `a ↦ g^a` is a bijection `Z_p → G` for `g ∈ G^*`.
 
 ## References
 
@@ -231,6 +234,30 @@ theorem pow_val_bijective {x : B.G} (hx : x ≠ 1) :
   rw [ho] at h
   exact Nat.ModEq.eq_of_lt_of_lt h (ZMod.val_lt a) (ZMod.val_lt b)
 
+/-- **The additive exponent law in `G`**: exponents of `G` add in `Z_p`,
+`x ^ (a + b).val = x ^ a.val * x ^ b.val` for `a, b ∈ Z_p`. -/
+theorem pow_val_add (x : B.G) (a b : ZMod B.order) :
+    x ^ (a + b).val = x ^ a.val * x ^ b.val := by
+  rw [ZMod.val_add, ← pow_add, ← Nat.mod_add_div (a.val + b.val) B.order, pow_add, pow_mul,
+    B.pow_order, one_pow, mul_one, Nat.mod_add_div]
+
+/-- **The negation exponent law in `G`**: negating an exponent in `Z_p` inverts the power,
+`x ^ (-a).val = (x ^ a.val)⁻¹` for `a ∈ Z_p`. -/
+theorem pow_val_neg (x : B.G) (a : ZMod B.order) : x ^ (-a).val = (x ^ a.val)⁻¹ := by
+  rw [eq_inv_iff_mul_eq_one, ← B.pow_val_add, neg_add_cancel, ZMod.val_zero, pow_zero]
+
+/-- **`a ↦ g^a` is a bijection `Z_p → G`** for every `g ∈ G^*`: `g ≠ 1` generates `G`, so
+`Function.Bijective fun a : ZMod B.order => g ^ a.val` (the identification `Z_p ≃ G` of the
+proofs, as an `Equiv` by `Equiv.ofBijective`). -/
+theorem pow_val_bijective_of_ne_one {g : B.G} (hg : g ≠ 1) :
+    Function.Bijective fun a : ZMod B.order => g ^ a.val := by
+  have ho : orderOf g = B.order := orderOf_eq_prime (B.pow_order _) hg
+  rw [Fintype.bijective_iff_injective_and_card]
+  refine ⟨fun a b hab => ZMod.val_injective _ ?_, by rw [ZMod.card, B.card_G]⟩
+  have h := pow_eq_pow_iff_modEq.1 hab
+  rw [ho] at h
+  exact Nat.ModEq.eq_of_lt_of_lt h (ZMod.val_lt a) (ZMod.val_lt b)
+
 end BilinearGroup
 
 /-- A **bilinear group generator**: a PPT `Gen(1^κ)` whose output, the *description* `d` of the

## ===== pr365.diff.txt (this pack) =====

diff --git a/TCSlib/Cryptography/Pairing/Group.lean b/TCSlib/Cryptography/Pairing/Group.lean
index 54e63b263..f9eb3af4f 100644
--- a/TCSlib/Cryptography/Pairing/Group.lean
+++ b/TCSlib/Cryptography/Pairing/Group.lean
@@ -63,6 +63,8 @@ only by the results whose reductions compute in the group.
 * `BilinearGroup.pow_val_add` — exponents add in `Z_p`: `x^{(a+b).val} = x^{a.val} x^{b.val}`.
 * `BilinearGroup.pow_val_neg` — negating an exponent inverts: `x^{(-a).val} = (x^{a.val})⁻¹`.
 * `BilinearGroup.pow_val_bijective_of_ne_one` — `a ↦ g^a` is a bijection `Z_p → G` for `g ∈ G^*`.
+* `pow_val_bijective_of_prime_card` — `a ↦ g^a` is a bijection `Z_p → M` for `g ≠ 1` in any finite
+  group `M` of prime order `p` (the generic form of the two bijections above).
 
 ## References
 
@@ -136,6 +138,27 @@ structure BilinearGroup (wG wT : ℕ) where
 attribute [instance] BilinearGroup.commGroupG BilinearGroup.commGroupGT BilinearGroup.fintypeG
   BilinearGroup.fintypeGT BilinearGroup.decEqG BilinearGroup.decEqGT
 
+/-- **`a ↦ g^a` is a bijection `Z_p → M`** for every `g ≠ 1` in a finite group `M` of prime order
+`p`: if `|M| = p` is prime and `g ≠ 1`, then `Function.Bijective fun a : ZMod p => g ^ a.val`.
+The one statement behind `BilinearGroup.pow_val_bijective` (on `G_T`) and
+`BilinearGroup.pow_val_bijective_of_ne_one` (on `G`).
+
+Glue lemma, with no counterpart in [BB04]: elementary group theory, assembled from Mathlib
+(`orderOf_eq_prime`, `pow_injOn_Iio_orderOf`). Mathlib's closest statement,
+`IsCyclic.unique_zpow_zmod`, gives the unique exponent in `ZMod (Fintype.card M)` of each element
+for a generator `g`, not this bijectivity on `ZMod p`.
+
+**Proof sketch.** By Lagrange, `g^p = 1`, so `g ≠ 1` has order exactly `p`. Hence `n ↦ g^n` is
+injective on `{0, …, p - 1}`, which contains every `a.val`, so `a ↦ g^{a.val}` is injective on
+`Z_p`. Both sides have `p` elements, so it is a bijection. -/
+theorem pow_val_bijective_of_prime_card {M : Type*} [Group M] [Fintype M] {p : ℕ}
+    [Fact p.Prime] (hM : Fintype.card M = p) {g : M} (hg : g ≠ 1) :
+    Function.Bijective fun a : ZMod p => g ^ a.val := by
+  have ho : orderOf g = p := orderOf_eq_prime (by rw [← hM]; exact pow_card_eq_one) hg
+  rw [Fintype.bijective_iff_injective_and_card]
+  refine ⟨fun a b hab => ZMod.val_injective p ?_, by rw [ZMod.card, hM]⟩
+  exact pow_injOn_Iio_orderOf (ho ▸ ZMod.val_lt a) (ho ▸ ZMod.val_lt b) hab
+
 namespace BilinearGroup
 
 variable {wG wT : ℕ} (B : BilinearGroup wG wT)
@@ -193,14 +216,12 @@ theorem pow_order_GT (y : B.GT) : y ^ B.order = 1 := by
 /-- Exponents of `G` act through `Z_p`: `x^{(ab mod p)} = (x^a)^b` read in `Z_p`, i.e.
 `x ^ (a * b).val = x ^ (a.val * b.val)` for `a, b ∈ Z_p`. -/
 theorem pow_val_mul (x : B.G) (a b : ZMod B.order) : x ^ (a * b).val = x ^ (a.val * b.val) := by
-  rw [ZMod.val_mul, ← Nat.mod_add_div (a.val * b.val) B.order, pow_add, pow_mul, B.pow_order,
-    one_pow, mul_one, Nat.mod_add_div]
+  rw [ZMod.val_mul, ← pow_mod_card x (a.val * b.val), B.card_G]
 
 /-- Exponents of `G_T` act through `Z_p`: `y ^ (a * b).val = y ^ (a.val * b.val)`. -/
 theorem pow_val_mul_GT (y : B.GT) (a b : ZMod B.order) :
     y ^ (a * b).val = y ^ (a.val * b.val) := by
-  rw [ZMod.val_mul, ← Nat.mod_add_div (a.val * b.val) B.order, pow_add, pow_mul, B.pow_order_GT,
-    one_pow, mul_one, Nat.mod_add_div]
+  rw [ZMod.val_mul, ← pow_mod_card y (a.val * b.val), B.card_GT]
 
 /-- **Non-degeneracy at every generator**: `e(x, x) ≠ 1` for every `x ∈ G^*` (from
 `e(g, g) ≠ 1` [BB04, §2.2, item 2], since every `x ∈ G^*` generates `G`).
@@ -226,20 +247,13 @@ for uniform `z ∈ Z_p` is uniform on `G_T` (the identification of [BB04, §3.1]
 `a ↦ e(x, x)^{a.val}` is injective on `Z_p`; both sides have `p` elements (`card_GT`). -/
 theorem pow_val_bijective {x : B.G} (hx : x ≠ 1) :
     Function.Bijective fun a : ZMod B.order => B.pair x x ^ a.val := by
-  have ho : orderOf (B.pair x x) = B.order :=
-    orderOf_eq_prime (B.pow_order_GT _) (B.pair_ne_one hx)
-  rw [Fintype.bijective_iff_injective_and_card]
-  refine ⟨fun a b hab => ZMod.val_injective _ ?_, by rw [ZMod.card, B.card_GT]⟩
-  have h := pow_eq_pow_iff_modEq.1 hab
-  rw [ho] at h
-  exact Nat.ModEq.eq_of_lt_of_lt h (ZMod.val_lt a) (ZMod.val_lt b)
+  exact pow_val_bijective_of_prime_card B.card_GT (B.pair_ne_one hx)
 
 /-- **The additive exponent law in `G`**: exponents of `G` add in `Z_p`,
 `x ^ (a + b).val = x ^ a.val * x ^ b.val` for `a, b ∈ Z_p`. -/
 theorem pow_val_add (x : B.G) (a b : ZMod B.order) :
     x ^ (a + b).val = x ^ a.val * x ^ b.val := by
-  rw [ZMod.val_add, ← pow_add, ← Nat.mod_add_div (a.val + b.val) B.order, pow_add, pow_mul,
-    B.pow_order, one_pow, mul_one, Nat.mod_add_div]
+  rw [ZMod.val_add, ← pow_add, ← pow_mod_card x (a.val + b.val), B.card_G]
 
 /-- **The negation exponent law in `G`**: negating an exponent in `Z_p` inverts the power,
 `x ^ (-a).val = (x ^ a.val)⁻¹` for `a ∈ Z_p`. -/
@@ -251,12 +265,7 @@ theorem pow_val_neg (x : B.G) (a : ZMod B.order) : x ^ (-a).val = (x ^ a.val)⁻
 proofs, as an `Equiv` by `Equiv.ofBijective`). -/
 theorem pow_val_bijective_of_ne_one {g : B.G} (hg : g ≠ 1) :
     Function.Bijective fun a : ZMod B.order => g ^ a.val := by
-  have ho : orderOf g = B.order := orderOf_eq_prime (B.pow_order _) hg
-  rw [Fintype.bijective_iff_injective_and_card]
-  refine ⟨fun a b hab => ZMod.val_injective _ ?_, by rw [ZMod.card, B.card_G]⟩
-  have h := pow_eq_pow_iff_modEq.1 hab
-  rw [ho] at h
-  exact Nat.ModEq.eq_of_lt_of_lt h (ZMod.val_lt a) (ZMod.val_lt b)
+  exact pow_val_bijective_of_prime_card B.card_G hg
 
 end BilinearGroup
 

## ===== TCSlib/Cryptography/Games/Relational.lean (Lean, at dfacac356ff1225aca4c900d81bbf2cabce7b499) =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Simulate
import TCSlib.Cryptography.Games.Probability

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Simulations on related states

Two implementations of the same oracles may keep states of different types: in a security proof
the real game and its simulation often record different data for the same history (for BB1, the
committed identity with a group element `h`, or with an exponent `α_1`). If a relation `R`
between the two kinds of state holds at the start, and every call from related states answers
alike and leads to related states, then the two simulations of any computation answer alike and
end in related states (`ProbComp.expect_simulate_rel`). "Alike" is measured by expectations: a
call, or a run, from related states gives the same expectation to any two functions of the
answer and the state that agree at equal answers and related states.

With one state type and `R` the equality this is `ProbComp.expect_simulate_congr`
(`Games.Hopping`); with `R s t ↔ s = f t` it is the law form of `simulate_eq_of_abs`
(`Games.Simulate`), without a query budget.

## Main definitions

None.

## Main results

* `ProbComp.expect_simulate_rel`: implementations on related states simulate alike.
* `ProbComp.prob_simulate_rel`: events on the output have the same probability, so games that
  return a bit computed from the output have the same acceptance probability.
* `ProbComp.expect_sample_rel`: a call that draws one uniform sample meets the hypothesis of
  `expect_simulate_rel` when a bijection of the samples matches the answers and relates the new
  states.

## References

* [BGZ09] G. Barthe, B. Grégoire, S. Zanella Béguelin, *Formal Certification of Code-Based
  Cryptographic Proofs*, POPL 2009.
* [Sho04] V. Shoup, *Sequences of Games: A Tool for Taming Complexity in Security Proofs*,
  Cryptology ePrint Archive 2004/332, revision of 18 January 2006.
-/

namespace TCSlib.Cryptography.Games

namespace ProbComp

variable {ι : Type} {spec : OracleSpec ι} {σ τ α : Type}

/-- **Implementations on related states simulate alike.** Let `impl₀` keep states in `σ` and
`impl₁` in `τ`, related by `R : σ → τ → Prop`. Suppose that every call from related states
`R s t` gives the same expectation to any function `g₀` of the answer and the new `σ`-state and
any function `g₁` of the answer and the new `τ`-state that agree at equal answers and related
states:
`(∀ y s' t', R s' t' → g₀ (y, s') = g₁ (y, t')) → 𝔼[g₀] (impl₀ i x s) = 𝔼[g₁] (impl₁ i x t)`.
Then from related states the simulations of every computation `c` do the same for functions of
the output and the final state: if `R s t`, and `G₀ (a, s') = G₁ (a, t')` whenever `R s' t'`,
then `𝔼[G₀] (simulate impl₀ c s) = 𝔼[G₁] (simulate impl₁ c t)`.

The conclusion has the form of [BGZ09, §4.1, lemma (=⟦⟧)]: runs from related states give equal
expectations to test functions that agree along the relation. The relation is carried as pre-
and postcondition of every call, as the invariant `φ` of [BGZ09, §4.2, ⊨_φ] (judgments in the
sense of [BGZ09, §4.1, Def. 5]). The computation `c` is an arbitrary context that reaches the
two implementations only through its oracle calls, like a well-formed adversary, which is free
to call oracles [BGZ09, §3.4]; [BGZ09, §5.2, Lemma 1] proves an equivalence inside an arbitrary
context, and §5.2 applies it to replace one oracle by another. A run of `c` against `impl₁` in
place of `impl₀` is a bridging step, `Pr[S_i] = Pr[S_{i+1}]` [Sho04, §1.1, bridging steps], as
in the replacement of a random function by a lazily tabulating oracle [Sho04, §4.2, Game 2].

**Deviation:** [BGZ09] states no rule for adversary calls with a relational invariant. This lemma
generalizes its `(=⟦⟧)` and `⊨_φ` (§4.1–§4.2) to oracle simulations whose states are related by
an invariant, in the arbitrary-context style of §5.2. The per-call hypothesis (equal
expectations of test functions that agree along `R`) is the library's formulation.

**Proof sketch.** Induction on `c`, generalizing the two states. At a return `a`, `R s t` gives
`G₀ (a, s) = G₁ (a, t)`. At a query, both sides are the expectation over the call of the
continuation's expectation (`simulate_query`, `expect_bind`); by the induction hypothesis the two
continuation values agree at equal answers and related new states, so the hypothesis on the call
equates them. -/
theorem expect_simulate_rel (impl₀ : QueryImpl spec σ unifSpec)
    (impl₁ : QueryImpl spec τ unifSpec) (R : σ → τ → Prop)
    (h : ∀ i x s t, R s t → ∀ (g₀ : spec.rng i × σ → ℝ) (g₁ : spec.rng i × τ → ℝ),
      (∀ y s' t', R s' t' → g₀ (y, s') = g₁ (y, t')) →
        expect (impl₀ i x s) g₀ = expect (impl₁ i x t) g₁)
    (c : OracleComp spec α) (G₀ : α × σ → ℝ) (G₁ : α × τ → ℝ)
    (hG : ∀ a s' t', R s' t' → G₀ (a, s') = G₁ (a, t')) {s : σ} {t : τ} (hst : R s t) :
    expect (simulate impl₀ c s) G₀ = expect (simulate impl₁ c t) G₁ := by
  sorry

/-- **Events on the output, from related states:** under the hypothesis of
`expect_simulate_rel`, from related states `R s t` every event `P` on the output of `c` has the
same probability under the two simulations:
`Pr[P (simulate impl₀ c s).1] = Pr[P (simulate impl₁ c t).1]`. For a game that returns a bit
computed from the output this equates the acceptance probabilities (`accept_eq`): a bridging
step [Sho04, §1.1, bridging steps].

**Proof sketch.** Both probabilities are expectations of the indicator of `P` on the output
(`prob_eq_expect`); the two indicators agree at equal outputs whatever the final states, so
`expect_simulate_rel` equates them. -/
theorem prob_simulate_rel (impl₀ : QueryImpl spec σ unifSpec)
    (impl₁ : QueryImpl spec τ unifSpec) (R : σ → τ → Prop)
    (h : ∀ i x s t, R s t → ∀ (g₀ : spec.rng i × σ → ℝ) (g₁ : spec.rng i × τ → ℝ),
      (∀ y s' t', R s' t' → g₀ (y, s') = g₁ (y, t')) →
        expect (impl₀ i x s) g₀ = expect (impl₁ i x t) g₁)
    (c : OracleComp spec α) (P : α → Prop) {s : σ} {t : τ} (hst : R s t) :
    prob (simulate impl₀ c s) (fun p => P p.1) = prob (simulate impl₁ c t) (fun p => P p.1) := by
  classical
  rw [prob_eq_expect, prob_eq_expect]
  exact expect_simulate_rel impl₀ impl₁ R h c _ _ (fun _ _ _ _ => rfl) hst

/-- **A sampling call, coupled by a bijection:** let `c₀` draw `u ∈ U` and return `f₀ u`, and
`c₁` draw `v ∈ V` and return `f₁ v`. If a bijection `e : U ≃ V` gives equal answers and related
states, `(f₀ u).1 = (f₁ (e u)).1` and `R (f₀ u).2 (f₁ (e u)).2`, then `c₀` and `c₁` give the same
expectation to any `g₀`, `g₁` that agree at equal answers and related states,
`𝔼[g₀] c₀ = 𝔼[g₁] c₁`: the hypothesis of `expect_simulate_rel` for such a call.

**Proof sketch.** Both sides are uniform averages (`expect_bind`, `expect_pure`); reindex the
average over `V` along `e` (`expect_sample_equiv`) and compare the two averages pointwise. -/
theorem expect_sample_rel {U V β : Type} [Fintype U] [Nonempty U] [Fintype V] [Nonempty V]
    (R : σ → τ → Prop) (e : U ≃ V) (f₀ : U → β × σ) (f₁ : V → β × τ)
    (hf : ∀ u, (f₀ u).1 = (f₁ (e u)).1 ∧ R (f₀ u).2 (f₁ (e u)).2)
    (g₀ : β × σ → ℝ) (g₁ : β × τ → ℝ) (hg : ∀ y s' t', R s' t' → g₀ (y, s') = g₁ (y, t')) :
    expect ((sample U).bind fun u => .pure (f₀ u)) g₀ =
      expect ((sample V).bind fun v => .pure (f₁ v)) g₁ := by
  sorry

end ProbComp

end TCSlib.Cryptography.Games

## ===== TCSlib/Cryptography/Games/Probability.lean (Lean, at dfacac356ff1225aca4c900d81bbf2cabce7b499) =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.OracleComp
import TCSlib.InformationTheory.FinDist

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Probabilistic computations

Randomness enters the framework as one more oracle: oracle `m` of `unifSpec` answers a uniformly
random element of `Fin (m + 1)`, and a uniform element of any nonempty finite type is obtained
through an enumeration. A *probabilistic computation* (`ProbComp`) is an oracle computation whose
only oracle is this one. Security games, once their adversary is plugged in and their oracles
implemented, are probabilistic computations.

The semantics is elementary and real-valued. The expectation of `g` over the output of a
computation is defined by recursion on the computation: a return contributes `g a`, and a sampling
step averages over its `m + 1` equally likely answers. There are no measures and no extended
reals: every computation is a finite tree with finite branching, so every probability is a finite
sum of rationals. The probability of an event is the expectation of its indicator. For a
computation with a finite output type, its output distribution is a `FinDist` of the library's
information-theory layer, so statistical distance and closeness (`EpsClose`) apply directly.

## Main definitions

* `Games.unifSpec`: the uniform-sampling oracles; `Games.ProbComp`: computations over them.
* `Games.ProbComp.sampleFin m`, `Games.ProbComp.sample T`: a uniform element of `Fin (m + 1)`, and
  of a nonempty finite type `T`.
* `Games.ProbComp.expect c g`: the expectation of `g` over the output of `c`.
* `Games.ProbComp.prob c p`: the probability that the output of `c` satisfies `p`.
* `Games.ProbComp.dist c`: the output distribution of `c`, for a finite output type.

## Main results

* `ProbComp.expect_bind`: **total expectation**; sequencing averages the continuations.
* `ProbComp.expect_sample`: sampling a finite type is the uniform average.
* `ProbComp.expect_add`, `expect_const_mul`, `expect_sum`, `expect_mono`: linearity and
  monotonicity.
* `ProbComp.prob_nonneg`, `prob_le_one`, `prob_mono`, `prob_or_le` (the union bound),
  `prob_not`, `prob_bind`.
* `ProbComp.expect_sample_equiv`, `expect_sample_comm`, `expect_sample_unique`,
  `expect_sample_update`, `expect_sample_coord`: reindexing, exchanging and resampling uniform
  samples; `expect_sub`, `abs_expect_sub_le`: subtraction and pointwise closeness.
* `ProbComp.abs_expect_sub_le_expect`: averaging a pointwise bound.
* `ProbComp.expect_expect_sample`: exchanging an expectation with a uniform sample (Fubini).

## References

* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), probabilistic computations as
  computations over the uniform-selection oracles (`OracleComp/ProbComp/Basic.lean`), and
  simulation of oracles by stateful handlers with query logging and composition (`SimSemantics/`,
  `SimSemantics/QueryImpl/Compose.lean`, `QueryTracking/LoggingOracle`).
  Uniform sampling as an oracle follows VCVio's uniform-selection oracle; the real-valued
  finite-sum semantics here is not VCVio's (which is measure-valued).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §2.1 (probabilistic algorithms; the uniform distribution over coin strings).
-/

namespace TCSlib.Cryptography.Games

open Finset TCSlib.InformationTheory

/-- The **uniform-sampling oracles**: oracle `m` takes no query and answers a uniformly random
element of `Fin (m + 1)`. [VCVio, OracleComp/ProbComp] -/
abbrev unifSpec : OracleSpec ℕ := ⟨fun _ => Unit, fun m => Fin (m + 1)⟩

/-- **Probabilistic computations**: oracle computations whose only oracles draw uniform samples.
[VCVio, OracleComp/ProbComp/Basic] -/
abbrev ProbComp := OracleComp unifSpec

namespace ProbComp

variable {α β : Type}

/-- A uniformly random element of `Fin (m + 1)`. [VCVio, OracleComp/ProbComp/Basic (uniformFin)] -/
def sampleFin (m : ℕ) : ProbComp (Fin (m + 1)) := .query m () .pure

/-- Sampling `Fin (m + 1)` is one query to the `m`-th sampling oracle:
`sampleFin m = .query m () .pure`. -/
theorem sampleFin_eq (m : ℕ) : sampleFin m = .query m () .pure := rfl

/-- A uniformly random element of the nonempty finite type `T`, through its enumeration
`Fintype.equivFin`. -/
noncomputable def sample (T : Type) [Fintype T] [Nonempty T] : ProbComp T :=
  (fun j : Fin (Fintype.card T - 1 + 1) =>
    (Fintype.equivFin T).symm (Fin.cast (Nat.sub_add_cancel Fintype.card_pos) j)) <$>
      sampleFin (Fintype.card T - 1)

/-- Sampling `T` is sampling an index below `|T|` and reading it through `Fintype.equivFin`:
`sample T = (fun j => (equivFin T).symm (Fin.cast _ j)) <$> sampleFin (|T| − 1)`. -/
theorem sample_eq (T : Type) [Fintype T] [Nonempty T] :
    sample T = (fun j : Fin (Fintype.card T - 1 + 1) =>
      (Fintype.equivFin T).symm (Fin.cast (Nat.sub_add_cancel Fintype.card_pos) j)) <$>
        sampleFin (Fintype.card T - 1) := rfl

/-- The **expectation** of `g` over the output of `c`: `g a` for a return, and the average over
the `m + 1` equally likely answers at a sampling step. -/
noncomputable def expect : ProbComp α → (α → ℝ) → ℝ
  | .pure a, g => g a
  | .query m _ k, g => ((m : ℝ) + 1)⁻¹ * ∑ j : Fin (m + 1), expect (k j) g

/-- The **probability** that the output of `c` satisfies `p`: the expectation of the indicator
of `p`. -/
noncomputable def prob (c : ProbComp α) (p : α → Prop) : ℝ := by
  classical exact expect c (fun a => if p a then 1 else 0)

/-- A return is its own expectation. -/
@[simp] theorem expect_pure (a : α) (g : α → ℝ) : expect (.pure a) g = g a := rfl

/-- A sampling step averages over its answers. -/
theorem expect_query (m : ℕ) (x : Unit) (k : Fin (m + 1) → ProbComp α) (g : α → ℝ) :
    expect (.query m x k) g = ((m : ℝ) + 1)⁻¹ * ∑ j : Fin (m + 1), expect (k j) g := rfl

/-- **Total expectation:** the expectation over `c` followed by `f` is the expectation over `c`
of the expectation over `f a`.

**Proof sketch.** Induction on `c`: a return is immediate, and at a sampling step both sides
average the same continuations. -/
theorem expect_bind (c : ProbComp α) (f : α → ProbComp β) (g : β → ℝ) :
    expect (c.bind f) g = expect c (fun a => expect (f a) g) := by
  induction c with
  | pure a => simp only [OracleComp.pure_bind, expect_pure]
  | query m x k ih => simp only [OracleComp.query_bind, expect_query, ih]

/-- The expectation over a mapped computation is the expectation of the composite. -/
theorem expect_map (h : α → β) (c : ProbComp α) (g : β → ℝ) :
    expect (h <$> c) g = expect c (fun a => g (h a)) := by
  rw [OracleComp.map_eq_bind, expect_bind]; rfl

/-- Sampling `Fin (m + 1)` is the uniform average over it. -/
theorem expect_sampleFin (m : ℕ) (g : Fin (m + 1) → ℝ) :
    expect (sampleFin m) g = ((m : ℝ) + 1)⁻¹ * ∑ j, g j := rfl

/-- Sampling a nonempty finite type is the uniform average over it.

**Proof sketch.** The sample is the image of a uniform element of `Fin |T|` under the bijection
`Fintype.equivFin`, and a sum is invariant under reindexing by a bijection. -/
theorem expect_sample (T : Type) [Fintype T] [Nonempty T] (g : T → ℝ) :
    expect (sample T) g = (Fintype.card T : ℝ)⁻¹ * ∑ t, g t := by
  have hc : Fintype.card T - 1 + 1 = Fintype.card T := Nat.sub_add_cancel Fintype.card_pos
  rw [sample, expect_map, expect_sampleFin]
  congr 1
  · congr 1
    exact_mod_cast hc
  · exact Fintype.sum_equiv ((finCongr hc).trans (Fintype.equivFin T).symm) _ _
      (fun j => by simp)

/-- Expectation is additive. -/
theorem expect_add (c : ProbComp α) (f g : α → ℝ) :
    expect c (fun a => f a + g a) = expect c f + expect c g := by
  induction c with
  | pure a => rfl
  | query m x k ih => simp only [expect_query, ih, sum_add_distrib, mul_add]

/-- Expectation commutes with scaling by a constant. -/
theorem expect_const_mul (c : ProbComp α) (r : ℝ) (f : α → ℝ) :
    expect c (fun a => r * f a) = r * expect c f := by
  induction c with
  | pure a => rfl
  | query m x k ih =>
    simp only [expect_query, ih, ← mul_sum]
    ring

/-- The expectation of a constant is that constant. -/
theorem expect_const (c : ProbComp α) (r : ℝ) : expect c (fun _ => r) = r := by
  induction c with
  | pure a => rfl
  | query m x k ih =>
    simp only [expect_query, ih, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (m : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp

/-- Expectation commutes with finite sums. -/
theorem expect_sum {ι : Type} (c : ProbComp α) (s : Finset ι) (f : ι → α → ℝ) :
    expect c (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, expect c (f i) := by
  induction c with
  | pure a => rfl
  | query m x k ih =>
    simp only [expect_query, ih, mul_sum]
    exact sum_comm

/-- Expectation is monotone. -/
theorem expect_mono (c : ProbComp α) {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    expect c f ≤ expect c g := by
  induction c with
  | pure a => exact h a
  | query m x k ih =>
    simp only [expect_query]
    exact mul_le_mul_of_nonneg_left (sum_le_sum fun j _ => ih j) (by positivity)

/-- The expectation of a nonnegative function is nonnegative. -/
theorem expect_nonneg (c : ProbComp α) {f : α → ℝ} (h : ∀ a, 0 ≤ f a) : 0 ≤ expect c f := by
  simpa [expect_const] using expect_mono c (f := fun _ => 0) h

/-! ### Probabilities of events -/

/-- The probability of `p` is the expectation of its indicator (any decidability instance). -/
theorem prob_eq_expect (c : ProbComp α) (p : α → Prop) [DecidablePred p] :
    prob c p = expect c (fun a => if p a then 1 else 0) := by
  unfold prob
  congr 1
  funext a
  congr 1

/-- A return satisfies `p` with probability one or zero. -/
theorem prob_pure (a : α) (p : α → Prop) [Decidable (p a)] :
    prob (.pure a) p = if p a then 1 else 0 := by
  classical
  rw [prob_eq_expect, expect_pure]
  congr 1

/-- **Total probability:** the probability over `c` followed by `f` is the expectation over `c`
of the probability over `f a`. -/
theorem prob_bind (c : ProbComp α) (f : α → ProbComp β) (p : β → Prop) :
    prob (c.bind f) p = expect c (fun a => prob (f a) p) := by
  classical
  simp only [prob_eq_expect, expect_bind]

/-- Probabilities are nonnegative. -/
theorem prob_nonneg (c : ProbComp α) (p : α → Prop) : 0 ≤ prob c p := by
  classical
  rw [prob_eq_expect]
  exact expect_nonneg c fun a => by split_ifs <;> norm_num

/-- Probabilities are at most one. -/
theorem prob_le_one (c : ProbComp α) (p : α → Prop) : prob c p ≤ 1 := by
  classical
  rw [prob_eq_expect]
  calc expect c (fun a => if p a then (1 : ℝ) else 0) ≤ expect c (fun _ => 1) :=
        expect_mono c fun a => by split_ifs <;> norm_num
    _ = 1 := expect_const c 1

/-- An event implied by another has at least its probability. -/
theorem prob_mono (c : ProbComp α) {p q : α → Prop} (h : ∀ a, p a → q a) :
    prob c p ≤ prob c q := by
  classical
  rw [prob_eq_expect, prob_eq_expect]
  exact expect_mono c fun a => by
    by_cases hp : p a
    · simp [hp, h a hp]
    · simp only [hp, if_false]; split_ifs <;> norm_num

/-- Events that agree on every output have the same probability. -/
theorem prob_congr (c : ProbComp α) {p q : α → Prop} (h : ∀ a, p a ↔ q a) :
    prob c p = prob c q :=
  le_antisymm (prob_mono c fun a => (h a).1) (prob_mono c fun a => (h a).2)

/-- **The union bound** for two events. -/
theorem prob_or_le (c : ProbComp α) (p q : α → Prop) :
    prob c (fun a => p a ∨ q a) ≤ prob c p + prob c q := by
  classical
  rw [prob_eq_expect, prob_eq_expect, prob_eq_expect, ← expect_add]
  exact expect_mono c fun a => by
    by_cases hp : p a <;> by_cases hq : q a <;> simp [hp, hq]

/-- The complement of an event has one minus its probability. -/
theorem prob_not (c : ProbComp α) (p : α → Prop) :
    prob c (fun a => ¬ p a) = 1 - prob c p := by
  classical
  rw [prob_eq_expect, prob_eq_expect, eq_sub_iff_add_eq, ← expect_add]
  calc expect c (fun a => (if ¬ p a then (1 : ℝ) else 0) + if p a then 1 else 0)
      = expect c (fun _ => 1) := by
        congr 1; funext a; by_cases hp : p a <;> simp [hp]
    _ = 1 := expect_const c 1

/-! ### Output distributions -/

/-- The **output distribution** of a computation with a finite output type: the probability of
each outcome. -/
noncomputable def dist [Fintype α] [DecidableEq α] (c : ProbComp α) : FinDist α where
  prob a := prob c (· = a)
  nonneg a := prob_nonneg c _
  sum_prob := by
    simp only [prob_eq_expect]
    rw [← expect_sum]
    calc expect c (fun x => ∑ a, if x = a then (1 : ℝ) else 0) = expect c (fun _ => 1) := by
          congr 1; funext x; simp
      _ = 1 := expect_const c 1

/-- The output distribution gives each outcome its probability. -/
theorem dist_apply [Fintype α] [DecidableEq α] (c : ProbComp α) (a : α) :
    dist c a = prob c (· = a) := rfl

/-! ### Sampling identities -/

section Sampling

variable {β : Type}

/-- **Reindexing a sample by an equivalence:** `𝔼_{a ← α} g (e a) = 𝔼_{b ← β} g b`.

**Proof sketch.** Both are uniform averages (`expect_sample`); the cardinalities agree
(`Fintype.card_congr`) and the sums agree by reindexing along `e` (`Equiv.sum_comp`). -/
theorem expect_sample_equiv [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] (e : α ≃ β)
    (g : β → ℝ) : expect (sample α) (fun a => g (e a)) = expect (sample β) g := by
  rw [expect_sample, expect_sample, Fintype.card_congr e, Equiv.sum_comp e g]

/-- **Independent samples commute:**
`𝔼_{a ← α} 𝔼_{b ← β} g a b = 𝔼_{b ← β} 𝔼_{a ← α} g a b`.

**Proof sketch.** Both sides are the double uniform average (`expect_sample`); exchange the two
finite sums (`Finset.sum_comm`). -/
theorem expect_sample_comm [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (g : α → β → ℝ) :
    (expect (sample α) fun a => expect (sample β) fun b => g a b) =
      expect (sample β) fun b => expect (sample α) fun a => g a b := by
  simp only [expect_sample, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun b _ => sum_congr rfl fun a _ => ?_
  ring

/-- **Fubini for a uniform sample:** `𝔼_c[𝔼_{t ← T}[h a t]] = 𝔼_{t ← T}[𝔼_c[h a t]]`.

**Proof sketch.** The inner sample is a uniform average (`expect_sample`); pull the constant
factor and the finite sum out of the outer expectation (`expect_const_mul`, `expect_sum`). -/
theorem expect_expect_sample (c : ProbComp α) (T : Type) [Fintype T] [Nonempty T]
    (h : α → T → ℝ) :
    expect c (fun a => expect (sample T) (h a)) =
      expect (sample T) fun t => expect c fun a => h a t := by
  simp only [expect_sample]
  rw [expect_const_mul, expect_sum]

/-- **Sampling a singleton type** returns its element: `𝔼_{a ← α} g a = g default`. -/
theorem expect_sample_unique [Fintype α] [Unique α] (g : α → ℝ) :
    expect (sample α) g = g default := by
  rw [expect_sample, Fintype.card_unique, Fintype.sum_unique]
  simp

/-- Expectation is subtractive: `𝔼[f − g] = 𝔼 f − 𝔼 g`. -/
theorem expect_sub (c : ProbComp α) (f g : α → ℝ) :
    expect c (fun a => f a - g a) = expect c f - expect c g := by
  have h := expect_add c f (fun a => -1 * g a)
  rw [expect_const_mul] at h
  simp only [neg_one_mul, ← sub_eq_add_neg] at h
  exact h

/-- **Resampling one coordinate of a uniform tuple leaves it uniform**:
`𝔼_{v} 𝔼_{b} f (update v j b) = 𝔼_{v} f v`.

**Proof sketch.** The map `(v, b) ↦ (update v j b, v j)` is an involution of `(ι → β) × β`
(`Function.update_idem`, `Function.update_eq_self`). Written as uniform averages
(`expect_sample`), the double sum of `f (update v j b)` over pairs is the sum of `f v` over pairs
reindexed along it (`Fintype.sum_prod_type'`, `Equiv.sum_comp`), which is `|β|` times the sum of
`f`. -/
theorem expect_sample_update {ι : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [Nonempty β]
    (j : ι) (f : (ι → β) → ℝ) :
    (expect (sample (ι → β)) fun v => expect (sample β) fun b => f (Function.update v j b)) =
      expect (sample (ι → β)) f := by
  let e : (ι → β) × β ≃ (ι → β) × β :=
    { toFun := fun p => (Function.update p.1 j p.2, p.1 j)
      invFun := fun p => (Function.update p.1 j p.2, p.1 j)
      left_inv := fun p => by
        simp only [Function.update_self, Function.update_idem, Function.update_eq_self]
      right_inv := fun p => by
        simp only [Function.update_self, Function.update_idem, Function.update_eq_self] }
  have hpair : (∑ v : ι → β, ∑ b : β, f (Function.update v j b)) =
      ∑ v : ι → β, ∑ _b : β, f v := by
    rw [← Fintype.sum_prod_type' (fun v b => f (Function.update v j b)),
      ← Fintype.sum_prod_type' (fun v (_ : β) => f v)]
    exact Equiv.sum_comp e (fun p => f p.1)
  have hβ : (Fintype.card β : ℝ) ≠ 0 := by positivity
  simp only [expect_sample, ← mul_sum]
  rw [hpair]
  simp only [sum_const, card_univ, nsmul_eq_mul, ← mul_sum]
  rw [inv_mul_cancel_left₀ hβ]

/-- **One coordinate of a uniform tuple, sampled apart:** if `F r T` does not depend on the
coordinate `j` of `T`, then `𝔼_{T} F (T j) T = 𝔼_{r} 𝔼_{T} F r T`.

**Proof sketch.** Exchange the samples on the right (`expect_sample_comm`) and resample the
coordinate `j` on the left (`expect_sample_update`); pointwise,
`F ((update T j r) j) (update T j r) = F r T` (`Function.update_self` and the hypothesis). -/
theorem expect_sample_coord {ι : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [Nonempty β]
    (j : ι) (F : β → (ι → β) → ℝ) (hF : ∀ r r' T, F r (Function.update T j r') = F r T) :
    expect (sample (ι → β)) (fun T => F (T j) T) =
      expect (sample β) fun r => expect (sample (ι → β)) fun T => F r T := by
  rw [expect_sample_comm, ← expect_sample_update j (fun T => F (T j) T)]
  refine congrArg _ (funext fun T => congrArg _ (funext fun r => ?_))
  rw [Function.update_self, hF]

/-- Expectations of functions `ε`-close at every point are `ε`-close:
`(∀ x, |f x - g x| ≤ ε) → |𝔼_c f - 𝔼_c g| ≤ ε`. -/
theorem abs_expect_sub_le (c : ProbComp α) {f g : α → ℝ} {ε : ℝ}
    (h : ∀ x, |f x - g x| ≤ ε) : |expect c f - expect c g| ≤ ε := by
  have h1 : expect c f ≤ expect c g + ε :=
    calc expect c f ≤ expect c (fun x => g x + ε) :=
          expect_mono c fun x => by linarith [(abs_le.1 (h x)).2]
      _ = expect c g + ε := by rw [expect_add c g (fun _ => ε), expect_const]
  have h2 : expect c g ≤ expect c f + ε :=
    calc expect c g ≤ expect c (fun x => f x + ε) :=
          expect_mono c fun x => by linarith [(abs_le.1 (h x)).1]
      _ = expect c f + ε := by rw [expect_add c f (fun _ => ε), expect_const]
  rw [abs_le]
  constructor <;> linarith

/-- **Averaging a pointwise bound:** expectations of functions within a pointwise bound of each
other are within the expectation of the bound:
`(∀ x, |f x - g x| ≤ h x) → |𝔼_c f - 𝔼_c g| ≤ 𝔼_c h`. -/
theorem abs_expect_sub_le_expect (c : ProbComp α) {f g h : α → ℝ}
    (hb : ∀ x, |f x - g x| ≤ h x) : |expect c f - expect c g| ≤ expect c h := by
  rw [← expect_sub, abs_le]
  constructor
  · have := expect_mono c fun x => (neg_le_of_abs_le (hb x))
    rw [show (fun x => -h x) = fun x => (-1) * h x from funext fun x => by ring,
      expect_const_mul] at this
    linarith
  · exact expect_mono c fun x => le_of_abs_le (hb x)

end Sampling

end ProbComp

end TCSlib.Cryptography.Games

## ===== TCSlib/Cryptography/Pairing/Group.lean (Lean, at 5eaddd171bceccee917929e7f319ff9202994c59) =====

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
* `BilinearGroup.pow_val_add` — exponents add in `Z_p`: `x^{(a+b).val} = x^{a.val} x^{b.val}`.
* `BilinearGroup.pow_val_neg` — negating an exponent inverts: `x^{(-a).val} = (x^{a.val})⁻¹`.
* `BilinearGroup.pow_val_bijective_of_ne_one` — `a ↦ g^a` is a bijection `Z_p → G` for `g ∈ G^*`.
* `pow_val_bijective_of_prime_card` — `a ↦ g^a` is a bijection `Z_p → M` for `g ≠ 1` in any finite
  group `M` of prime order `p` (the generic form of the two bijections above).

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

/-- **`a ↦ g^a` is a bijection `Z_p → M`** for every `g ≠ 1` in a finite group `M` of prime order
`p`: if `|M| = p` is prime and `g ≠ 1`, then `Function.Bijective fun a : ZMod p => g ^ a.val`.
The one statement behind `BilinearGroup.pow_val_bijective` (on `G_T`) and
`BilinearGroup.pow_val_bijective_of_ne_one` (on `G`).

Glue lemma, with no counterpart in [BB04]: elementary group theory, assembled from Mathlib
(`orderOf_eq_prime`, `pow_injOn_Iio_orderOf`). Mathlib's closest statement,
`IsCyclic.unique_zpow_zmod`, gives the unique exponent in `ZMod (Fintype.card M)` of each element
for a generator `g`, not this bijectivity on `ZMod p`.

**Proof sketch.** By Lagrange, `g^p = 1`, so `g ≠ 1` has order exactly `p`. Hence `n ↦ g^n` is
injective on `{0, …, p - 1}`, which contains every `a.val`, so `a ↦ g^{a.val}` is injective on
`Z_p`. Both sides have `p` elements, so it is a bijection. -/
theorem pow_val_bijective_of_prime_card {M : Type*} [Group M] [Fintype M] {p : ℕ}
    [Fact p.Prime] (hM : Fintype.card M = p) {g : M} (hg : g ≠ 1) :
    Function.Bijective fun a : ZMod p => g ^ a.val := by
  have ho : orderOf g = p := orderOf_eq_prime (by rw [← hM]; exact pow_card_eq_one) hg
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun a b hab => ZMod.val_injective p ?_, by rw [ZMod.card, hM]⟩
  exact pow_injOn_Iio_orderOf (ho ▸ ZMod.val_lt a) (ho ▸ ZMod.val_lt b) hab

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
  rw [ZMod.val_mul, ← pow_mod_card x (a.val * b.val), B.card_G]

/-- Exponents of `G_T` act through `Z_p`: `y ^ (a * b).val = y ^ (a.val * b.val)`. -/
theorem pow_val_mul_GT (y : B.GT) (a b : ZMod B.order) :
    y ^ (a * b).val = y ^ (a.val * b.val) := by
  rw [ZMod.val_mul, ← pow_mod_card y (a.val * b.val), B.card_GT]

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
  exact pow_val_bijective_of_prime_card B.card_GT (B.pair_ne_one hx)

/-- **The additive exponent law in `G`**: exponents of `G` add in `Z_p`,
`x ^ (a + b).val = x ^ a.val * x ^ b.val` for `a, b ∈ Z_p`. -/
theorem pow_val_add (x : B.G) (a b : ZMod B.order) :
    x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  rw [ZMod.val_add, ← pow_add, ← pow_mod_card x (a.val + b.val), B.card_G]

/-- **The negation exponent law in `G`**: negating an exponent in `Z_p` inverts the power,
`x ^ (-a).val = (x ^ a.val)⁻¹` for `a ∈ Z_p`. -/
theorem pow_val_neg (x : B.G) (a : ZMod B.order) : x ^ (-a).val = (x ^ a.val)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← B.pow_val_add, neg_add_cancel, ZMod.val_zero, pow_zero]

/-- **`a ↦ g^a` is a bijection `Z_p → G`** for every `g ∈ G^*`: `g ≠ 1` generates `G`, so
`Function.Bijective fun a : ZMod B.order => g ^ a.val` (the identification `Z_p ≃ G` of the
proofs, as an `Equiv` by `Equiv.ofBijective`). -/
theorem pow_val_bijective_of_ne_one {g : B.G} (hg : g ≠ 1) :
    Function.Bijective fun a : ZMod B.order => g ^ a.val := by
  exact pow_val_bijective_of_prime_card B.card_G hg

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

## ===== briefs/pairings/fills/bb1-sim/design-r1.md (records, at ab17e37feb00a677d69f6abd5ff7e427e3b9ef3c) =====

# Fill `bb1-sim` (T2, T3): design round 1, a relational simulation lemma in `Games`

This is a design note for the statement phase of fill unit `bb1-sim`, which covers T2 `bb1_sim_real`
and T3 `bb1_sim_random`. It was prepared read-only: no Lean was run, and nothing was committed. Every
Lean line number refers to the pins below and was read with `git show <pin>:<path>`.

| Pin | Value |
|---|---|
| #331 head (statements; Gate 40 closed) | `9e7a96481785d6cac4dea3b2e990c49ac278b060` |
| T4 branch `fill/pairings-bb1-machine` (T4 still `sorry`; the 7 readers are not in it yet) | `7c0a55e0239c14786612d0cd4462e64238543ca1` |
| Records commit with the ruling (decision log, 2026-11-16, "Rulings (Seyoon) … (2) T2/T3 design") | `bf08dbfa3a057a3b41d20f6dbede3066bc5e6660` |
| Records tip when this note was written (`TCSlib/Cryptography/Games/` is identical to #331's) | `a0e3148309dbc3bf836d46745b707724599541f0` |
| Gate 40 note | `briefs/pairings/gates/40-pairings-statements/findings/gate40-pairings-statements-findings.md`, § "Truth and sufficiency", the T2 paragraph |

**The ruling (Seyoon, 2026-11-16).** A public relational simulation lemma goes into `Games`. It
relates two handlers whose state types `σ` and `τ` are linked by an invariant `R : σ → τ → Prop`.
Each oracle call keeps the invariant, and the answers have equal laws. The lemma is statement-gated
together with the `bb1-sim` fill, and it is preferred to a combined state kept local to the fill.

**Summary of the proposal.**
* A new module, `TCSlib/Cryptography/Games/Relational.lean`, with three statements:
  * `ProbComp.expect_simulate_rel` (the target);
  * `ProbComp.prob_simulate_rel` (the event and acceptance corollary);
  * `ProbComp.expect_sample_rel` (discharges one call that samples once, coupled by a bijection).
* T2 uses `expect_simulate_rel` twice, together with the existing `Games.expect_simulate_eager`
  twice. T3 needs only the existing single-state `ProbComp.expect_simulate_congr`, after one
  eager/lazy step.
* The main practical risk is not the lemma. It is the set of readers that T2 needs in the frozen
  `Defs.lean` and `BonehBoyen.lean` (§3.3, §5). A probe should settle that set before the statement
  PR.

---

## 1. The `Games` API this builds on (at `9e7a9648`)

All paths below are relative to `TCSlib/Cryptography/`.

### 1.1 Types

| Name (full namespace `TCSlib.Cryptography.Games`) | What it is | File:line |
|---|---|---|
| `OracleSpec ι` | structure with fields `dom rng : ι → Type` | `Games/OracleComp.lean:74` |
| `OracleComp spec α` | inductive type: `pure : α → _`, `query (i : ι) (x : spec.dom i) (k : spec.rng i → OracleComp spec α)` | `Games/OracleComp.lean:84` |
| `OracleComp.AllOutputs P c` | every possible output satisfies `P` | `Games/OracleComp.lean:292` |
| `unifSpec : OracleSpec ℕ` | `abbrev`, `⟨fun _ => Unit, fun m => Fin (m + 1)⟩` | `Games/Probability.lean:73` |
| `ProbComp` | `abbrev ProbComp := OracleComp unifSpec` | `Games/Probability.lean:77` |
| `ProbComp.sample T` | uniform element of a nonempty finite type | `Games/Probability.lean:92` |
| `ProbComp.expect : ProbComp α → (α → ℝ) → ℝ` | expectation | `Games/Probability.lean:106` |
| `ProbComp.prob c p` | `expect` of the indicator | `Games/Probability.lean:112` |
| `QueryImpl spec σ spec'` | `abbrev`, `∀ i, spec.dom i → σ → OracleComp spec' (spec.rng i × σ)`. Notation under R-04-4. | `Games/Simulate.lean:73` |
| `simulate (impl : QueryImpl spec σ spec') : OracleComp spec α → σ → OracleComp spec' (α × σ)` | defined by recursion: `pure a, s ↦ pure (a, s)`; `query i x k, s ↦ (impl i x s).bind fun ys => simulate impl (k ys.1) ys.2` | `Games/Simulate.lean:83` |
| `accept G := prob G (· = true)`, `advantage G₀ G₁ := abs (accept G₀ - accept G₁)` | acceptance probability and advantage of games | `Games/Advantage.lean:63`, `:72` |
| `bitSpec din dout` | `abbrev`, `⟨fun i => Fin (din i) → Bool, fun i => Fin (dout i) → Bool⟩` | `Games/BitCodec.lean:73` |
| `NUPPT.toComp D codec n q r : OracleComp spec α` | the machine as an oracle computation | `Games/Machines.lean:221` |

**Note on names.**
* For games there is no `acceptProb`: the acceptance probability is `Games.accept`.
* `acceptProb` exists only in the concrete layer (`Foundations/Experiments.lean:72`). The bridge
  between the two is `Games.Bridge.acceptProb_eq` (`Games/Bridges/Experiments.lean:120`).
* T2's frozen sketch cites `Games.expect_simulate_congr`. The lemma's actual name is
  `Games.ProbComp.expect_simulate_congr`.

### 1.2 The two lemmas the ruling is about, verbatim

`Games/Hopping.lean:384–393`, namespace `TCSlib.Cryptography.Games.ProbComp`:

```lean
theorem expect_simulate_congr {ι : Type} {spec : OracleSpec ι} {σ α : Type}
    (impl₀ impl₁ : QueryImpl spec σ unifSpec)
    (h : ∀ i x s (g : spec.rng i × σ → ℝ), expect (impl₀ i x s) g = expect (impl₁ i x s) g)
    (c : OracleComp spec α) (s : σ) (G : α × σ → ℝ) :
    expect (simulate impl₀ c s) G = expect (simulate impl₁ c s) G
```

Here both implementations have the single state type `σ`, and both runs start from the same `s`.
This is the restriction that Gate 40 flagged.

`Games/Hopping.lean:494–503`, namespace `TCSlib.Cryptography.Games`; both T2 and T3 use it:

```lean
theorem expect_simulate_eager (O : QueryImpl spec σ unifSpec) (OE : T → QueryImpl spec σ unifSpec)
    (used : σ → Prop) (hused : ∀ t i x s, used s → OE t i x s = O i x s)
    (hstick : ∀ i x s, used s → (O i x s).AllOutputs fun p => used p.2)
    (hfresh : ∀ i x s, ¬ used s →
      (∀ t, OE t i x s = O i x s ∧ (O i x s).AllOutputs fun p => ¬ used p.2) ∨
      (O i x s = (ProbComp.sample T).bind (fun t => OE t i x s) ∧
        ∀ t, (OE t i x s).AllOutputs fun p => used p.2))
    (c : OracleComp spec α) (G : α × σ → ℝ) {s : σ} (hs : ¬ used s) :
    ProbComp.expect (simulate O c s) G =
      ProbComp.expect (ProbComp.sample T) fun t => ProbComp.expect (simulate (OE t) c s) G
```

This lemma also has one state type. It moves a one-shot sample between "drawn in advance" and
"drawn at the call that spends it".

### 1.3 Every `simulate_*` and `expect_simulate_*` lemma in `Games/`

| Lemma | Content | File:line |
|---|---|---|
| `simulate_pure`, `simulate_query` (`@[simp]`) | the two defining equations | `Games/Simulate.lean:93`, `:97` |
| `simulate_bind`, `simulate_call` | sequencing; a single call | `Games/Simulate.lean:107`, `:114` |
| `simulate_comp` | composing implementations (state `σ₁ × σ₂`) | `Games/Simulate.lean:199` |
| `simulate_withLog` | logging is conservative | `Games/Simulate.lean:241` |
| `simulate_costBoundedBy`, `simulate_costBoundedBy_once` | query cost under simulation | `Games/Simulate.lean:264`, `:290` |
| `simulate_eq_of_abs` | **two state types**, `f : σ₂ → σ₁`, exact equality of computations, every state | `Games/Simulate.lean:334` |
| `simulate_eq_of_abs_bounded` | the same, deterministic calls, with a query budget `cnt` | `Games/Simulate.lean:357` |
| `simulate_allOutputs_bad` | a sticky bad flag stays raised | `Games/Hopping.lean:179` |
| `expect_eq_until_bad`, `prob_eq_until_bad`, `identical_until_bad`, `identical_until_bad_init`, `hagree_of_eq` | the fundamental lemma; one state type | `Games/Hopping.lean:201`, `:252`, `:306`, `:343`, `:331` |
| `ProbComp.expect_simulate_congr` | equal laws per call; one state type | `Games/Hopping.lean:384` |
| `ProbComp.prob_bad_le` | per-query potential bound | `Games/Hopping.lean:403` |
| `simulate_eq_of_used` (private) | helper for the eager lemma | `Games/Hopping.lean:469` |
| `expect_simulate_eager` | one-shot coins in advance; one state type | `Games/Hopping.lean:494` |
| `simulate_castImpl_toCompOn`, `expect_simulate_castImpl_toCompOn` | transport along equal length functions | `Games/BitCodec.lean:415`, `:430` |
| `simulate_ofComp_pure`, `Bridge.simulate_eq` | query trees | `Games/Bridges/QueryTree.lean:83`, `:124` |

Supporting expectation lemmas:

| Lemma | File:line |
|---|---|
| `expect_pure` | `Games/Probability.lean:116` |
| `expect_bind` | `:127` |
| `expect_sample` | `:146` |
| `expect_const` | `:173` |
| `expect_mono` | `:192` |
| `prob_eq_expect` | `:207` |
| `prob_bind` | `:223` |
| `expect_sample_equiv` | `:303` |
| `expect_sample_comm` | `:312` |
| `expect_expect_sample` | `:325` |
| `expect_sub` | `:339` |
| `abs_expect_sub_le` | `:392` |
| `expect_congr_of_allOutputs` | `Games/Hopping.lean:101` |
| `Bridge.prob_sample_eq_uprob` | `Games/Bridges/Experiments.lean:65` |
| `Bridge.expect_sample_pair` | `Games/Bridges/Experiments.lean:72` |

### 1.4 The handler types of the IBE game and of the simulator

All lines below are in `AdvancedEncryption/IdentityBased/`.

| Object | Type or definition | File:line |
|---|---|---|
| `IBEScheme.sidSpec κ` | `abbrev := bitSpec (S.inLens κ) (S.outLens κ)`. `inLens` and `outLens` are defs (`:201`, `:217`), sealed for consumers. | `Defs.lean:232` |
| `IBEScheme.SidState κ` | `abbrev := Option (Fin (S.idLen.eval κ) → Bool) × Option (Fin (S.ctLen.eval κ) → Bool)` | `Defs.lean:240` |
| **real handler** `S.sidImpl b κ pp msk` | `QueryImpl (S.sidSpec κ) (S.SidState κ) unifSpec` | `Defs.lean:258–281` |
| its readers | `sidImpl_init_none`/`_some`, `_keyGen_none`/`_target`/`_ne`, `_challenge_none`/`_repeat`/`_fresh`/`_invalid`, all stated with **typed** queries `Fin (S.idLen.eval κ) → Bool` | `Defs.lean:284–346` |
| `S.oracleImpl κ init key chal` | `QueryImpl (S.sidSpec κ) σ unifSpec` built from typed handlers; readers `oracleImpl_zero`/`_one`/`_two` (typed) | `Defs.lean:352`, `:363`, `:372`, `:381` |
| `S.sidGame A q b κ` | `(S.setup κ).bind fun k => (sample (A.Coins κ)).bind fun r => (simulate (S.sidImpl b κ k.1 k.2) (A.toComp (S.sidCodec κ) κ q r) (none, none)).bind fun res => .pure (res.1 0)` | `Defs.lean:399` (`sidGame_eq` `:407`) |
| `BB1SimState G ℓ κ d` | `abbrev := Option ((Fin ℓ(κ) → Bool) × ZMod (G.group κ d).order) × Option (Fin ctLen(κ) → Bool)` | `BonehBoyen.lean:429` |
| **simulator** `bb1SimImpl G ℓ b κ d g X Y Z T` | `QueryImpl ((bb1Scheme G ℓ).sidSpec κ) (BB1SimState G ℓ κ d) unifSpec := (bb1Scheme G ℓ).oracleImpl κ (bb1SimInit …) (bb1SimKeyQ …) (bb1SimChal …)` | `BonehBoyen.lean:627–631` (`_eq` `:634`) |
| simulator readers | `bb1SimInit_none`/`_some` (`:487`, `:496`), `bb1SimKeyQ_none`/`_target`/`_ne` (`:517`–`:530`), `bb1SimChal_none`/`_repeat`/`_fresh`/`_invalid` (`:578`–`:611`), `bb1SimParams_eq` (`:448`), `bb1SimKey_eq` (`:466`), `bb1SimCt_eq` (`:548`) | `BonehBoyen.lean` |
| `bb1SimGame G ℓ A q b real κ` | draws `r`, `g ∈ G^*`, `(a, b', c)`, `T`, `ρ`; simulates `bb1SimImpl` from `(none, none)` | `BonehBoyen.lean:645` (`_eq` `:660`) |
| T2 `bb1_sim_real` | `advantage (sidGame A q b κ) (bb1SimGame G ℓ A q b true κ) ≤ uprob (fun r => (G.inst κ r).order < 2 ^ ℓ.eval κ)` | `BonehBoyenSecurity.lean:89–92` (sketch `:73–88`) |
| T3 `bb1_sim_random` | `advantage (bb1SimGame … false false κ) (bb1SimGame … true false κ) = 0` | `BonehBoyenSecurity.lean:104–106` (sketch `:94–103`) |

The two state types in T2 differ in their first component:
* the real game's is `Option ID`;
* the simulator's is `Option (ID × Z_p)`.

Within one run, the stored `α₁` is related to the real game's `h` only through `ID*`. The relation
`h = g_1^{−ID*} g^{α₁}` is exactly the invariant `R`.

---

## 2. The proposed statements

### 2.1 Placement: a new file `Games/Relational.lean`

**Recommended: a new child module `TCSlib/Cryptography/Games/Relational.lean`**, about 150–190
lines, namespace `TCSlib.Cryptography.Games`, imported by the `Games.lean` facade. Reasons:

* **Modularity.** The new file is one coherent cluster: comparing simulations on related states.
  Its only imports are `Games.Simulate` and `Games.Probability`; it needs nothing from `Hopping`.
* **Verification cost and ownership.** `Games/Hopping.lean` (524 lines) is imported directly by 7
  modules and transitively by most of `Cryptography/`. Appending to it would rebuild and re-seal
  that whole closure, and would put a shared file into the fill's diff. The facade `Games.lean` is
  imported only by `TCSlib.lean`. A new module therefore costs only itself, the facade and the
  root, and it is a file that only `bb1-sim` owns.
* **Size.** Appending would also be acceptable for size (Hopping would reach about 640 lines, under
  the 1000-line cap). This is not the reason to prefer the new file; the two reasons above are.
* **Exports.** The facade change is one `import` line and one `## Contents` entry
  (`Games.lean:5–11`, `:32–48`). `TCSlib.lean` already imports the facade (line 65), so the root
  does not change.
* **Placement elsewhere.** `Games` has no `Basic.lean`, and this is a framework lemma, not a
  pairing helper. Placing it in the pairing area would make it a private host, which the ruling
  rules out.

`Hopping.lean` is left byte-identical. In particular, its docstring gets no cross-reference, because
any change there rebuilds its whole downstream closure. The new file points back to
`ProbComp.expect_simulate_congr` and `simulate_eq_of_abs` instead.

### 2.2 Statement-phase text of the new module

The first two lemmas have `sorry` bodies at the statement phase. The third (L2) is proved from the
first (L1) at that point, by the proved-modulo rule, as `bb1_sidSecure` is proved from T2–T4. Every
line is at most 100 characters. There is no `@[simp]` and no new definition, so no reader is owed.

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Simulate
import TCSlib.Cryptography.Games.Probability

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Simulations on related states

Two implementations of the same oracles may keep states of different types: in a security proof
the real game and its simulation often record different data for the same history (for BB1, the
committed identity with a group element `h`, or with an exponent `α_1`). If a relation `R`
between the two kinds of state holds at the start, and every call from related states answers
alike and leads to related states, then the two simulations of any computation answer alike and
end in related states (`ProbComp.expect_simulate_rel`). "Alike" is measured by expectations: a
call, or a run, from related states gives the same expectation to any two functions of the
answer and the state that agree at equal answers and related states.

With one state type and `R` the equality this is `ProbComp.expect_simulate_congr`
(`Games.Hopping`); with `R s t ↔ s = f t` it is the law form of `simulate_eq_of_abs`
(`Games.Simulate`), without a query budget.

## Main definitions

None.

## Main results

* `ProbComp.expect_simulate_rel`: implementations on related states simulate alike.
* `ProbComp.prob_simulate_rel`: events on the output have the same probability, so games that
  return a bit computed from the output have the same acceptance probability.
* `ProbComp.expect_sample_rel`: a call that draws one uniform sample meets the hypothesis of
  `expect_simulate_rel` when a bijection of the samples matches the answers and relates the new
  states.

## References

* [BGZ09] G. Barthe, B. Grégoire, S. Zanella Béguelin, *Formal certification of code-based
  cryptographic proofs*, POPL 2009 (the probabilistic relational Hoare logic and its rule for
  adversary calls with oracles that keep a relational invariant). ⟨location to pin, Q11⟩
* [Sho04] V. Shoup, *Sequences of games: a tool for taming complexity in security proofs*, IACR
  ePrint 2004/332, revision of 18 January 2006 (bridging steps). ⟨location to pin, Q11⟩
-/

namespace TCSlib.Cryptography.Games

namespace ProbComp

variable {ι : Type} {spec : OracleSpec ι} {σ τ α : Type}

/-- **Implementations on related states simulate alike.** Let `impl₀` keep states in `σ` and
`impl₁` in `τ`, related by `R : σ → τ → Prop`. Suppose that every call from related states
`R s t` gives the same expectation to any function `g₀` of the answer and the new `σ`-state and
any function `g₁` of the answer and the new `τ`-state that agree at equal answers and related
states:
`(∀ y s' t', R s' t' → g₀ (y, s') = g₁ (y, t')) → 𝔼[g₀] (impl₀ i x s) = 𝔼[g₁] (impl₁ i x t)`.
Then from related states the simulations of every computation `c` do the same for functions of
the output and the final state: if `R s t`, and `G₀ (a, s') = G₁ (a, t')` whenever `R s' t'`,
then `𝔼[G₀] (simulate impl₀ c s) = 𝔼[G₁] (simulate impl₁ c t)`.
[BGZ09, ⟨rule for adversary calls⟩] [Sho04, ⟨bridging steps⟩]

**Deviation:** [BGZ09] asks for a coupling of the two calls whose support relates their results;
here the hypothesis is its expectation form (equal expectations for every pair of test functions
that agree along the relation), which such a coupling implies and which is all the induction
uses.

**Proof sketch.** Induction on `c`, generalizing the two states. At a return `a`, `R s t` gives
`G₀ (a, s) = G₁ (a, t)`. At a query, both sides are the expectation over the call of the
continuation's expectation (`simulate_query`, `expect_bind`); by the induction hypothesis the two
continuation values agree at equal answers and related new states, so the hypothesis on the call
equates them. -/
theorem expect_simulate_rel (impl₀ : QueryImpl spec σ unifSpec)
    (impl₁ : QueryImpl spec τ unifSpec) (R : σ → τ → Prop)
    (h : ∀ i x s t, R s t → ∀ (g₀ : spec.rng i × σ → ℝ) (g₁ : spec.rng i × τ → ℝ),
      (∀ y s' t', R s' t' → g₀ (y, s') = g₁ (y, t')) →
        expect (impl₀ i x s) g₀ = expect (impl₁ i x t) g₁)
    (c : OracleComp spec α) (G₀ : α × σ → ℝ) (G₁ : α × τ → ℝ)
    (hG : ∀ a s' t', R s' t' → G₀ (a, s') = G₁ (a, t')) {s : σ} {t : τ} (hst : R s t) :
    expect (simulate impl₀ c s) G₀ = expect (simulate impl₁ c t) G₁ := by
  sorry

/-- **Events on the output, from related states:** under the hypothesis of
`expect_simulate_rel`, from related states `R s t` every event `P` on the output of `c` has the
same probability under the two simulations:
`Pr[P (simulate impl₀ c s).1] = Pr[P (simulate impl₁ c t).1]`. For a game that returns a bit
computed from the output this equates the acceptance probabilities (`accept_eq`). -/
theorem prob_simulate_rel (impl₀ : QueryImpl spec σ unifSpec)
    (impl₁ : QueryImpl spec τ unifSpec) (R : σ → τ → Prop)
    (h : ∀ i x s t, R s t → ∀ (g₀ : spec.rng i × σ → ℝ) (g₁ : spec.rng i × τ → ℝ),
      (∀ y s' t', R s' t' → g₀ (y, s') = g₁ (y, t')) →
        expect (impl₀ i x s) g₀ = expect (impl₁ i x t) g₁)
    (c : OracleComp spec α) (P : α → Prop) {s : σ} {t : τ} (hst : R s t) :
    prob (simulate impl₀ c s) (fun p => P p.1) = prob (simulate impl₁ c t) (fun p => P p.1) := by
  classical
  rw [prob_eq_expect, prob_eq_expect]
  exact expect_simulate_rel impl₀ impl₁ R h c _ _ (fun _ _ _ _ => rfl) hst

/-- **A sampling call, coupled by a bijection:** let `c₀` draw `u ∈ U` and return `f₀ u`, and
`c₁` draw `v ∈ V` and return `f₁ v`. If a bijection `e : U ≃ V` gives equal answers and related
states, `(f₀ u).1 = (f₁ (e u)).1` and `R (f₀ u).2 (f₁ (e u)).2`, then `c₀` and `c₁` give the same
expectation to any `g₀`, `g₁` that agree at equal answers and related states,
`𝔼[g₀] c₀ = 𝔼[g₁] c₁`: the hypothesis of `expect_simulate_rel` for such a call.

**Proof sketch.** Both sides are uniform averages (`expect_bind`, `expect_pure`); reindex the
average over `V` along `e` (`expect_sample_equiv`) and compare the two averages pointwise. -/
theorem expect_sample_rel {U V β : Type} [Fintype U] [Nonempty U] [Fintype V] [Nonempty V]
    (R : σ → τ → Prop) (e : U ≃ V) (f₀ : U → β × σ) (f₁ : V → β × τ)
    (hf : ∀ u, (f₀ u).1 = (f₁ (e u)).1 ∧ R (f₀ u).2 (f₁ (e u)).2)
    (g₀ : β × σ → ℝ) (g₁ : β × τ → ℝ) (hg : ∀ y s' t', R s' t' → g₀ (y, s') = g₁ (y, t')) :
    expect ((sample U).bind fun u => .pure (f₀ u)) g₀ =
      expect ((sample V).bind fun v => .pure (f₁ v)) g₁ := by
  sorry

end ProbComp

end TCSlib.Cryptography.Games
```

**Changes to the facade `Games.lean`.**
* Import: `import TCSlib.Cryptography.Games.Relational`, after `…Games.Hopping` (line 9).
* `## Contents` entry: "`TCSlib.Cryptography.Games.Relational`: simulations of two implementations
  on related states (the relational form of simulation congruence)."

**How the hypothesis expresses the ruling's wording.** The ruling asks for "an invariant `R`
preserved by each oracle call, with equal answer laws". The single hypothesis `h` contains both
parts:
* **Equal answer laws.** Take `g₀`, `g₁` to be the same function of the answer only; `h` then says
  the two answers have the same law.
* **Preservation of `R`.** The test functions need to agree only at *related* successor states. If
  a call could reach a successor that is unrelated to the other side's successors, a pair of test
  functions would separate the two calls.

Packaging both parts as one expectation condition is what makes the induction a direct copy of
`expect_simulate_congr`'s. It is also the form in which the conclusion comes out, so the lemma
composes. Requiring an explicit coupling instead would add a new kind of object to `Games`
(Q3 in §5).

### 2.3 How the proofs would go, and which existing lemmas they use

* **L1 `expect_simulate_rel`.** The proof has the same shape as `ProbComp.expect_simulate_congr`
  (`Hopping.lean:384–393`): induction on `OracleComp` (`OracleComp.lean:84`), generalizing `s`, `t`
  and `hst`. It uses:
  * `simulate_pure` and `simulate_query` (`Simulate.lean:93`, `:97`);
  * `expect_pure` and `expect_bind` (`Probability.lean:116`, `:127`).

  An unchecked outline:
  ```lean
    induction c generalizing s t with
    | pure a =>
      rw [simulate_pure, simulate_pure, expect_pure, expect_pure]
      exact hG a s t hst
    | query i x k ih =>
      rw [simulate_query, simulate_query, expect_bind, expect_bind]
      exact h i x s t hst _ _ fun y s' t' hR => ih y hR
  ```
* **L2 `prob_simulate_rel`.** Proved from L1 with `prob_eq_expect` (`Probability.lean:207`). It is
  proved at the statement phase.
* **L3 `expect_sample_rel`.** Uses `expect_bind`, `expect_pure` and `expect_sample_equiv`
  (`Probability.lean:303`); about 10 lines.
* **Rule 10.** Every foreign definition is read through its published lemmas: `simulate` through
  `simulate_pure`/`simulate_query`, `expect` through `expect_pure`/`expect_bind`, `prob` through
  `prob_eq_expect`, and `sample` through `expect_sample_equiv`. `QueryImpl` is an `abbrev`, which
  counts as notation. Nothing is unfolded, so the canonical seal of the new owner should pass
  unchanged.

### 2.4 Why it is not a duplicate

**How the search was done.** I searched `TCSlib/` at `9e7a9648` in four ways:
1. A script scanned every `theorem` or `lemma` statement mentioning `simulate` at least twice, or
   `simulate` together with two `QueryImpl`s. 49 hits; each was classified from its statement, and
   the relevant ones were read in full.
2. `git grep` for the terms "coupl", "bisim", `σ → τ → Prop`, `σ₁`/`σ₂`/`τ` beside
   `simulate`/`QueryImpl`, "pRHL", "Barthe" and "bridging".
3. The same grep for `expect_simulate_rel`, `simulate_rel`, `σ → τ → Prop` and "bisim" on **every
   local and remote branch** (including `fill/pairings-bb1-machine`, `fill/pairings-pair-bdh` and
   `stmt/*`). This found nothing.
4. The T4 helper modules on `7c0a55e0`.

**Result.**
* No public or private lemma relates two simulations by a relation between different state types.
* The new lemma generalizes three existing lemmas without restating any of them:
  * `expect_simulate_congr`, the case where `R` is equality;
  * the law form of `simulate_eq_of_abs`, the case `R s t ↔ s = f t`;
  * the unbudgeted cases of the ETT forms, the case `R s t ↔ P t ∧ s = f t`.
* L3 is new. No lemma states a bijective coupling of one sample as a relational step; the existing
  uses inline `expect_sample_equiv`.

**Near-relatives, and why each is not the same statement.**

| Lemma | File:line | Relation to the proposal |
|---|---|---|
| `Games.ProbComp.expect_simulate_congr` | `Games/Hopping.lean:384` | One state type, the same start state. The `R = Eq` special case. |
| `Games.simulate_eq_of_abs` | `Games/Simulate.lean:334` | Two state types, but a function `f : σ₂ → σ₁` and **exact equality of computations** for **every** state. It cannot express re-randomization (T2's `h ↔ α₁`, `r̃ ↔ r`) or an invariant (Gate 40: "structural state abstraction, but not arbitrary distributional re-randomization"). |
| `Games.simulate_eq_of_abs_bounded` | `Games/Simulate.lean:357` | As above, with deterministic calls and a budget. |
| `Composability.ETTGame.expect_simulate_abs`, `expect_simulate_abs_inv` | `Encryption/PrivateKey/EncryptThenTag/Tools.lean:65`, `:88` | **Closest relatives.** Law form with a function abstraction `f`, an invariant `P` on one side, and a **query budget** (`cnt`, `κ`, `CostBoundedBy`). A function cannot relate T2's states, where `h` and `α₁` are linked through `ID*`. In the ETT layer (the file's docstring: "candidates for promotion to the `Games` layer"), and recorded in **DL-40** as a deferred promotion (`duplication-ledger.md:67`). The new lemma is the unbudgeted relational generalization; the budgeted ETT lemmas are not instances of it (Q5). |
| `Games.expect_eq_until_bad`, `prob_eq_until_bad`, `identical_until_bad(_init)` | `Games/Hopping.lean:201`, `:252`, `:306`, `:343` | One state type; equality up to a bad flag. |
| `Games.expect_simulate_eager` | `Games/Hopping.lean:494` | One state type; moves one-shot coins. Used *beside* the new lemma (§3). |
| `Composability.ChallengeSim.expect_simulate_eager` | `Encryption/PublicKey/OracleSecurity/ChallengeSim.lean:148` | The same name in another namespace; a CPA-shaped eager step with one state type. |
| `NMSim.expect_simulate_rImpl_eager` | `Encryption/PublicKey/NonMalleability/Simulation/Hybrid.lean:267` | An application of `Games.expect_simulate_eager`. |
| `ETTGame.simulate_tapeImpl_congr`, `expect_simulate_tapeImpl`, `freshImpl`, `tapeImpl` | `…/EncryptThenTag/Tools.lean:145`, `:167`, `:116`, `:130` | Tapes against fresh coins; state `σ` against `σ × ℕ`, fixed by construction, with a budget. |
| `AdaptiveCPA.simulate_tapeImpl_congr`, `expect_tapeImpl` | `Encryption/PublicKey/AdaptiveCPA/Hybrid.lean:170`, `:244` | Specific tape hybrids. |
| `PRFGame.expect_lazyImpl` | `Encryption/PrivateKey/OracleFromPRF/Lazy.lean:351` | Lazy against eager random function; two state shapes, proved by its own induction for one pair of handlers. A specific bisimulation; the new lemma would be the generic tool for such proofs. |
| `ETTGame.expect_ettImpl_lazy`, `expect_ettLazyTape` | `Encryption/PrivateKey/EncryptThenTag/Lazy.lean:499`, `:461` | The same, for ETT. |
| `PRFGame.simulate_eImpl_congr` | `Encryption/PrivateKey/OracleFromPRF/Games.lean:199` | Congruence for one family of handlers. |
| `HashSignFill.expect_simulate_sample_once` | `Authentication/Signatures/HashAndSign/OneQuerySampling.lean:47` | One-query sampling law. |
| `LamportFill.planted_coupling` | `Authentication/Signatures/Lamport/Planted.lean:403` | A deterministic "coupling" for one specific aborting handler (at most one query). |
| `NMSim.expect_runB_good` (private) | `Encryption/PublicKey/NonMalleability/Simulation/SimIND.lean:702` | A coupling through `expect_eq_until_bad`. |
| `BB1Machine.exists_simulate_tape_eq_pure`, `expect_castImpl_freshImpl` (T4 branch) | `…/BonehBoyenMachine/Draws.lean:399`, `…/Reduction.lean:203` at `7c0a55e0` | Specific to T4's tape handler. |

**Note.** Several of these specific bisimulations (`expect_lazyImpl`, `expect_ettImpl_lazy`) could
later be re-proved from `expect_simulate_rel`. That is a candidate refactor for the DL-40 clean-up,
not part of this unit.

---

## 3. How T2 and T3 use it

The fill-local names below (`bb1RealAt`, `bb1RealLazy`, `bb1SimLazy`, `BB1RealState`) are
illustrative. Let `S := bb1Scheme G ℓ` and `c := A.toComp (S.sidCodec κ) κ q ρ`; this is the same
computation in both games. Fix the generator coins `r`, and write `d = G.desc κ r` and
`B = G.group κ d`. A coin set is *good* when `2^ℓ ≤ p`.

### 3.1 T2 `bb1_sim_real`

**Chain.** All quantities below are acceptance probabilities conditioned on `r`. Steps (1)–(4) and
(6)–(7) hold for every `r`; only step (5) uses good coins.

| Step | Equation | How it is justified |
|---|---|---|
| (1) | `Pr[sidGame_b | r] = 𝔼_{g,α,g₂,ρ} 𝔼_h Pr[simulate (S.sidImpl b κ pp_h msk_h) c ∅]` | Move the setup sample `h` inside, past `g₂` and `ρ` (`expect_sample_comm`, `expect_expect_sample`). |
| (2) | `= 𝔼_{g,α,g₂,ρ} 𝔼_h Pr[simulate (bb1RealAt h) c ∅]` | **`expect_simulate_rel` with `R_h`** (step R1 below). |
| (3) | `= 𝔼_{g,α,g₂,ρ} Pr[simulate bb1RealLazy c ∅]` | **`Games.expect_simulate_eager`** (step E-h below). |
| (4) | `= 𝔼_{g,α,b',ρ} Pr[… with g₂ := g^{b'}]` | `expect_sample_equiv` with the bijection `Z_p ≃ G`, `b' ↦ g^{b'}` (`g ≠ 1`). |
| (5) | `= 𝔼_{g,α,b',ρ} Pr[simulate bb1SimLazy c ∅]` | **`expect_simulate_rel` with `R`** (step M below); needs good coins. |
| (6) | `= 𝔼_{g,α,b',ρ} 𝔼_c Pr[simulate (bb1SimImpl b κ d g X Y g^c e(g,g)^{αb'c}) c ∅]` | **`Games.expect_simulate_eager`** (step E-c below). |
| (7) | `= Pr[bb1SimGame_{b,true} | r]` | Reorder; merge `(a, b', c)` (`Bridge.expect_sample_pair`); with `real = true` the sample `T` is unused (`expect_const`). |
| Bad coins | `abs (accept₀ − accept₁) ≤ 𝔼_r 1[p < 2^ℓ] = uprob (…)` | Pointwise bound `abs (F₀ r − F₁ r) ≤ 1[bad r]`, then `Bridge.prob_sample_eq_uprob` and `BilinearGen.inst_eq` (`Pairing/Group.lean:282`). |

**Handlers and invariants.** Throughout, `X = g^α` and `Y = g₂ = g^{b'}`.

* **Step R1** (equation (2)): from the real handler to a handler that stores `h`.
  * `impl₀ := S.sidImpl b κ pp_h msk_h` on `S.SidState κ`, where
    `pp_h = ⟨d, (g, X, Y, h)⟩` and `msk_h = ⟨d, ((g, X, Y, h), Y^α)⟩`. This is the shape of
    `bb1Scheme`'s setup output, `(⟨d, k.1⟩, ⟨d, k⟩)`.
  * `impl₁ := bb1RealAt h` on
    `BB1RealState := Option ((Fin ℓ(κ) → Bool) × B.G) × Option (Fin ctLen(κ) → Bool)`. On a
    committed state it runs `sidImpl`'s call with the *stored* `h`. On the first `Init` it stores
    `(ID*, h)`.
  * `R_h s u :↔ s = (u.1.map Prod.fst, u.2) ∧ ∀ p ∈ u.1, p.2 = h`.
  * Start: `R_h (none, none) (none, none)`.
  * Per-call obligations: from related states the two calls are the same computation, with the
    state mapped. The deterministic cases need `expect_pure`. The sampling cases (`KeyGen` for
    `ID ≠ ID*`, a fresh `Challenge`) need L3 with `e := Equiv.refl`.
* **Step E-h** (equation (3)): `Games.expect_simulate_eager` with `O := bb1RealLazy` (draws
  `h ← G` at the first `Init`), `OE h := bb1RealAt h`, and `used u := u.1.isSome`.
  * From a committed state, `bb1RealAt h = bb1RealLazy`.
  * `KeyGen` and `Challenge` before `Init` answer `⊥` and leave the state uncommitted.
  * `Init` from an uncommitted state is the spending call.
* **Step M** (equation (5)): the main relation. **This is the coupling in T2's sketch.**
  * `impl₀ := bb1RealLazy`.
  * `impl₁ := bb1SimLazy b κ d g X Y (zt := fun c => (g^c, e(g, g)^{(α b' c)}))`: the simulator
    with the challenge coin `c` drawn at the first valid challenge.
  * `R u v :↔ u.2 = v.2 ∧ Option.Rel (fun (t, h) (t', α₁) => t = t' ∧
    h = X ^ (−idToZ t).val * g ^ α₁.val) u.1 v.1`, i.e., the same recorded challenge, and
    `h = g₁^{−ID*} g^{α₁}`.
  * Start: `R (none, none) (none, none)`.
* **Step E-c** (equation (6)): `Games.expect_simulate_eager` with `O := bb1SimLazy …` and
  `OE c := bb1SimImpl b κ d g X Y (g^c) (e(g,g)^{αb'c})`, both on `BB1SimState`, and
  `used v := v.2.isSome`. `Z` and `T` enter only the fresh valid challenge
  (`bb1SimChal_fresh`), so the coins are one-shot.

**Per-call obligations of step M.** In every case the precondition is `R u v`. The left column is
`bb1RealLazy`, read through `sidImpl`'s readers. The right column is `bb1SimLazy`, read through
`oracleImpl_*_onSpec` and the `bb1Sim*` readers.

| Call | Real (`impl₀`) | Simulator (`impl₁`) | Why the hypothesis of L1 holds |
|---|---|---|---|
| `Init`, uncommitted | Draw `h ← G`. Answer `encPP ⟨d,(g,X,Y,h)⟩`. Store `(ID, h)`. | `bb1SimInit_none`: draw `α₁ ← Z_p`. Answer `encPP ⟨d, bb1SimParams g X Y ID α₁⟩`. Store `(ID, α₁)`. | **L3** with `e : G ≃ Z_p`, the inverse of `α₁ ↦ X^{(−ID)} g^{α₁}` (a bijection for each `ID`, because `g ≠ 1`). `bb1SimParams_eq` makes the parameters equal, so the answers are equal (compared through `ofFn_bb1Scheme_encPP`). The new states are in `R`. |
| `Init`, committed | Answer the stored parameters. | `bb1SimInit_some`. | Deterministic. `R` gives `h = X^{−t} g^{α₁}`. |
| `KeyGen` before `Init`, or for `ID*` | `⊥` (`sidImpl_keyGen_none`, `_target`) | `bb1SimKeyQ_none`, `_target` | Deterministic; states unchanged. |
| `KeyGen` for `ID ≠ ID*` | Draw `r̃`. Answer `⟨1, encSK ⟨d,(Y^α F(ID)^{r̃}, g^{r̃})⟩⟩` (`sidImpl_keyGen_ne`, `bb1Scheme_keyGen`, `BB1.keyGen_eq`). | `bb1SimKeyQ_ne`: draw `r`. Answer `⟨1, encSK ⟨d, bb1SimKey g X Y t α₁ ID r⟩⟩`. | **L3** with `r̃ ↦ r̃ + b'/(ID − ID*)` (`Equiv.addRight`). Good coins make `ID − ID* ≠ 0` in `Z_p` (`bitsToNat_lt`, `bitsToNat_injective`, `Asymptotic/Sampling.lean:412`, `:417`). The keys are equal by BB04's computation, with `F(ID) = g^{α(ID−ID*)+α₁}` (`bb1SimKey_eq`, `BB1.F_eq`, `pow_val_mul` and exponent laws). States unchanged. |
| `Challenge` before `Init` | `⊥` | `bb1SimChal_none` | Deterministic. |
| `Challenge`, repeated | the recorded ciphertext | `bb1SimChal_repeat` | `u.2 = v.2`. |
| `Challenge`, first, invalid | `⊥` (`sidImpl_challenge_invalid`) | `bb1SimChal_invalid` | Both message spaces depend only on `d` (`bb1Scheme_msgSpace_iff`). |
| `Challenge`, first, valid | Draw `s`. Answer and record `encCT ⟨d, (e(X,Y)^s · M_b, g^s, F(ID*)^s)⟩` (`sidImpl_challenge_fresh`, `bb1Scheme_enc`, `BB1.encrypt_eq`). | Draw `c`. Answer and record `bb1SimCt d (g^c) (e(g,g)^{αb'c}) α₁ M_b`. | **L3** with `e := Equiv.refl` (`s = c`). `F(ID*) = g^{α₁}`; `e(X,Y)^c = e(g,g)^{αb'c}` (`bilinear_pow`, `pow_val_mul_GT`); `G_T` is commutative. Answers compared through `ofFn_bb1SimCt` and an `encCT` reader (§3.3). |

**Mapping to T2's frozen sketch** (`BonehBoyenSecurity.lean:78–88`).

| Sketch sentence | Where it is in this design |
|---|---|
| "Fix coins with `2^ℓ ≤ p` …" | The good-coin case, used in `KeyGen` for `ID ≠ ID*`. |
| "Map `α ↦ a`, `g_2 ↦ g^{b'}` …" | Steps (4) and (5). |
| "… and `h ↦ g_1^{−ID*} g^{α_1}`" | Step M at `Init`. It is per call only after E-h moves `h` to `Init`: `h` is drawn before `ID*` exists. |
| "Answers to `Init` agree." | The two `Init` rows. |
| "the simulated key with exponent `r` is the real key with exponent `r̃` …" | The `KeyGen` row for `ID ≠ ID*`. |
| "The challenge is `Encrypt` with `s = c` …" | The valid-challenge row, after E-c moves `c` to the challenge. |
| "The state machines agree step by step (`simulate` with matched implementations, `Games.expect_simulate_congr`)" | **Becomes `ProbComp.expect_simulate_rel` with `R`**, plus the two eager steps. |
| "differ only on the excluded coins" | The bad-coin row of the chain. |

The sketch's route is sound, but two of its steps are implicit: the timing of `h` (drawn before
`ID*`) and of `c` (drawn before the challenge). The docstring-only sketch refresh at landing
(standing rule) should name `expect_simulate_rel` and the two `expect_simulate_eager` steps.

### 3.2 T3 `bb1_sim_random`

The relational lemma is **not needed** for T3. Both games use the same simulator shape and the same
state type `BB1SimState`, so `R` is equality and the existing `ProbComp.expect_simulate_congr`
applies. L3 is used with `R := Eq` at one call.

**Chain, for each `b`.**

| Step | Equation | How it is justified |
|---|---|---|
| (1) | `Pr[bb1SimGame_{b,false}] = 𝔼_{r,g,abc,ρ} 𝔼_T Pr[simulate (bb1SimImpl b κ d g X Y Z T) c ∅]` | Move `T` inside, past `ρ`. |
| (2) | `= 𝔼_{r,g,abc,ρ} Pr[simulate (bb1SimLazy b κ d g X Y (zt := fun T => (Z, T))) c ∅]` | **`Games.expect_simulate_eager`** (step E-T): `used v := v.2.isSome`, and `T` is spent at the first valid challenge. |

**Comparing the two bits.** Then `bb1SimLazy false …` and `bb1SimLazy true …` have the same law
call by call (`ProbComp.expect_simulate_congr`, `Hopping.lean:384`):
* `Init` and `KeyGen` are identical (the same `bb1SimInit` and `bb1SimKeyQ`).
* `Challenge` before `Init`, repeated, or invalid is identical: the validity test does not depend
  on `b`.
* At the first valid challenge, apply **L3 with `R := Eq`** and the bijection
  `T ↦ decodeT M₁⁻¹ · decodeT M₀ · T` of `G_T`. Then `M₀ · T = M₁ · e(T)`, so the answers are
  equal and both sides record the same ciphertext (compared through `ofFn_bb1SimCt`).

Hence the accepts are equal, and `advantage = 0` (`advantage_eq`).

**Relation to T3's sketch** (`BonehBoyenSecurity.lean:98–103`). The sketch says: "exchanging the
sample of `T` with the rest of the game (`expect_expect_sample`) and reindexing it by
`T ↦ M_b^{−1} M_{1−b} · T`".
* `expect_expect_sample` alone cannot move `T` past the adaptive history. The step that does it is
  E-T. Gate 40 made the same point: "an unconditional permutation chosen before seeing the adaptive
  history is not required".
* The reindexing is per call, at the challenge.

The sketch refresh at landing should name `expect_simulate_eager` and `expect_simulate_congr`.

### 3.3 What else the fill needs

1. **Readers in the frozen files.** This is the main dependency.
   * **From T4's PR** (approved; not yet on `7c0a55e0`):
     * `IBEScheme.oracleImpl_{zero,one,two}_onSpec` (`Defs.lean`), for reading `bb1SimImpl` at the
       game's query type; needed by T2 and T3;
     * `bb1Scheme_msgSpace_iff`, for T2's invalid-challenge case;
     * `ofFn_bb1SimCt`, for the challenge answers in T2 and T3;
     * `ofFn_bb1Scheme_encPP` and `ofFn_bb1Scheme_encSK`, for T2's `Init` and `KeyGen` answers.
   * **Probably new** (to be confirmed by a probe):
     * **a reader for `sidImpl` at the game's query type.** The nine `sidImpl_*` readers take typed
       queries `Fin (S.idLen.eval κ) → Bool`. Under the seals, `inLens` blocks unification with
       `(S.sidSpec κ).dom i`, which is the obstruction T4 hit for `oracleImpl`. Proposed:
       `IBEScheme.sidImpl_eq_oracleImpl : S.sidImpl b κ pp msk =
       S.oracleImpl κ (S.sidImpl b κ pp msk 0) (S.sidImpl b κ pp msk 1) (S.sidImpl b κ pp msk 2)`.
       It is one reader, proved by `funext` and a three-way `match` with `rfl`. Combined with
       T4's `_onSpec` readers it makes the typed `sidImpl_*` lemmas apply. The alternative is three
       `sidImpl_*_onSpec` readers in T4's form.
     * **an `ofFn` reader for `bb1Scheme`'s `encCT`** (`ofFn_bb1Scheme_encCT`), parallel to T4's
       `encPP` and `encSK` readers, for comparing the real challenge with `bb1SimCt`.
   * **Constructing values in a consumer file.** T4's report notes that anonymous constructors
     `⟨d, pp⟩ : (bb1Scheme G ℓ).PP κ` do not elaborate under the seals. The real-side handlers
     (`bb1RealAt`, `bb1RealLazy`) should therefore take the setup's output map as a parameter,
     instantiated from `bb1Scheme_setup` and `BB1.setup_eq` at the use site. They should not
     construct `PP` or `MSK` values themselves.
2. **Group helpers.** None of these is published:
   * `a ↦ g^{a.val}` is a bijection `Z_p ≃ G` for `g ≠ 1`. Only the `G_T` form
     `pow_val_bijective` exists (`Pairing/Group.lean:224`).
   * The additive and negation exponent laws `x^{(u+v).val} = x^{u.val} x^{v.val}` and
     `x^{(−u).val} = (x^{u.val})⁻¹`, next to `pow_val_mul` (`:192`).
   * Residue injectivity of `ℓ`-bit identities when `2^ℓ ≤ p`, from `bitsToNat_lt` and
     `bitsToNat_injective`.

   Each is a short proof from `exists_pow_eq`, `pow_order` and Mathlib's `orderOf` facts. Q10 asks
   where they go.
3. **Lazy handlers, with readers and eager lemmas.**
   * `bb1SimLazy` should be generic in the challenge coins (`zt : U → G × G_T`). One definition
     then serves T2's `c` (`U = Z_p`) and T3's `T` (`U = G_T`), with one eager lemma derived from
     `Games.expect_simulate_eager`.
   * `bb1RealAt` and `bb1RealLazy` serve T2's `h`.
   * They are public definitions in a helper module, so each lands with case readers (policy §1).
   * No new eager lemma is to be proved: DL-33 recorded an earlier near-copy of the eager lemma.
4. **Averaging a pointwise bound.** T2's last step needs `abs (𝔼 f − 𝔼 g) ≤ 𝔼 h` from
   `∀ x, abs (f x − g x) ≤ h x`. The only copy is the **private**
   `abs_expect_sub_le_expect` (`Encryption/PrivateKey/EncryptThenTag/Forgery.lean:515`), which
   DL-40 has queued for promotion. The fill must not add a second private copy (Q6).
5. **Plumbing that already exists.**
   * Game equations: `IBEScheme.sidGame_eq`, `bb1SimGame_eq`, the `bb1Scheme_*` `simps` equations,
     `BB1.setup_eq`.
   * Advantage: `accept_eq`, `advantage_eq`.
   * Expectations: `prob_bind`, `expect_bind`, `expect_sample_comm`, `expect_expect_sample`,
     `Bridge.expect_sample_pair`, `expect_const`, `expect_sample_equiv`,
     `Bridge.prob_sample_eq_uprob`.
   * Group: `BilinearGen.inst_eq`, `bilinear_pow`, `pow_val_mul(_GT)`.
   * The instance `nonempty_ne_one` (`Pairing/Group.lean:147`) for sampling `G^*`.
   * No query budget is needed anywhere.
6. **Layout.**
   * Helper modules under `IdentityBased/BonehBoyenSecurity/`, for example `Lazy.lean` (the lazy
     handlers and eager lemmas), `Real.lean` (R1 and E-h) and `Coupling.lean` (step M with the
     group helpers).
   * `BonehBoyenSecurity.lean` gains their imports and a `## Contents` section, following T4's
     precedent for `BonehBoyenMachine.lean`.
   * T2's and T3's headers and statement prose stay byte-identical.
   * At landing, the `**Proof sketch.**` paragraphs get a docstring-only refresh.
   * Size: the plan estimates T2 at 400–800 lines and T3 at 150–350. The lazy handlers and their
     readers move T2 toward the upper end.

---

## 4. Unit split and gating

### 4.1 Statement phase (Phase S)

**Contents of the change.**
* The new file `Games/Relational.lean` exactly as in §2.2:
  * `expect_simulate_rel` and `expect_sample_rel` are `sorry`'d, with sketches;
  * `prob_simulate_rel` is proved from `expect_simulate_rel` (proved-modulo).
* The `Games.lean` facade: one import and one `## Contents` entry.
* Nothing else. `Hopping.lean`, `TCSlib.lean` and every pairing file stay unchanged.

**Branch.** Phase S touches only `Games/`, which sits above the pairing closure and is disjoint
from #331, #340 and T4's branch. It can therefore be a small PR on the records tip. The precedent
is #210's shared statements S1–S3, which were added `sorry`'d and later filled by the units.

**Evidence, in the campaign's usual form.**
* A build of `Games.Relational`, `Games` and the root.
* An axiom census: `sorryAx` only in `expect_simulate_rel` and `expect_sample_rel`, and inherited by
  `prob_simulate_rel`.
* Canonical seals of the new owner (strict and coe, A and B), with paired controls and the
  explicit-unfold scan.
* Style lint; frozen check: no other file is changed.

**Before Phase S is filed, a probe (not committed).** This avoids T4's mid-fill stop. The probe
should:
* state T2's per-call obligations for step M and T3's challenge obligation;
* check them under the development seals, using T4's 7 readers and the proposed
  `sidImpl_eq_oracleImpl` and `ofFn_bb1Scheme_encCT`;
* put the exact reader set to Seyoon as a scope request before the fill is issued.

### 4.2 Fill (Phase F, unit `bb1-sim`)

**What the unit owns.**
* The proof bodies of `expect_simulate_rel` and `expect_sample_rel` in `Games/Relational.lean`.
  Their headers and statement prose are frozen at the Phase S commit.
* T2 and T3 in `IdentityBased/BonehBoyenSecurity.lean`, plus the new helper modules.
* The reader insertions that the scope ruling approves.

**Base.** The fill uses T4's readers, so it must be based on T4's PR after the readers land there,
or on the records tip once that PR has merged.

**End state.** `bb1_sidSecure` reaches standard axioms once both T4 and `bb1-sim` are in.

### 4.3 Gate coverage

* **Gate 44** audits T4's PR (`fill/pairings-bb1-machine`): the T4 fill, and the 7 readers checked
  as pure insertions. It does not cover `Games/Relational.lean` or T2/T3, and it should not be
  widened to them.
* **Recommended: one `bb1-sim` gate after Gate 44**, numbered with the next free number when it is
  staged. Having one gate for the statement and the fill matches the ruling. Its pack:
  1. pins the Phase S commit as the statement baseline;
  2. runs a frozen-header check: `expect_simulate_rel`, `prob_simulate_rel` and
     `expect_sample_rel` are byte-identical to Phase S apart from their `**Proof sketch.**`, and T2
     and T3 are byte-identical to #331;
  3. audits the three statements for generality, docstring fidelity, attribution, placement and
     non-duplication against the table in §2.4;
  4. checks the reader insertions as pure insertions, as Gate 44 does;
  5. audits the fill: seals for the new owners and for every owner whose closure changed, axioms,
     and the sketch refresh.
* **Alternative.** If Seyoon wants the `Games` statement fixed before the fill is issued, Phase S
  can be appended to Gate 44's pack as a separate item. The files are disjoint and the item is
  statement-only. The fill would then be audited at the later gate.
* **The file-disjointness caveat.** The premise that "T4's PR … owns disjoint files" holds for the
  owned files, but not for the reader insertions:
  * T4's PR inserts into `Defs.lean` and `BonehBoyen.lean`, and `bb1-sim` probably needs more
    insertions in the same two files.
  * To keep the diffs disjoint in time, sequence them: T4 merges first, then `bb1-sim`.
  * The `bb1-sim` readers go at different anchors: in `Defs.lean`, after T4's `_onSpec` block
    (`sidImpl_eq_oracleImpl` mentions `oracleImpl`, so it must follow `Defs.lean:352`); in
    `BonehBoyen.lean`, next to the `simps` attribute (`:386`).
  * Each of those owners' canonical seals is re-run in that gate.

---

## 5. Risks and open questions

### Risks

1. **The reader scope (high).**
   * T2 cannot read `sidImpl` at the game's query type with the published readers. This is the
     `inLens` obstruction from T4's report.
   * T2 probably also needs an `encCT` reader, and a way to avoid constructing
     `(bb1Scheme G ℓ).PP κ` values in a consumer file.
   * Without a probe first, the fill would stop mid-way as T4 did (§3.3, item 1; §4.1).
2. **Dependence on T4's PR (medium).** `bb1-sim` consumes `oracleImpl_*_onSpec`,
   `bb1Scheme_msgSpace_iff` and the `ofFn_*` readers, and both units insert into the same two
   frozen files. Q9 covers the ordering.
3. **Sketch drift (low; standard).**
   * T2's frozen sketch cites `Games.expect_simulate_congr` (the wrong namespace, and the wrong
     lemma, since the state types differ).
   * Both sketches leave the eager/lazy steps implicit (§3.1, §3.2).
   * The standing rule gives a docstring-only refresh at landing; the statements are never changed.
4. **Budget and DL-40 (low).**
   * `expect_simulate_rel` has no query budget, so the budgeted ETT `expect_simulate_abs(_inv)`
     are not instances of it.
   * If DL-40's promotion later wants them derived from the relational form, it needs a budgeted
     variant (Q5).
   * Today's ETT copies stay as recorded in DL-40. Nothing new is duplicated.
5. **Duplication traps for the fill (medium).**
   * A second private copy of `abs_expect_sub_le_expect` (Q6).
   * Re-proving an eager lemma instead of citing `Games.expect_simulate_eager` (the DL-33
     precedent).
   * Private group helpers that duplicate a Mathlib fact. The fill should check Mathlib's
     `orderOf` and `ZMod` API first and disclose whatever it adds.
6. **Audit of the hypothesis form (low).**
   * An auditor may ask whether a hypothesis stated as "the conclusion for one call" is checkable.
     L3 answers this: in the BB1 proofs every call is either deterministic or one sample coupled by
     a bijection.
   * The hypothesis is weaker than an explicit coupling, which implies it. Its conclusion has the
     same form, so it composes.
7. **Attribution (low).** The locations in [BGZ09] (the rule for adversary calls) and [Sho04]
   (bridging steps) are not pinned here: the PDFs are not in the repository, and nothing was read
   to confirm a section number (Q11).
8. **Verification cost (low).**
   * Phase S rebuilds one new module, the `Games` facade and the root.
   * The reader insertions in Phase F rebuild the IBE closure, and need canonical re-seals of
     `Defs` and `BonehBoyen`.
9. **Name collision (none found).** `expect_simulate_rel`, `prob_simulate_rel` and
   `expect_sample_rel` exist on no branch. Readers should not confuse `Games.expect_simulate_eager`
   with `ChallengeSim.expect_simulate_eager`.

### Open questions for Seyoon (recommended option first)

- **Q1. Placement.**
  - (A) A new `Games/Relational.lean`, imported by the `Games` facade.
  - (B) Append to `Games/Hopping.lean` after `expect_simulate_congr`. This touches a widely
    imported file and costs a large rebuild and re-seal.
- **Q2. Names.**
  - (A) `Games.ProbComp.expect_simulate_rel`, `prob_simulate_rel`, `expect_sample_rel`, beside
    `ProbComp.expect_simulate_congr`.
  - (B) Root `Games.` names, as with `expect_simulate_eager`.
- **Q3. Form of the hypothesis.**
  - (A) The inline expectation hypothesis of §2.2: equal expectations of test functions that agree
    along `R`.
  - (B) A named predicate (for example `ProbComp.RelLaw R c₀ c₁`) with its `relLaw_iff` reader.
  - (C) An explicit coupling computation with an `AllOutputs` support condition.
- **Q4. Companions.**
  - (A) `prob_simulate_rel` and `expect_sample_rel` with the target.
  - (B) The target only. The fill then discharges calls inline with `expect_sample_equiv`.
- **Q5. Query budget.**
  - (A) None now.
  - (B) Also state `expect_simulate_rel_bounded` (a budget `cnt`/`κ`), so that DL-40 can later
    re-derive ETT's `expect_simulate_abs(_inv)` from it.
- **Q6. The averaging bound `abs (𝔼 f − 𝔼 g) ≤ 𝔼 h`.**
  - (A) The T2 fill writes it inline in T2's proof (a few lines, disclosed), and DL-40's promotion
    stays queued.
  - (B) Promote the ETT lemma now into `Games/Probability.lean` (a widely imported file).
  - (C) Add it to `Games/Relational.lean` in Phase S.
- **Q7. Reading `sidImpl` at the game's query type.**
  - (A) One reader, `IBEScheme.sidImpl_eq_oracleImpl`, in `Defs.lean` after T4's `_onSpec`
    readers. It is carried by the `bb1-sim` PR under an advance scope ruling from the probe.
  - (B) Three `sidImpl_{zero,one,two}_onSpec` readers in T4's form.
  - (C) Ask T4's PR to carry it, which widens T4's approved minimal scope.
- **Q8. Gate.**
  - (A) One `bb1-sim` gate after Gate 44, covering the Phase S statement, the reader insertions and
    the fill.
  - (B) Fold the Phase S statement into Gate 44's pack and audit the fill later.
- **Q9. Order and bases.**
  - (A) Phase S as its own small PR on the records tip. The fill is stacked on T4's PR, or based on
    the tip once T4 has merged.
  - (B) Everything on one branch stacked on T4's PR.
- **Q10. Group helpers** (`Z_p ≃ G` for `g ≠ 1`, exponent laws, identity injectivity on good
  coins).
  - (A) Public helpers with formula docstrings in the fill's helper module, disclosed.
  - (B) A reader-style request into the frozen `Pairing/Group.lean`.
- **Q11. Attribution of the lemma.**
  - (A) Cite [BGZ09] and [Sho04] at locations the maintainer pins from the sources.
  - (B) Treat it as a framework lemma and give only the design references; policy §2 allows tags to
    be omitted for technical glue.

---

## Appendix: search record

**Scanner.** A script was run on `9e7a9648` with `python3 -I`; it is in the job's scratch area and
is not committed. It lists every `theorem` or `lemma` under `TCSlib/` whose statement contains
`simulate` twice, or `simulate` together with two `QueryImpl`s. 49 hits; each was classified from
its statement, and the relevant ones were read in full and are listed in §2.4.

**Greps on `9e7a9648`.**
* `coupl|bisim` (case-insensitive) under `TCSlib/Cryptography`: prose only, in Lamport,
  HashAndSign, NonMalleability, FromPRF and the IBE docstrings. No generic lemma.
* `Barthe|pRHL|CertiCrypt|EasyCrypt|bridging step` under `TCSlib` and `blueprint`: no
  cryptographic citation.
* `theorem …simulate…` in `Games/`: the rows of §1.3.

**All local and remote branches:** `expect_simulate_rel|simulate_rel|σ → τ → Prop|bisim` under
`TCSlib/Cryptography`. Nothing found.

**The `Games/` layer:** `git diff 9e7a9648 a0e31483 -- TCSlib/Cryptography/Games` is empty.

## ===== briefs/pairings/gates/44-pairing-fills/findings-r1.md (records, at ab17e37feb00a677d69f6abd5ff7e427e3b9ef3c) =====

<!-- Filed by the maintainer on 2026-11-17 from the auditor's chat reply, pasted by Seyoon. The text below is verbatim.
The evidence ZIP it mentions (gate44-pairing-fills-evidence.zip) was not uploaded; only this Markdown was received. -->

# Gate 44 pairing fills — round 1 findings

**Verdict: HOLD. Open findings: 0 blockers, 1 major, 1 minor, 1 note.**

The delivered proofs establish the frozen T1 and T4 statements. The hold concerns the required acceptance of disclosed duplication.

| Audited item | Pin |
|---|---|
| Exchange | `30ef1257a56873489b599007782046b7dedeb7fc` |
| Campaign records | `8f888790b7e40f9e0529967e29a05a72c5ee8ba3` |
| #340 / merge base | `916afc25c21f5e52b4b01958186ad55d2f615fd1` / `9e7a96481785d6cac4dea3b2e990c49ac278b060` |
| #346 / merge base | `89a18a8225be1b76166af12a15179da291747783` / `7291f6b237fec75add1549c0992c174442180488` |
| Joint tree T44 | `33681cb8ed893a897ca2028d5ada70ca29237978` |

## Findings

Lean paths below are under `TCSlib/Cryptography/`.

| ID | Severity | PR · location | Claim and evidence | Proposed fix |
|---|---|---|---|---|
| G44-01 | **Major** | #340, `Pairing/Assumptions.lean:199`; #346, `IdentityBased/BonehBoyenMachine/Words.lean:261` and neighboring reader proofs | Disclosed exact re-derivations are classified as “no duplicated proved material; nothing for the duplication ledger.” T1’s inline verdict identity is precisely public `TrapdoorPredictor.decide_singleton_eq_true` (`Encryption/PublicKey/TrapdoorPredictor.lean:144`), specialized to the solver-success decision bit. The checkpoint’s `poly_rU`, `poly_rZ`, `poly_rW`, `poly_rS` also re-prove the polynomial-time facts for identical public `InteractiveHandler` projection functions (`Games/Efficiency.lean:538`, `:542`, `:546`, `:550`). Both families are disclosed, but no explicit human acceptance and scheduled repayment is recorded in the audited material or pinned duplication ledger. Policy §1 requires that acceptance, including for mechanically forced copies. | Reuse shared facts, promoting missing generic readers where necessary; or record Seyoon’s explicit acceptance, the shared home and repayment point. Correct both reports’ “nothing for the ledger” dispositions. |
| G44-02 | **Minor** | #346, `BonehBoyenMachine/Draws.lean:58`, `:130`; References entries in `Words.lean:60` and `Handler.lean:62` | `[PS10, Theorem 52.3]` is an inaccurate locator for bounded rejection sampling. That theorem concerns the discrete-log collection of one-way functions; its proof merely remarks that the domain is easy to sample. It does not specify this sampler, fixed coin budget, fallback or statistical bound. The actual formal justification is `Candidates.statClose_sampleBelowL`. This is a genuine source with an inaccurate citation, rather than a fabricated-tag major. | Attribute the bounded sampler to the existing library construction and bound. Retain PS10 §2.8/Theorem 52.3 only as context, and correct the three References entries consistently. |
| G44-03 | **Note** | `pack-r1.md:339`, Assumptions paired-control figures | The prose doubles the totals. Each variant has **2 sealed and 2 unsealed probes**, with **25** expected negative errors: 12 in A and 13 in B. Across strict and coe together: 4 sealed, 4 unsealed and 50 negative errors. The raw logs and plans verify these actual counts, with every reader passing. | Correct “per variant” and “50 … in each.” No replay or control repair is needed. |

The PS10 source supports G44-02’s distinction between its discrete-log theorem and the bounded sampler. [cs.cornell.edu](https://www.cs.cornell.edu/courses/cs4830/2010fa/lecnotes.pdf?utm_source=chatgpt.com)

G44-01 is an acceptance/ledger requirement. The overlaps were disclosed; it is **not** an undisclosed-copy accusation.

## Proof and scope checks

| Question | Result |
|---|---|
| **1 — T1 correctness** | **Pass.** `exists_bdhDistinguisher` constructs a total polynomial-time raw function through `NUPPT.ofPolyTime`, retaining the solver’s coins and advice. On the real tuple law, `coinsCongr` and `expect_sample_equiv` preserve success probability and the unused target sample disappears. On the random law, exchanging independent target/coin samples and encoding injectivity give the inverse-order bound, including outputs outside the encoding range. `accept_bdhGame_le` is pointwise in the security parameter; the bad-order charge is exactly the stated hypothesis. The final negligibility argument adds no assumption. |
| **1 — T4 correctness** | **Pass.** The handler uses total polynomial-time string operations. Negation reduces before subtracting from the modulus; differences and inverses agree with `ZMod`, including inverse zero. Membership precedes message decoding. The per-call identity covers all three oracles and every simulator state. At most one tape entry is consumed per oracle call, so the budget suffices. The sampler is exactly G40-03’s; encoding injectivity supplies its strict modulus bound on every generated group. Machines and error function are chosen before the universally quantified bits and security parameter. |
| **1 — edge cases and sufficiency** | **Pass.** Parameter zero, zero budget, empty coins/advice, absent initialization/challenge, refused target-key queries, repetitions, invalid messages and identity collisions are covered. T4 requires no identity-injectivity/order-growth hypothesis: both simulations use the same zero-inverse convention. Orders zero and one and invalid mathematical group objects are excluded by `BilinearGroup`’s fields; malformed machine strings still receive total polynomial-time behavior. `bb1_sidSecure` is unchanged and reaches `sorryAx` exactly through T2 and T3. T1 is not used by that consumer. |
| **2 — frozen declarations** | **Pass.** Independently reconstructed T44 from the pinned trees; both PR diffs match the pack. T1/T4 headers and statement prose are unchanged. Restoring permitted regions restores the base files. All six T1 and ten T4 mutation controls reject their mutations. The checkpoint inserts only its four imports and Contents section. Public declarations: 101 → 275, exactly 174 additions, with no other frozen declaration changed or removed. |
| **3 — seven readers** | **Pass.** Independent reconstruction is byte-exact: `Defs` +43/−0, `BonehBoyen` +37/−0 at the approved positions. All nine controls reject their mutations. These are precisely the three `oracleImpl_*_onSpec` readers and four approved BB1 encoding/message-space readers, with approved proofs and no added attribute. The casts’ `rfl` witnesses read `Defs`’ own `sidSpec`; consumers use published theorems. |
| **4 — LE-bb1m** | **Pass.** Direct parent/head comparison confirms only deletion of unused `hpp` and reordering of the formula docstring. No statement changes. |
| **5 — duplication** | G44-01 and the grading tables below. No additional undisclosed duplicate was identified. The checkpoint overlaps were reviewed beyond the full-name clash check. |
| **6 — Rule 10** | **Pass.** Recounted **24/24** joint-owner and **16/16** supplement seals: source/probe hashes, conservative request sets reconstructed from collector catalogs, exact source recovery after removing harness insertions, install/EOF coverage, rc 0 and no errors. Strict/coe A/B exclusions match the rulings. Assumptions controls pass at the corrected counts; supplement controls give 24 expected negatives per variant, with all readers/unsealed controls passing. The three skipped owners have **12** row-, source- and probe-identical records against phase 2; its **32/32** earlier seals also recount cleanly. Those owners do not import changed Assumptions, so unchanged inputs justify reuse. The explicit scan has 1,016 items and zero foreign reads; source inspection agrees. |
| **7 — sources** | **Pass apart from G44-02.** BB04 §4.2/Theorem 4.1 and algorithm B are correct sources. The theorem is on printed p. 6 and its proof on pp. 7–8, so the locators are compatible. T1’s independent folklore attribution is accurate under Q10. PS10 Algorithm 43.2 and Definition 181.1 are apt for Euclid and statistical closeness. Inherited missing SOK00/BF01 entries remain outside these fills. |
| **8 — documentation** | **Pass apart from G44-02.** New public docstrings state their formulas; sketches describe the delivered proofs. The sole 15-line sketch omission is pre-existing frozen `bb1SimChal_fresh`. “Handler theorem T1” explicitly names `Games.exists_handlerMachine`, distinguishing it from pairing T1; consistently spelling out “Games” would improve readability. |
| **9 — replay and axioms** | **Pass on supplied evidence.** Independently reconstructed the 16-module downstream set and 1,427-module root/audit closure. All 16 build logs and source bindings recount cleanly: rc 0, no errors, exactly the two T2/T3 admission warnings. Census: **198 → 196**, exactly T1 and T4 removed. Both targets have the standard three axioms and no sorried dependency; the owner census has 604 constants and no nonstandard axioms. State, output-map and snapshot-preservation records are consistent. |
| **10 — disclosures** | G44-03 is an additional pack discrepancy. Other recorded staging/provenance slips do not alter the audited code or conclusions. The shared signing key establishes account-session provenance, not individual authorship. |

The BB04 page locators and the PS10 Euclid/statistical-closeness locators were checked against the primary texts. [crypto.stanford.edu](https://crypto.stanford.edu/~xb/eurocrypt04b/bbibe.pdf?utm_source=chatgpt.com)

The principal bounds checked are

\[
\operatorname{accept}(G.\mathrm{bdhGame}\ A\ \kappa)
\le G.\mathrm{dbdhAdv}\ D\ \kappa+2^{-\kappa}+\delta(\kappa),
\]

\[
q(\kappa)2^{-n}\le(q(\kappa)+1)2^{-\kappa}=\sigma(\kappa),
\qquad n=\kappa+w_G(\kappa)+1.
\]

## Grades: BM-F01–BM-F09

These dispositions do not add to the open-finding counts.

| Finding | Grade / disposition |
|---|---|
| BM-F01 | Agree: note, **closed** by removal of the unused proof. |
| BM-F02 | Agree: minor, **closed** by corrected argument order and explicit security parameter. |
| BM-F03 | Agree: evidence note, **closed**. Independently recounted Oracles controls: 14 negative and 14 reader rows per variant, all as expected. |
| BM-F04 | Agree: note, superseded by landing-head seals and unchanged-input comparisons. |
| BM-F05 | Agree: evidence nits; source/log/hash checks resolve the substantive questions. G44-03 is separate. |
| BM-F06 | Agree: inherited documentation note, outside permitted edits. |
| BM-F07 | Agree: size note; the files exceed the target but remain below the cap. |
| BM-F08 | Agree: disclosed promotion request. The private range-type lemmas derive from published readers without re-proving an existing public IBE theorem. |
| BM-F09 | Agree: suitable machine-specific public glue, with its formula and sketch. |

## Grades: #340’s seven overlap disclosures

| Item | Grade / disposition |
|---|---|
| 1 — raw machine versus `NUPPT.wrap` | Agree. Composition of verified construction layers; the alternative’s bookkeeping does not make this an additional copied theorem. |
| 2 — equality test | Agree. `polyTimeComputable_pairEq` is reused. |
| 3 — projections | Agree. Fixed compositions of published projections; the iterated-first-projection theorem does not supply the required second-projection contract. |
| 4 — target probability | Agree. Tuple-specific application of published probability/injectivity facts; the list-membership bound is a near-alternative. |
| 5 — verdict identity | **Reject “no duplicated proved material / no ledger”: G44-01.** The exact public identity is re-derived inline. Disclosure does not establish acceptance of retained debt. |
| 6 — bad-order bound | Agree as disclosed pattern overlap. The ElGamal safe-prime/index proof is not copied as an interchangeable theorem. |
| 7 — advantage inequality | Agree. Direct absolute-value API use; no matching public Games lemma was identified. |

The checkpoint’s identical round-input projections and polynomial-time facts have the same acceptance gap. Its API obstruction is real, but the required acceptance/repayment record is absent. Other disclosed specializations, casts, encoding-contract applications and simulator comparisons have different contracts or apply existing facts.

## Verification and limits

All **14/14** outer and **549/549** verification-archive checksums pass, with an exact file set. All **186** source-manifest entries pass; **181** Lean source copies bind to pinned git blobs. All **43** bundle sections match their separate copies. The two additionally consulted review archives verify **962/962** and **255/255** inner files and their pinned outer hashes.

The ZIP contains the independent checks, results, mutation-control reruns and pinned duplication ledger. **I did not run a fresh Lean compilation**; compilation/axiom conclusions use the hash-bound supplied replay and probes, independently recounted and checked against the inspected sources.

Gate 40, the T2/T3 fill and #351/#352 are not re-audited. Merge order and snapshot adoption remain maintainer conditions.

**Notation:** `A`: adversary/solver; `D`: reduction distinguisher; `G`: bilinear generator; `κ`: security parameter; `q(κ)`: query budget; `w_G(κ)`: source-group encoding width; `n`: sampler width defined above; `δ(κ)`: bad-order bound; `σ(κ)`: simulation-error bound. T1/T4 and BM-F01–BM-F09 retain the campaign’s labels.

## ===== briefs/pairings/gates/48-bb1-sim-fill/findings-r1.md (records, at ab17e37feb00a677d69f6abd5ff7e427e3b9ef3c) =====

# Gate 48 · round 1 findings (Codex), filed verbatim

Received from Seyoon in chat, 2026-11-17. The referenced `gate48-bb1-sim-evidence.zip` was linked from the auditor's
chat and was not supplied to the maintainer; this file is the auditor's Markdown summary as pasted.

---

**HOLD — 0 blockers, 1 major, 0 minors, 0 notes.**

Audited PR **#357**, Lean head `7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff`, records `e6cdf4d4eed898acd71d48bd60082140eb076cfe`, exchange `827065642ff5965c6f7c51c592f18b9f32dc2811`.

| # | Severity | File · declaration | Finding | Proposed fix |
|---|---|---|---|---|
| **G48-01** | **major** | `BonehBoyenSecurity.lean:128–134` · `bb1_sim_real`, local `h01` | The bad-coin proof re-derives the public Mathlib lemma `abs_sub_le_of_nonneg_of_le`, specialized to real numbers and upper bound `1`. This duplication is unaccepted, and the pack's assertion that no public counterpart exists is incorrect. | Remove `h01` and apply the Mathlib lemma directly. Correct the reuse claim and refresh verification at the repaired head. |

`abs_sub_le_of_nonneg_of_le` takes exactly the four bounds supplied to `h01`, in the same order, and bounds the absolute difference by their common upper bound.

This lemma exists in the **pinned** Mathlib revision `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`: `Mathlib/Algebra/Order/Group/Abs.lean:119–124` generates it through `@[to_additive]`. The audited checkout already uses the identifier in `TCSlib/Cryptography/LWE/BitNoise.lean:110`.

The bad-coin branch can instead use:

```lean
    exact abs_sub_le_of_nonneg_of_le
      (ProbComp.prob_nonneg _ _) (ProbComp.prob_le_one _ _)
      (ProbComp.prob_nonneg _ _) (ProbComp.prob_le_one _ _)
```

This is a proposed proof-only repair, not a tested patch. DL-57 covers the `sidSpec_rng_*` twins; it does not cover this overlap. The contrary reuse claims occur in `pack-r1.md:254–255` and `fill-final-r1/review.md:218–219`. The major grading follows the gate's explicit duplication rule and Gate 44's inline-identity precedent.

The remaining audit checks passed:

| Area | Result |
|---|---|
| Integrity | **11/11** pack checksums and **189/189** verification-archive entries pass. The original phase-2 ZIP and its complete manifest also verify; I recovered its seven omitted entries. |
| Four targets | No correctness defect found. The relational induction generalizes both states; sampling reindexes along the supplied equivalence. T2 uses exactly the frozen bad event and proves identity injectivity on good coins. T3 uses the correct target-group translation. |
| Helpers and edge cases | No false, vacuous, or assumption-like helper found. All nine Step-M cases are covered, including pre-initialization calls, target-key queries, invalid/repeated challenges, and recorded challenges without an identity. Zero parameters/budgets and runs without initialization or challenge are covered. Order `1` and trivial groups are excluded by the existing bundle. |
| Frozen declarations | Independently reproduced **12/12** frozen checks, all **8** mutation controls, and **69 ADDED / 0 CHANGED / 0 REMOVED**. `bb1_sidSecure`, `prob_simulate_rel`, and the frozen sketches remain unchanged. |
| Ten readers | Both blocks are verbatim insertions at their approved anchors, retain the specified pins, restore the base exactly when removed, and reject all **12** insertion mutations. |
| LE-bsf1 | Matches the proposed diff. Apart from the added `rfl` reader `bb1RealState_eq`, all changes are comments. |
| Rule 10 | Independently recounted **36 worker head seals** and **16 base seals**, with source/probe/log bindings. Reconstructed **36/36 phase-2 seal sources** and **64/64 control sources**, matching recorded hashes and plans. Each harness has **485** sealed negatives, each failing once, and **1479** clean other entries. |
| Exceptions and unfolds | The abbrev reader's positive-only treatment and `RealReads` projection treatment satisfy the recorded rulings. The recovered scan contains **527** entries and **zero foreign definitions**; I inspected its non-theorem classes. |
| Other duplication | DL-57 records both twins, acceptance, and Stage-2 repayment. Searches across all **529** cryptography files and comparison with #355's pinned `Games/Tapes.lean` found no further undisclosed duplication. The eager/relational instances apply public framework results. |
| Sources and documentation | BB04 quotation checks match the supplied December-2004 transcription. Locators, glue notes, variant descriptions, sketches, file sizes, and widths are acceptable. |
| Replay | All **19/19** build sources and logs bind to the audited head. Recovered state contains **1432** modules; reused records are unchanged. Recorded builds have rc 0 and no error, warning, or `sorry` diagnostic. Admissions fall **196 → 192**, exactly the four targets. |
| Axioms | **76** named constants and **325** owner constants have no nonstandard axioms. All six traces are empty, including `bb1_sidSecure`'s **20,373**-constant closure. The intentional sorry control is caught by both checks. |

The prior review findings are graded separately from the new Gate-48 count:

| Review finding | Grade and disposition |
|---|---|
| BSF-F01 | Agree: minor, process only; remains disclosed. Fix future rebase/signing instructions. No history rewrite requested. |
| BSF-F02 | Agree: minor, closed by `bb1RealState_eq`. |
| BSF-F03 | Agree: minor, closed by LE-bsf1's documentation changes. |
| BSF-F04 | Regrade the pre-acceptance gap as major under the duplication rule; **closed at this pin** by Q1 and DL-57. |
| BSF-F05 | Agree: information, accepted; projections and consumer seals provide the required treatment. |
| BSF-F06 | Agree: information; the missing checkpoint acknowledgment is disclosed and resolutions are traceable. |
| BSF-F07 | Agree: information / accepted placement debt; promotion is recorded for Stage 2. |
| BSF-F08 | Agree: maintainer merge condition, outside this audit. |

I did **not** execute Lean afresh. I independently checked the static surface, regenerated probe hashes, recounted raw worker logs, and verified the recorded native-build and axiom logs. Phase-2 raw seal/probe logs remain on the maintainer host; the supplied result tables, exact regenerated sources, and worker recounts support their reported outcomes.

#351/#352 and the closed Gates 40/44 were not re-audited. No dispatch or merge was performed.

## ===== blueprint/src/references/barthe-gregoire-zanella-2009-certified-proofs.md (records, at ab17e37feb00a677d69f6abd5ff7e427e3b9ef3c) =====

<!-- generated-by: maintainer transcription of the passages used (DW-8) -->
<!-- source-pdf-sha256: 216f8cd86ce5e077730bcf9d5ed1a90131f0107d23e64f249c7df02690b4678a -->
<!-- validation-status: scoped transcription for DW-8; awaiting Codex source review -->

# Formal Certification of Code-Based Cryptographic Proofs

Gilles Barthe, Benjamin Grégoire and Santiago Zanella. *POPL 2009* (36th ACM
SIGPLAN-SIGACT Symposium on Principles of Programming Languages); tag `BGZ09`. Uploaded
copy: 12 PDF pages.

*Transcription note.* The byline of this version reads "Gilles Barthe, Benjamin Grégoire,
Santiago Zanella" (Microsoft Research – INRIA Joint Centre, France), without the third
author's later surname "Zanella Béguelin" used in the library's reference list.

**Scope.** Only the passages that the relational simulation lemma uses are transcribed
(DW-8; pairing ruling Q11): §3.4 (adversaries and the oracles they may call), the opening
of §4 (why a relational Hoare logic, and Shoup's three categories of proof step), §4.1
(the lifting of a relation to distributions, Definition 5 of pRHL judgments, the derived
rules of Figure 5, and the lemmas $(=_{[\![]\!]})$ and $(\le_{[\![]\!]})$ that move a pRHL
judgment to equalities of expectations), §4.2 (observational equivalence and its two
invariant-carrying variants $\vDash_\varphi$ and $\vDash_{\Psi,\Phi}$), and §5.2 (Lemma 1,
lazy/eager sampling, and the replacement of a lazy random oracle $O_l$ by an eager one
$O_e$ inside an arbitrary context). §§1–2, §3.1–§3.3, §5.1, §5.3, §6 and §§7–9 are not
transcribed. The PDF is not committed. Physical and printed pages coincide.

**On the raw extraction.** The paper is set in two columns. Poppler's reading order
interleaves the columns around figures and footnotes, so in
`barthe-gregoire-zanella-2009-certified-proofs.raw.md` a section heading can appear *after*
the text it heads (§3.4's heading on p. 6 is the clearest case). The raw file is the
mechanical extraction and is left as Poppler produced it; this transcription restores the
reading order, which was checked against the page images (rendered at 170 dpi).
Mathematics is set in LaTeX; the wording is the paper's. Notes marked *Transcription note*
are not part of the source.

<a id="pdf-216f8cd86ce5-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.95 -->

**Section 3.4, Adversaries (p. 6).** In order to reason formally about security, we make
explicit which variables and procedures are accessible to adversaries, and provide a simple
analysis to check whether an adversary respects its policy. Given a set of procedure
identifiers $\mathcal O$ (the procedures that may be called by the adversary), and sets of
global variables $\mathcal G_A$ (those that can be read and written by the adversary) and
$\mathcal G_{ro}$ (those that the adversary can only read), we say that an adversary
$\mathcal A$ is well-formed in an environment $E$ if the judgment
$\vdash_{\mathrm{wf}}\mathcal A$ can be derived using the rules in Fig. 4. These rules
guarantee that each time a variable is written by the adversary, the adversary has the
right to do so; and that each time a variable is read by the adversary, it is either a
global variable in $\mathcal G_A\cup\mathcal G_{ro}$ or a local variable previously
initialized. **A well-formed adversary is free to call oracles, but any other procedure it
calls must be a well-formed adversary itself.**

Additional constraints may be imposed on adversaries. For example, exact security proofs
usually impose an upper bound to the number of calls adversaries can make to a given
oracle, whereas for some properties such as IND-CCA2 there are some restrictions on the
parameters with which the oracles may be called. Likewise, some proofs impose extra
conditions such as forbidding repeated or malformed queries. These kinds of properties can
be formalized using lists that record the oracle calls, and verifying as postcondition that
the calls were legitimate.

*Transcription note.* Figure 4 ("Static analysis for well-formedness of adversaries", p. 6)
is a rule figure and is not transcribed; only the prose that states its guarantees is.

<a id="pdf-216f8cd86ce5-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=0.95 -->

**Section 4, Relational Hoare Logic, opening (pp. 6–7).** Shoup [31] classifies proof steps
into three categories: transitions based on indistinguishability—which typically involve
applying a security hypothesis, e.g. the DDH assumption—; transitions based on failure
events—which typically amount to bound the probability of bad, as in the Switching
Lemma—; and bridging steps—which correspond to replacing or reorganizing code in a way
that is not observable by adversaries. In some circumstances, a bridging transition from
$G_1$ to $G_2$ may replace a program fragment $P$ by another fragment $P'$ observationally
equivalent to $P$. In general, however, $P$ and $P'$ are only observationally equivalent in
the context where the replacement is done. Such transitions are supported through a
relational Hoare logic, that generalizes observational equivalence through preconditions
and postconditions which we use to characterize the context where the replacement is valid.
Besides, we use relational Hoare logic to establish (in)equalities between probabilities of
two events, as shown by the lemmas $(=_{[\![]\!]})$ and $(\le_{[\![]\!]})$ below, and to
establish program invariants, e.g. in the proof of the Switching Lemma in Sec. 2.2.

*Transcription note.* Reference "[31]" is Shoup's *Sequences of games* (tag `Sho04` in this
library); the three categories named here are the three transition types of
`shoup-2004-sequences-of-games.md`.

<a id="pdf-216f8cd86ce5-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.95 -->

**Section 4.1, Probabilistic Relational Hoare Logic (pRHL) (p. 7).** Our logic pRHL
elaborates on and extends to probabilistic programs Benton's Relational Hoare Logic [9].
Benton's logic uses judgments of the form $\vdash G_1\sim G_2:\Psi\Rightarrow\Phi$, and
relates the evaluation of a program $G_1$ to the evaluation of a program $G_2$ w.r.t. a
precondition $\Psi$ and a postcondition $\Phi$, both defined as relations on deterministic
states. Such a judgment states that for any initial memories $m_1$ and $m_2$ satisfying the
precondition $m_1\,\Psi\,m_2$, if the evaluations of $G_1$ in $m_1$ and $G_2$ in $m_2$
terminate with final memories $m_1'$ and $m_2'$ respectively, then $m_1'\,\Phi\,m_2'$
holds. In a probabilistic setting, the evaluation of a program w.r.t. an initial memory
yields a (sub-)distribution. In order to give a meaning to the above judgment, one
therefore needs to lift relations over memories into relations over distributions. We
follow early work on probabilistic bisimulations [21]. The lifting to distributions of a
unary predicate $P$ and of a binary relation $\Phi$ are respectively defined as

$$
\begin{aligned}
\mathsf{range}\ P\ \mu &\stackrel{\mathrm{def}}{=}
  \forall f.\ (\forall a.\ P\,a\Rightarrow f\,a=0)\Rightarrow \mu\,f=0\\
\mu_1\sim_\Phi\mu_2 &\stackrel{\mathrm{def}}{=}
  \exists\mu.\ \pi_1(\mu)=\mu_1\wedge\pi_2(\mu)=\mu_2\wedge\mathsf{range}\ \Phi\ \mu
\end{aligned}
$$

where the projections of $\mu$ are defined as

$$
\pi_1(\mu)\stackrel{\mathrm{def}}{=}\mathsf{bind}\ \mu\ (\lambda(x,y).\mathsf{unit}\ x)
\qquad
\pi_2(\mu)\stackrel{\mathrm{def}}{=}\mathsf{bind}\ \mu\ (\lambda(x,y).\mathsf{unit}\ y)
$$

This way of lifting relations over memories to relations over distributions is a
generalization to arbitrary relations of the definition of Sabelfeld and Sands [29]. Their
definition applies only to PERs, whereas our definition applies to arbitrary relations.
Nevertheless, both definitions coincide for PERs as established by Jonsson, Larsen and
Yi [21].

<a id="pdf-216f8cd86ce5-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.95 -->

**Definition 5 (pRHL judgments) (p. 7).** Programs $G_1$ and $G_2$ are equivalent w.r.t.
precondition $\Psi$ and postcondition $\Phi$ iff

$$
\vDash G_1\sim G_2:\Psi\Rightarrow\Phi\ \stackrel{\mathrm{def}}{=}\
\forall\,m_1\,m_2.\ m_1\,\Psi\,m_2\Rightarrow
[\![G_1]\!]\,m_1\sim_\Phi[\![G_2]\!]\,m_2
$$

Our approach slightly departs from Benton's: rather than defining the rules for pRHL and
proving them sound w.r.t. the meaning of judgments, we place ourselves in a semantic
setting and derive the rules as lemmas. This allows to easily extend the system by deriving
extra rules, or even to resort to the semantic definition if the system turns out to be
insufficient.

Figure 5 gathers some representative derived rules. To improve readability, in the figure
and in the remainder of the paper we let $e\langle i\rangle$ denote
$\lambda m_1\,m_2.\ [\![e]\!]\,m_i=\mathsf{true}$, where $e$ is a boolean expression. As
pRHL allows for arbitrary relations, we freely use higher-order logic; in particular,
$\mathsf{PER}$ and $\mathsf{SYM}$ are predicates over relations that stand for *partial
equivalence relation* and *symmetric relation* respectively.

<a id="pdf-216f8cd86ce5-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.95 -->

**Section 4.1, one-sided variants and the rules that are new in pRHL (p. 7).** There are
two points worth noting. First, most rules admit, in addition to their symmetrical version
of Fig. 5, one-sided (left and right) variants, e.g. for assignments

$$
\frac{m_1\,\Phi'\,m_2\stackrel{\mathrm{def}}{=}(m_1\{[\![e_1]\!]m_1/x_1\})\,\Phi\,m_2}
{\vDash E_1,x_1\leftarrow e_1\sim E_2,\mathsf{nil}:\Phi'\Rightarrow\Phi}
$$

Second, some rules of pRHL do not appear in RHL, or generalize existing rules. The rule
[R-Case] allows to do a case analysis on the evaluation of an arbitrary relation in the
initial memories. Together with simple rules in the spirit of

$$
\frac{\vDash E_1,c_1\sim E_2,c:\Psi\wedge e\langle1\rangle\Rightarrow\Phi}
{\vDash E_1,\mathsf{if}\ e\ \mathsf{then}\ c_1\ \mathsf{else}\ c_2\sim E_2,c:
 \Psi\wedge e\langle1\rangle\Rightarrow\Phi}
$$

it subsumes [R-Cond] and allows to prove judgments that would otherwise not be derivable,
such as the equivalence between $(\mathsf{if}\ e\ \mathsf{then}\ c_1\ \mathsf{else}\ c_2)$
and $(\mathsf{if}\ \neg e\ \mathsf{then}\ c_2\ \mathsf{else}\ c_1)$. We also use [R-Case]
to prove the correctness of dataflow analyses that exploit the information provided by
entering branches.

In addition, we often use the rule [R-Inv] that generalizes the rule [R-Sym] to inverse of
relations

$$
\frac{\vDash G_1\sim G_2:\Psi\Rightarrow\Phi}
{\vDash G_2\sim G_1:\Psi^{-1}\Rightarrow\Phi^{-1}}\ \text{[R-Inv]}
$$

and we make an extensive use of the rule [R-Comp] that generalizes the rule [R-Tr] to
composition of relations

$$
\frac{\vDash G_1\sim G:\Psi'\Rightarrow\Phi'\qquad\vDash G\sim G_2:\Psi''\Rightarrow\Phi''}
{\vDash G_1\sim G_2:\Psi'\circ\Psi''\Rightarrow\Phi'\circ\Phi''}\ \text{[R-Comp]}
$$

The benefits of the rule [R-Comp], as opposed to [R-Tr], are illustrated by considering
"independent" preconditions and postconditions of the form
$\Psi\stackrel{\mathrm{def}}{=}\lambda x\,y.\Psi_1\,x\wedge\Psi_2\,y$ and
$\Phi\stackrel{\mathrm{def}}{=}\lambda x\,y.\Phi_1\,x\wedge\Phi_2\,y$. In order to apply
the rule [R-Tr] to $G_1$ and $G_2$, we are essentially forced to have $\Psi_1=\Psi_2$ and
$\Phi_1=\Phi_2$, and furthermore we must also choose the same pre and postcondition for the
intermediate game $G$. This constraint makes the rule [R-Tr] impractical, we use instead
the rule [R-Comp] to introduce intermediate games that do not satisfy the same
specification as $G_1$ or $G_2$.

*Footnote 4 (p. 7).* The machine-checked rule requires that $\Phi,\Phi'$ are decidable, and
uses **Set**-valued existential quantification $\exists_{\mathbf{Set}}$ in the composition
for preconditions, i.e.
$x\,(\Psi\circ\Psi')\,z\stackrel{\mathrm{def}}{=}\exists_{\mathbf{Set}}y.\ x\,\Psi\,y\wedge y\,\Psi'z$.

<a id="pdf-216f8cd86ce5-p007-b004"></a>
<!-- pdf-source: page=7; block=4; confidence=0.95 -->

**Section 4.1, the rule [R-Rand] and its bijection premise (p. 7).** The rule [R-Rand] is
also (obviously) not present in RHL. Let
$\mathbb I_x\stackrel{\mathrm{def}}{=}(\lambda v.\mathsf{if}\ x=v\ \mathsf{then}\ 1\
\mathsf{else}\ 0)$, and define the support of a distribution,
$\mathsf{supp}([\![d]\!]\,m)$, by the clause

$$
v\in\mathsf{supp}([\![d]\!]\,m)\iff[\![d]\!]\,m\,\mathbb I_v\neq 0
$$

Finally, let $[\![d_1]\!]\,m_1=_g[\![d_2]\!]\,m_2$ iff there exists a set $X$ and a
bijection $g:X\to X$ such that
$\mathsf{supp}([\![d_1]\!]\,m_1)=\mathsf{supp}([\![d_2]\!]\,m_2)=X$ and
$[\![d_1]\!]\,m_1\,\mathbb I_a=[\![d_2]\!]\,m_2\,\mathbb I_{(g\,a)}$ for all $a$ in $X$. To
apply rule [R-Rand], it is necessary to exhibit a function $f$ such that for all memories
$m_1$ and $m_2$, $[\![d_1]\!]\,m_1=_{f\,m_1\,m_2}[\![d_2]\!]\,m_2$. Thus, if
$d_1=d_2=[0..n]$ for some constant $n$, and we take $f$ to be the identity function, the
premise simplifies to the expected,

$$
m_1\,\Psi\,m_2\stackrel{\mathrm{def}}{=}
\forall\,v\in[0..n].\ (m_1\{v/x_1\})\,\Phi\,(m_2\{v/x_2\})
$$

Section 5.3 shows that the generality of the rule is required for applications such as
optimistic sampling.

<a id="pdf-216f8cd86ce5-p007-b005"></a>
<!-- pdf-source: page=7; block=5; confidence=0.95 -->

**Section 4.1, pRHL judgments as equalities of expectations — the lemma
$(=_{[\![]\!]})$ (p. 7).** It is often fruitful to understand pRHL judgments in terms of
the inability of the postcondition to separate between the two commands of the judgment.
Define two functions $f$ and $g$ to be equivalent w.r.t. a predicate $\Phi$ iff

$$
f=_\Phi g\ \stackrel{\mathrm{def}}{=}\ \forall\,m_1\,m_2.\ m_1\,\Phi\,m_2\Rightarrow
f(m_1)=g(m_2)
$$

The definition of pRHL judgments entails

$$
\left.
\begin{array}{l}
\vDash G_1\sim G_2:\Psi\Rightarrow\Phi\\
f=_\Phi g\\
m_1\,\Psi\,m_2
\end{array}
\right\}
\Rightarrow\ [\![G_1]\!]\,m_1\,f=[\![G_2]\!]\,m_2\,g
\qquad (=_{[\![]\!]})
$$

*Transcription note.* $[\![G]\!]\,m\,f$ is the expectation of $f$ under the
(sub-)distribution that running $G$ from memory $m$ produces. The paper's semantics (§3.2,
not transcribed) is given in the **measure monad**
$\mathcal M(X)\stackrel{\mathrm{def}}{=}(X\to[0,1])\to[0,1]$, with
$[\![c]\!]\,m:\mathcal M(\mathcal M)$ (p. 5), so a distribution *is* a function on
functions and $[\![G]\!]\,m\,f$ is literally its application to $f$. The paper notes that
$\mathcal M(X)$ "was proposed by Audebaud and Paulin [4] as a variant of the expectation
monad used by Ramsey and Pfeffer [27]" (p. 5).

<a id="pdf-216f8cd86ce5-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.95 -->

**Figure 5, selection of derived rules of pRHL (p. 8).**

$$
\vDash E_1,\mathsf{nil}\sim E_2,\mathsf{nil}:\Phi\Rightarrow\Phi\quad\text{[R-Skip]}
$$

$$
\frac{\vDash E_1,c_1\sim E_2,c_2:\Phi\Rightarrow\Phi'\qquad
      \vDash E_1,c_1'\sim E_2,c_2':\Phi'\Rightarrow\Phi''}
{\vDash E_1,c_1;c_1'\sim E_2,c_2;c_2':\Phi\Rightarrow\Phi''}\ \text{[R-Seq]}
$$

$$
\vDash E_1,x_1\leftarrow e_1\sim E_2,x_2\leftarrow e_2:
(\lambda\,m_1\,m_2.\ (m_1\{[\![e_1]\!]m_1/x_1\})\,\Phi\,(m_2\{[\![e_2]\!]m_2/x_2\}))
\Rightarrow\Phi\quad\text{[R-Ass]}
$$

$$
\frac{m_1\,\Psi\,m_2\stackrel{\mathrm{def}}{=}
 [\![d_1]\!]m_1=_{f\,m_1\,m_2}[\![d_2]\!]m_2\wedge
 \forall\,v\in\mathsf{supp}([\![d_1]\!]m_1).\ (m_1\{v/x_1\})\,\Phi\,(m_2\{f\,m_1\,m_2\,v/x_2\})}
{\vDash E_1,x_1\xleftarrow{\$}d_1\sim E_2,x_2\xleftarrow{\$}d_2:\Psi\Rightarrow\Phi}
\ \text{[R-Rand]}
$$

$$
\frac{\forall m_1\,m_2.\ m_1\,\Psi\,m_2\Rightarrow[\![e_1]\!]\,m_1=[\![e_2]\!]\,m_2
 \qquad\vDash E_1,c_1\sim E_2,c_2:\Psi\wedge e_1\langle1\rangle\Rightarrow\Phi
 \qquad\vDash E_1,c_1'\sim E_2,c_2':\Psi\wedge\neg e_1\langle1\rangle\Rightarrow\Phi}
{\vDash E_1,\mathsf{if}\ e_1\ \mathsf{then}\ c_1\ \mathsf{else}\ c_1'\sim
 E_2,\mathsf{if}\ e_2\ \mathsf{then}\ c_2\ \mathsf{else}\ c_2':\Psi\Rightarrow\Phi}
\ \text{[R-Cond]}
$$

$$
\frac{\forall m_1\,m_2.\ m_1\,\Phi\,m_2\Rightarrow[\![e_1]\!]\,m_1=[\![e_2]\!]\,m_2
 \qquad\vDash E_1,c_1\sim E_2,c_2:\Phi\wedge e_1\langle1\rangle\Rightarrow\Phi}
{\vDash E_1,\mathsf{while}\ e_1\ \mathsf{do}\ c_1\sim
 E_2,\mathsf{while}\ e_2\ \mathsf{do}\ c_2:\Phi\Rightarrow\Phi\wedge\neg e_1\langle1\rangle}
\ \text{[R-Whl]}
$$

$$
\frac{\vDash G_1\sim G_2:\Psi'\Rightarrow\Phi'\quad
 \forall m_1\,m_2.\ m_1\,\Psi\,m_2\Rightarrow m_1\,\Psi'\,m_2\quad
 \forall m_1\,m_2.\ m_1\,\Phi'\,m_2\Rightarrow m_1\,\Phi\,m_2}
{\vDash G_1\sim G_2:\Psi\Rightarrow\Phi}\ \text{[R-Sub]}
$$

$$
\frac{\vDash G_1\sim G_2:\Psi\Rightarrow\Phi\quad\mathsf{SYM}(\Psi)\quad\mathsf{SYM}(\Phi)}
{\vDash G_2\sim G_1:\Psi\Rightarrow\Phi}\ \text{[R-Sym]}
\qquad
\frac{\vDash G_1\sim G:\Psi\Rightarrow\Phi\quad\vDash G\sim G_2:\Psi\Rightarrow\Phi
 \quad\mathsf{PER}(\Psi)\quad\mathsf{PER}(\Phi)}
{\vDash G_1\sim G_2:\Psi\Rightarrow\Phi}\ \text{[R-Tr]}
$$

$$
\frac{\vDash G_1\sim G_2:\Psi\wedge\Psi'\Rightarrow\Phi\quad
 \vDash G_1\sim G_2:\Psi\wedge\neg\,\Psi'\Rightarrow\Phi}
{\vDash G_1\sim G_2:\Psi\Rightarrow\Phi}\ \text{[R-Case]}
$$

<a id="pdf-216f8cd86ce5-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.95 -->

**Section 4.1, termination sensitivity and the lemma $(\le_{[\![]\!]})$ (p. 8).** By
instantiating $f$ and $g$ to $\mathbb 1$, one can observe that observational equivalence
enjoys some form of termination sensitivity

$$
(\vDash G_1\sim G_2:\Psi\Rightarrow\Phi)\wedge m_1\,\Psi\,m_2\Rightarrow
[\![G_1]\!]\,m_1\,\mathbb 1=[\![G_2]\!]\,m_2\,\mathbb 1
$$

This interpretation of pRHL judgments is strongly connected to the relation between
relational logics and information flow [3, 9]. We extensively use $(=_{[\![]\!]})$, and its
variant $(\le_{[\![]\!]})$ below, to fall back from the world of pRHL into the world of
probabilities, in which security statements are expressed;

$$
\left.
\begin{array}{l}
\vDash G_1\sim G_2:\Psi\Rightarrow\Phi\\
f\le_\Phi g\\
m_1\,\Psi\,m_2
\end{array}
\right\}
\Rightarrow\ [\![G_1]\!]\,m_1\,f\le[\![G_2]\!]\,m_2\,g
\qquad (\le_{[\![]\!]})
$$

where $f\le_\Phi g\stackrel{\mathrm{def}}{=}\forall\,m_1\,m_2.\ m_1\,\Phi\,m_2\Rightarrow
f(m_1)\le g(m_2)$.

<a id="pdf-216f8cd86ce5-p008-b003"></a>
<!-- pdf-source: page=8; block=3; confidence=0.95 -->

**Section 4.2, Observational equivalence (p. 8).** Observational equivalence is derived as
an instance of relational Hoare judgments in which pre and postconditions are restricted to
relations based on equality over a subset of variables. Given a set $X$ of variables, we
define $=_X$ as

$$
m_1=_X m_2\ \stackrel{\mathrm{def}}{=}\ \forall\,x\in X.\ m_1\,x=m_2\,x
$$

Then, the observational equivalence of $G_1$ and $G_2$ w.r.t. an input set $I$ and an
output set $O$ is defined as

$$
\vDash G_1\simeq^I_O G_2\ \stackrel{\mathrm{def}}{=}\
\vDash G_1\sim G_2:\ =_I\ \Rightarrow\ =_O
$$

All derived rules for pRHL can be specialized to the case of observational equivalence. For
example, we have

$$
\frac{\vDash e_1\simeq^I e_2\qquad\vDash E_1,c_1\simeq^I_O E_2,c_2
 \qquad\vDash E_1,c_1'\simeq^I_O E_2,c_2'}
{\vDash E_1,\mathsf{if}\ e_1\ \mathsf{then}\ c_1\ \mathsf{else}\ c_1'\simeq^I_O
 E_2,\mathsf{if}\ e_2\ \mathsf{then}\ c_2\ \mathsf{else}\ c_2'}
$$

where $\vDash e_1\simeq^I e_2$ iff for every memories $m_1$ and $m_2$, $m_1=_I m_2$ implies
$[\![e_1]\!]\,m_1=[\![e_2]\!]\,m_2$.

To support automation, CertiCrypt implements a calculus of variable dependencies and
provides two functions, $\mathsf{eqobsIn}$ and $\mathsf{eqobsOut}$, that given a command
$c$ and a set $O$ (respectively $I$) of output (input) variables compute a set $I$ ($O$) of
input (output) variables such that $\vDash E_1,c\simeq^I_O E_2,c$. **CertiCrypt also
provides tactics for two variants of observational equivalence that are widely used in
game-based proofs, namely**

$$
\begin{aligned}
\vDash_\varphi G_1\simeq^I_O G_2\ &\stackrel{\mathrm{def}}{=}\
  \vDash G_1\sim G_2:\ =_I\wedge\varphi\ \Rightarrow\ =_O\wedge\varphi\\
\vDash_{\Psi,\Phi} G_1\simeq^I_O G_2\ &\stackrel{\mathrm{def}}{=}\
  \vDash G_1\sim G_2:\ =_I\wedge\Psi\ \Rightarrow\ =_O\wedge\Phi
\end{aligned}
$$

These tactics use a (sound but incomplete) weakest precondition calculus for relational
judgments.

<a id="pdf-216f8cd86ce5-p008-b004"></a>
<!-- pdf-source: page=8; block=4; confidence=0.95 -->

**Section 5, Proof methods for bridging steps, opening (p. 8).** CertiCrypt provides a
powerful set of tactics and algebraic equivalences to automate bridging steps. Most tactics
rely on an implementation of a certified optimizer for pWHILE, with the exception of *lazy
sampling* which has an ad hoc implementation.

<a id="pdf-216f8cd86ce5-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.95 -->

**Section 5.2, Lazy sampling (p. 9).** It is sometimes convenient to defer random choices
in games until they are actually needed, or conversely, to make random choices as early as
possible. The lazy sampling technique, allows to delay the random sampling of a value until
the point in the program where it is first used. Conversely, eager sampling allows to
choose a random value, which would be otherwise sampled later, at the beginning of a game.
These techniques are presented in [8], where the authors discuss some of its subtleties. In
this section we present a syntax-oriented criterion for the correctness of lazy sampling
that can be applied provided the sampling is adequately guarded. **Here by context we mean
a program context with multiple holes that may appear either in the main program or any of
the procedures in the environment.**

<a id="pdf-216f8cd86ce5-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.95 -->

**Lemma 1 (Lazy/eager sampling) (p. 9).** Let $C[\cdot]$ be a context, $c_1$ and $c_2$
commands, $e$ a boolean expression, $d$ a distribution expression, and $z$ a variable, such
that $C[\cdot]$ does not modify $\mathrm{fv}(e)\cup\mathrm{fv}(d)$ and does not use $z$.
Assume

1. $\vDash z\xleftarrow{\$}d;c_1;\mathsf{if}\ e\ \mathsf{then}\ z\xleftarrow{\$}d\ \sim\
   z\xleftarrow{\$}d;c_1\ :\ (=\wedge\,e\langle1\rangle)\Rightarrow\ =$
2. $\vDash c_2\sim c_2\ :\ (=\wedge\,\neg e\langle1\rangle)\Rightarrow
   (=\wedge\,\neg e\langle1\rangle)$

Let $c=\mathsf{if}\ e\ \mathsf{then}\ z\xleftarrow{\$}d;c_1\ \mathsf{else}\ c_2$ and
$c'=\mathsf{if}\ e\ \mathsf{then}\ c_1\ \mathsf{else}\ c_2$. Then,

$$
\vDash C[c];\mathsf{if}\ e\ \mathsf{then}\ z\xleftarrow{\$}d\ \sim\
z\xleftarrow{\$}d;C[c']\ :\ (=\wedge\,e\langle1\rangle)\Rightarrow\ =
$$

Intuitively, in the above lemma $e$ indicates whether $z$ has not been used in the game
since it was last sampled. If it has not been used, then it is perfectly fine to resample
it. The first two hypotheses ensure that $e$ has exactly this meaning, $c_1$ must set it to
false if it has used the value sampled in $z$, and $c_2$ must not reset $e$ if it is false.
The first hypothesis is the one that allows to swap $c_1$ with $z\xleftarrow{\$}d$,
provided the value of $z$ is not used in $c_1$. Note that, for clarity, we have omitted
environments in the above lemma, and so the second hypothesis is not as trivial as it may
seem because both programs may have different environments.

<a id="pdf-216f8cd86ce5-p009-b003"></a>
<!-- pdf-source: page=9; block=3; confidence=0.95 -->

**Section 5.2, replacing a lazy random oracle by an eager one (pp. 9–10).** Suppose we want
to eagerly sample the answer that a random oracle

$$
O_l(x)\stackrel{\mathrm{def}}{=}
\mathsf{if}\ x\notin\mathrm{dom}(L)\ \mathsf{then}\ y\xleftarrow{\$}d;\
L\leftarrow(x,y)::L;\ \mathsf{return}\ L[x]
$$

gives to a particular query $x'$, i.e. we want to transform $O_l$ into

$$
\begin{aligned}
O_e(x)\stackrel{\mathrm{def}}{=}\ &\mathsf{if}\ x\notin\mathrm{dom}(L)\ \mathsf{then}\\
&\qquad\mathsf{if}\ x=x'\ \mathsf{then}\ y\leftarrow y'\ \mathsf{else}\ y\xleftarrow{\$}d;\\
&\qquad L\leftarrow(x,y)::L\\
&\mathsf{return}\ L[x]
\end{aligned}
$$

Define
$O_l'(x)\stackrel{\mathrm{def}}{=}\mathsf{if}\ x'\notin\mathrm{dom}(L)\ \mathsf{then}\
y'\xleftarrow{\$}d;O_e(x)\ \mathsf{else}\ O_l(x)$,
$O_e'(x)\stackrel{\mathrm{def}}{=}\mathsf{if}\ x'\notin\mathrm{dom}(L)\ \mathsf{then}\
O_e(x)\ \mathsf{else}\ O_l(x)$, both returning $L[x]$. **Oracles $O_l$ and $O_e$ result
semantically equivalent to $O_l'$ and $O_e'$, respectively.**

<a id="pdf-216f8cd86ce5-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.95 -->

**Section 5.2, the oracle replacement, conclusion (p. 10).** Lemma 1 can be applied taking
$e=x'\notin\mathrm{dom}(L)$, $z=y'$, and $c_1=O_e(x)$, $c_2=O_l(x)$ **to safely replace
oracle $O_l$ by oracle $O_e$ in the environment of a program**, sampling $y'$ at the
beginning. Whenever a bound for the number of queries to a random oracle is known in
advance, the above trick can be iteratively applied to completely remove randomness from
the oracle code, as it is done in the proof of the Switching Lemma in Sec. 2.2.

## ===== blueprint/src/references/shoup-2004-sequences-of-games.md (records, at ab17e37feb00a677d69f6abd5ff7e427e3b9ef3c) =====

<!-- generated-by: maintainer transcription of the passages used (DW-8) -->
<!-- source-pdf-sha256: fde1f65e83ec85297f58840bf87de15fb68e91ada8aefaf77db3b153cf826820 -->
<!-- validation-status: scoped transcription for DW-8; awaiting Codex source review -->

# Sequences of Games: A Tool for Taming Complexity in Security Proofs

Victor Shoup. Cryptology ePrint Archive, Report 2004/332 (tag `Sho04`). Uploaded copy: the
revision dated **January 18, 2006**, 33 PDF pages; the title page records "First public
version: Nov. 30, 2004".

**Scope.** Only the passages that the relational simulation lemma uses are transcribed
(DW-8; pairing ruling Q11): §1 (Introduction) and §1.1 (The Basic Idea), which set up the
sequence-of-games framework and give the three transition types — transitions based on
indistinguishability, transitions based on failure events (with Lemma 1, the Difference
Lemma, and its generalization) and **bridging steps**. One worked bridging step is
transcribed as context, from §4.2 (Game 2 of the universal-hash input-extension proof,
p. 13), because it is the kind of state-reformulation step the cited lemma abstracts. The
PDF is not committed. Physical and printed pages coincide. The scoped raw extraction is
`shoup-2004-sequences-of-games.raw.md`. Mathematics is set in LaTeX; the wording is the
paper's. Notes marked *Transcription note* are not part of the source.

<a id="pdf-fde1f65e83ec-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.95 -->

**Title and abstract (p. 1).** Sequences of Games: A Tool for Taming Complexity in
Security Proofs. Victor Shoup. January 18, 2006.

> **Abstract.** This paper is brief tutorial on a technique for structuring security proofs
> as sequences games.

*Transcription note.* The abstract is transcribed as printed, including "is brief tutorial"
and "sequences games"; neither is a transcription slip.

<a id="pdf-fde1f65e83ec-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.95 -->

**Section 1, Introduction (p. 1).** Security proofs in cryptography may sometimes be
organized as sequences of games. In certain circumstances, this can be a useful tool in
taming the complexity of security proofs that might otherwise become so messy, complicated,
and subtle as to be nearly impossible to verify. This technique appears in the literature in
various styles, and with various degrees of rigor and formality. This paper is meant to
serve as a brief tutorial on one particular "style" of employing this technique, which seems
to achieve a reasonable level of mathematical rigor and clarity, while not getting bogged
down with too much formalism or overly restrictive rules. We do not make any particular
claims of originality — it is simply hoped that others might profit from some of the ideas
discussed here in reasoning about security.

At the outset, it should be noted that this technique is certainly not applicable to all
security proofs. Moreover, even when this technique is applicable, it is only a tool for
organizing a proof — the actual ideas for a cryptographic construction and security analysis
must come from elsewhere.

<a id="pdf-fde1f65e83ec-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=0.95 -->

**Section 1.1, The Basic Idea (p. 1).** Security for cryptograptic primitives is typically
defined as an attack game played between an adversary and some benign entity, which we call
the challenger. Both adversary and challenger are probabilstic processes that communicate
with each other, and so we can model the game as a probability space. Typically, the
definition of security is tied to some particular event $S$. Security means that for every
"efficient" adversary, the probability that event $S$ occurs is "very close to" some
specified "target probabilty": typically, either $0$, $1/2$, or the probability of some
event $T$ in some other game in which the same adversary is interacting with a different
challenger.

*Transcription note.* "cryptograptic", "probabilstic" and "probabilty" are transcribed as
printed.

<a id="pdf-fde1f65e83ec-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.95 -->

**Section 1.1, the sequence-of-games framework (p. 2).** Now, to prove security using the
sequence-of-games approach, one prodceeds as follows. One constructs a sequence of games,
Game 0, Game 1, …, Game $n$, where Game 0 is the original attack game with respect to a
given adversary and cryptographic primitive. Let $S_0$ be the event $S$, and for
$i=1,\dots,n$, the construction defines an event $S_i$ in Game $i$, usually in a way
naturally related to the definition of $S$. The proof shows that $\Pr[S_i]$ is negligibly
close to $\Pr[S_{i+1}]$ for $i=0,\dots,n-1$, and that $\Pr[S_n]$ is equal (or negligibly
close) to the "target probability." From this, and the fact that $n$ is a constant, it
follows that $\Pr[S]$ is negligibly close to the "target probability," and security is
proved.

That is the general framework of such a proof. However, in constructing such proofs, it is
desirable that the changes between succesive games are very small, so that analyzing the
change is as simple as possible. From experience, it seems that **transitions between
successive games can be restricted to one of three types**:

*Transcription note.* "prodceeds" and "succesive" are transcribed as printed.

<a id="pdf-fde1f65e83ec-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.95 -->

**Transition type 1: transitions based on indistinguishability (p. 2).** In such a
transition, a small change is made that, if detected by the adversary, would imply an
efficient method of distinguishing between two distributions that are indistinguishable
(either statistically or computationally). For example, suppose $P_1$ and $P_2$ are assumed
to be computationally indistinguishable distributions. To prove that
$|\Pr[S_i]-\Pr[S_{i+1}]|$ is negligible, one argues that there exists a distinguishing
algorithm $D$ that "interpolates" between Game $i$ and Game $i+1$, so that when given an
element drawn from distribution $P_1$ as input, $D$ outputs $1$ with probability $\Pr[S_i]$,
and when given an element drawn from distribution $P_2$ as input, $D$ outputs $1$ with
probabilty $\Pr[S_{i+1}]$. The indistinguishability assumption then implies that
$|\Pr[S_i]-\Pr[S_{i+1}]|$ is negligible. Usually, the construction of $D$ is obvious,
provided the changes made in the transition are minimal. Typically, one designs the two
games so that they could easily be rewritten as a single "hybrid" game that takes an
auxilliary input — if the auxiallary input is drawn from $P_1$, you get Game $i$, and if
drawn from $P_2$, you get Game $i+1$. The distinguisher then simply runs this single hybrid
game with its input, and outputs $1$ if the appropriate event occurs.

*Transcription note.* "probabilty", "auxilliary" and "auxiallary" are transcribed as
printed.

<a id="pdf-fde1f65e83ec-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.95 -->

**Transition type 2: transitions based on failure events (pp. 2–3).** In such a transition,
one argues that Games $i$ and $i+1$ proceed identically unless a certain "failure event" $F$
occurs. To make this type of argument as cleanly as possible, it is best if the two games
are defined on the same underlying probability space — the only differences between the two
games are the rules for computing certain random variables. When done this way, saying that
the two games proceed identically unless $F$ occurs is equivalent to saying that

$$
S_i\wedge\neg F\iff S_{i+1}\wedge\neg F,
$$

that is, the events $S_i\wedge\neg F$ and $S_{i+1}\wedge\neg F$ are the same. If this is
true, then we can use the following fact, which is completely trivial, yet is so often used
in these types of proofs that it deserves a name:

<a id="pdf-fde1f65e83ec-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.95 -->

**Lemma 1 (Difference Lemma) (p. 3).** Let $A$, $B$, $F$ be events defined in some
probability distribution, and suppose that $A\wedge\neg F\iff B\wedge\neg F$. Then
$|\Pr[A]-\Pr[B]|\le\Pr[F]$.

*Proof.* This is a simple calculation. We have

$$
\begin{aligned}
|\Pr[A]-\Pr[B]|
&=\left|\Pr[A\wedge F]+\Pr[A\wedge\neg F]-\Pr[B\wedge F]-\Pr[B\wedge\neg F]\right|\\
&=\left|\Pr[A\wedge F]-\Pr[B\wedge F]\right|\\
&\le\Pr[F].
\end{aligned}
$$

The second equality follows from the assumption that $A\wedge\neg F\iff B\wedge\neg F$, and
so in particular, $\Pr[A\wedge\neg F]=\Pr[B\wedge\neg F]$. The final inequality follows from
the fact that both $\Pr[A\wedge F]$ and $\Pr[B\wedge F]$ are numbers between $0$ and
$\Pr[F]$. $\square$

So to prove that $\Pr[S_i]$ is negligibly close to $\Pr[S_{i+1}]$, it suffices to prove that
$\Pr[F]$ is negligible. Sometimes, this is done using a security assumption (i.e., when $F$
occurs, the adversary has found a collision in a hash function, or forged a MAC), while at
other times, it can be done using a purely information-theoretic argument.

Usually, the event $F$ is defined and analyzed in terms of the random variables of one of
the two adjacent games. The choice is arbitrary, but typically, one of the games will be
more suitable than the other in terms of allowing a clear proof.

In some particularly challenging circumstances, it may be difficult to analyze the event $F$
in either game. In fact, the analysis of $F$ may require its own sequence of games sprouting
off in a different direction, or the sequence of games for $F$ may coincide with the
sequence of games for $S$, so that $\Pr[F]$ finally gets pinned down in Game $j$ for
$j>i+1$. This technique is sometimes crucial in side-stepping potential circularities.

<a id="pdf-fde1f65e83ec-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.95 -->

**Transition type 3: bridging steps (p. 3).** The third type of transition introduces a
**bridging step**, which is typically a way of restating how certain quantities can be
computed in a completely equivalent way. The change is purely conceptual, and
$\Pr[S_i]=\Pr[S_{i+1}]$. The reason for doing this is to prepare the ground for a transition
of one of the above two types. While in principle, such a bridging step may seem
unnecessary, without it, the proof would be much harder to follow.

<a id="pdf-fde1f65e83ec-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.95 -->

**Section 1.1, one probability space, and the generalized Difference Lemma (p. 3).** As
mentioned above, in a transition based on a failure event, it is best if the two successive
games are understood to be defined on the same underlying probability space. This is an
important point, which we repeat here for emphasis — it seems that proofs are easiest to
understand if one does not need to compare "corresponding" events across distinct and (by
design) quite different probability spaces. Actually, it is good practice to simply have all
the games in the sequence defined on the same underlying probability space. However, the
Difference Lemma generalizes in the obvious way as follows: if $A$, $B$, $F_1$ and $F_2$ are
events such that $\Pr[A\wedge\neg F_1]=\Pr[B\wedge\neg F_2]$ and $\Pr[F_1]=\Pr[F_2]$, then
$|\Pr[A]-\Pr[B]|\le\Pr[F_1]$. With this generalized version, one may (if one wishes) analyze
transitions based on failure events when the underlying probability spaces are not the same.

<a id="pdf-fde1f65e83ec-p013-b001"></a>
<!-- pdf-source: page=13; block=1; confidence=0.90 -->

**Section 4.2, a worked bridging step (Game 2, p. 13).** [Context: §4.2, "Extending the
Input Length with a Universal Hash Function" (p. 12), stretches a pseudo-random family
$F=\{F_s\}_{s\in S}$ by a universal hash family $H=\{H_k\}_{k\in K}$. Game 1 gives the
adversary oracle access to a truly random function $f$.]

**Game 2.** [This transition is a bridging step.] We now make a purely conceptual change to
Game 1. Intuitively, one can think of a black box containing the random function $f$ as a
box with a little "gnome" inside: the gnome keeps a table of previous input/output pairs,
and if a query is made that matches one of the previous inputs, the corresponding output is
returned, and otherwise, an output value is chosen at random, and a new input/output pair is
added to the table (see Figure 1). Based on this, we get the following equivalent
formulation of Game 1:

$$
\begin{aligned}
&k\stackrel{\scriptscriptstyle ?}{\leftarrow}K,\quad Y_1,\dots,Y_q\stackrel{\scriptscriptstyle ?}{\leftarrow}\{0,1\}^{\ell_2}\\
&r\stackrel{\scriptscriptstyle ?}{\leftarrow}R\\
&\textbf{for } i\leftarrow 1\dots q \textbf{ do}\\
&\qquad w_i\leftarrow A(r,y_1,\dots,y_{i-1})\in\{0,1\}^{\ell}\\
&\qquad x_i\leftarrow H_k(w_i)\in\{0,1\}^{\ell_1}\\
&\qquad \textbf{if } x_i=x_j \textbf{ for some } j<i \textbf{ then } y_i\leftarrow y_j
  \textbf{ else } y_i\leftarrow Y_i\\
&b\leftarrow A(r,y_1,\dots,y_q)\in\{0,1\}\\
&\textbf{output } b
\end{aligned}
$$

Let $S_2$ be the event that $b=1$ in Game 2. Since the change in going from Game 1 to
Game 2 was purely conceptual, we clearly have

$$
\Pr[S_2]=\Pr[S_1].\tag{5}
$$

*Transcription note, partly illegible glyph.* The paper writes random assignment as a left
arrow with a small mark set above it. The `-layout` extraction renders that mark as the two
characters `c|`, and on the page image (read at 600 dpi) it is a cent-like sign (a "c" with
a vertical stroke); it is **not** legibly an "R", and the mark could not be identified with
confidence. It is written below as $\stackrel{\scriptscriptstyle ?}{\leftarrow}$, with `?`
standing for that unidentified mark. From the paper's own use of the same arrow in §4.1
(p. 11) — $\Pr[s\stackrel{\scriptscriptstyle ?}{\leftarrow}S:A^{F_s}()=1]$ — and from the
prose above ("an output value is chosen at random"), the arrow denotes a uniform random
choice from the set on its right. Figure 1 ("A gnome implementation of a random function",
p. 13) is a diagram and is not transcribed.

## ===== policy.md (records, at ab17e37feb00a677d69f6abd5ff7e427e3b9ef3c) =====

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

