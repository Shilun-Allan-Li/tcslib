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
