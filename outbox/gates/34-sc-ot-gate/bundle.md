## ===== briefs/pass-shelat-ch5-8/gates/34-sc-ot/pack.md =====

# Gate 34 · Oblivious transfer from trapdoor permutations (`sc-ot`, Protocol 160.4 and Proposition 161.5)

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews).

- **PR:** draft [PR #318](https://github.com/Shilun-Allan-Li/tcslib/pull/318) at
  `f62a25b3eda099c9cf9371900664752e7b89007d` (branch `land/pass-shelat-sc-ot`, tree
  `163be55abcd012eac6595af41807ce5cc57ef8f3`).
- **Target and base:** the PR targets `cryptography/pass-shelat-ch2-4` on base
  `a334ec2e1d87dbde7eac40812286ba60e85c9078` (the merge base: the records tip after #315 merged).
  - The fill was issued on `107f1e8c218733eac12d6b9bee6fece441271317`. The owned file's blob is the same at the issue
    base and at `a334ec2e` (`pack-checks/headers.txt`). Between them #307, #311, #312, #314 and #315 merged; the
    review's builds cover them (`build-r3`: the downstream of every module changed since `eff2dcd0`).
  - The records tip is now `1321b9cb358867f5b51974b8c5d0781519a9cfdb`. Since `a334ec2e` it has merged **#317**
    (prf-mac, `1d9b2ac3`) and **#316** (headD promotion, `1c09448c`). Their 8 Lean files are not in the PR, and the
    PR is **not** rebased onto them (below, *Pending merge condition*).
  - `pr.diff.txt` is `git diff origin/cryptography/pass-shelat-ch2-4...f62a25b3`, which equals `a334ec2e..f62a25b3`
    byte for byte (7 paths, 2256 insertions, 40 deletions).
  - **Open PRs and the tip.** `git merge-tree --write-tree` of the head with the tip, #313 (`94b31964`), #316
    (`c18afbe6`), #317 (`590d1a56`) and #319 (`6421ac16`, canonizer) is clean in each case, and no path is shared
    (`pack-checks/mergetrees.txt`). Every unit module is downstream of #316's `Foundations/BitLists` (now on the tip).
    **Pending merge condition** (not an audit item): #318 needs an integration rebuild on the merged tip before it
    merges, and whichever of #318 and #319 merges second needs one too; the maintainer runs these builds (question 7).
- **Commits:** 5, all authored and committed by Claude and SSH-signed (`pack-checks/rebase.txt`).
  - The Claude worker's 3 commits (job `sc-ot`), applied with `git am` with the delivered committer data. The three
    worker hashes `fc7d0366`, `a643e566`, `e2c6f1a8` reproduce only with the environment's signing on (review F-05).
    They were then rebased three times without conflict, author kept: `8d4290678ef1b27df17fd9dde7bc4518fd1dfc22`
    (checkpoint 1: `otProtocol_polyTime`), `53969e06170b57b8815e25194a07220e11869946` (checkpoint 2: Alice's side)
    and `b2e817cae4737dbcbeaf4171c9598b3e2b21fd57` (final: Bob's side). At `b2e817ca` the 7 files are
    byte-identical to the worker's `src/` (exchange `a8972fa0`; `pack-checks/rebase.txt`).
  - Landing edit **LE-doc** `7a1fa29bae093192e21344fb9110d8a087d0a123`: 50 formula docstrings, docstrings only.
  - Landing edit **LE-reuse** `f62a25b3eda099c9cf9371900664752e7b89007d` (the head): review finding F-01, proof
    only.
- **Scope:** a **proof audit**. The job proves the admitted `SecureComputation.otProtocol_polyTime` [PS10, Protocol
  160.4; Definition 155.1's efficiency requirement] and `SecureComputation.otProtocol_simulators` [PS10, Proposition
  161.5 with the explicit simulators `S_A`, `S_B`]. Both statements are frozen (prong B, ruling G3-8 applied in
  `587843c7`, Gate 06B PASS) and quoted in the brief. Their consumer `otProtocol_hbcSecure` (unchanged) now uses only
  the standard axioms.
- **Brief:** `fills/sc-ot/issued-r1/brief.md` on the records branch (SHA-256 `b4b5c73a…`). Three checkpoints
  (`otProtocol_polyTime`; Alice's side; Bob's side). The owned file plus the helper directory
  `SecureComputation/ObliviousTransfer/` only; every other file frozen. The binding duplication rule with an
  `## Overlap and reuse` section, and the expected adapted copy of `exists_pkPredictor`. Rule 10 with the
  projection-coercion ruling, and seals with `PolyExpr.eval` both excluded and sealed. The formula-docstring and
  sketch rules, the G26-N1 error count and the evidence-completeness rule.

## What changed

Paths are under `TCSlib/Cryptography/SecureComputation/`; `OT/` is `ObliviousTransfer/`. The PR touches 7 Lean files:
1 modified and 6 new (2256 insertions, 40 deletions). Line counts are base → worker head `b2e817ca` → LE-doc
`7a1fa29b` → PR head.

| File | Status | Lines |
|---|---|---:|
| `ObliviousTransfer.lean` | owned, modified | 671 → 747 → 748 → 748 |
| `OT/Shape.lean` | helper, new | 206 → 216 → 216 |
| `OT/Efficiency.lean` | helper, new | 526 → 545 → 545 |
| `OT/Simulators.lean` | helper, new | 431 → 435 → 435 |
| `OT/ViewA.lean` | helper, new | 186 → 186 → 186 |
| `OT/Predictor.lean` | helper, new | 206 → 212 → 212 |
| `OT/ViewB.lean` | helper, new | 534 → 545 → 545 |

The owned file imports the six helpers directly, so after #305 no facade edit is needed, and none was made.

**The design.** The helpers cannot import the owned file (it imports them). So they state every result for every
protocol and every pair of machines of the *shapes* of Protocol 160.4 and of `S_A`, `S_B`. The shapes are the
predicates `OT.IsOT`, `OT.IsSimA` and `OT.IsSimB`, which restate the owned definitions' bodies (review F-06, by design).
The owned file proves that `otProtocol`, `otSimA` and `otSimB` have these shapes, from its own published readers
(`otProtocol_isOT`, `otSimA_isSimA`, `otSimB_isSimB`). Then:

```lean
theorem otProtocol_polyTime : otFunctionality.PolyTime (otProtocol T H) :=
  OT.polyTime_of_isOT T hH (otProtocol_isOT T H)

theorem otProtocol_simulators (hT : T.OneWay) (hEHC : EnhancedHardCore T h) : … :=
  OT.simulators_of_isOT T H hH henc (otProtocol_isOT T H) (otProtocol_outV T H henc)
    (otProtocol_outP T H) (otSimA_isSimA T) (otSimB_isSimB T hH) hT
    ((enhancedHardCore_iff T h).1 hEHC)
```

The proof follows [PS10, Protocol 160.4, Proposition 161.5] and the frozen sketches. The targets' step lists were
rewritten to describe the delivered proof; the statement prose is unchanged. See REPORT § 2 and the review's
*Content* line.
1. **Shape** (`Shape`). `OT.IsOT T H π`: the next-message functions are `OT.senderNext` and `OT.receiverNext`. Alice
   uses `Gen`'s coins and Bob two sampler blocks. There are five messages, Alice first. `OT.exec_five` gives the five
   moves, and `OT.transcriptWith_isOT` the transcript `([y, []], [i, z, []])` with its two empty fillers.
2. **`otProtocol_polyTime`** (`Efficiency`; checkpoint 1). The raw functions `OT.senderRaw` and `OT.receiverRaw` read
   the case off the encoded history by emptiness tests. `NUPPT.ofPolyTimeUniform` of them computes the next-message
   functions (`senderRaw_advInput`, `receiverRaw_advInput`). The messages are bounded by
   `B = Q₁ + (3(Q₂ + Q₃) + 2) + 5` (`OT.exists_messages_le`): the index by `Gen`'s `runLenPoly` `Q₁`, the pair by two
   sampler outputs (`Q₂`) or evaluations (`Q₃`), and one bit per mask.
3. **Alice's side** (`Simulators`, `ViewA`; checkpoint 2). On the coins `(r, s₁, s₂)` (`OT.realCoins`,
   `OT.simACoins`), the real view carries `⟨f_i(w₁), w₂⟩` (swapped when `b`), and `S_A`'s carries `⟨w₁, w₂⟩`.
   `OT.statClose_eval_sample` shows that at every generated index `eval ⟨i, Sample⟩` is `2δ(n)`-close to `Sample`
   under `SampleClose δ`. `OT.statClose_prod_of_forall` lifts this to the joint samplers.
   `OT.distAdv_realA_idealA_le`: Alice's side is at most **`2δ(n)` at every `n`**, for every distinguisher and all
   inputs.
4. **Bob's side** (`Predictor`, `ViewB`; final). `OT.bobView` is Bob's view with the unselected mask
   `[β ⊕ a_{1−b}]`. The real view has `β = B s₂`, the enhanced bit `OT.hcBit = h_i(perm_i⁻¹(dec_i(Sample(i; s₂))))`;
   the ideal view has a fresh coin. So the advantage is `|U₊ − U₋| / 2` with `U± = E_r accB r (±B)`
   (`acceptProb_realB`, `acceptProb_idealB`, `uprob_xor_shear`).
   - The machine `OT.viewDist D b a₀ a₁` (`NUPPT.ofPolyTime` of `OT.viewDistRaw`, with `D`'s advice) reads
     `⟨i, ⟨s', [β]⟩⟩`. It builds Bob's view around the challenge, with Bob's tape containing `s'`, and runs `D`.
   - The published **`tdpPredictor (viewDist …) fl`** of Algorithm 104.3 is the predictor. Through `uprob_tdpPredictor`
     and the **signed-predictor identity** `OT.uprob_signedPredictor_false/_true`, it predicts `B` from `⟨i, s'⟩` with
     probability `1/2 ± (U₊ − U₋)/2` (`uprob_predictor_false/_true`).
   - **`hEHC` is applied to 16 machines**: 8 triples `t = (b, a₀, a₁)` × 2 signs `fl`.
     `ε_B(n) = Σ_t Σ_fl |ε_{t,fl}(n)|` is negligible (`OT.negligible_finset_sum`). For the inputs' bits `t`,
     `distAdv_realB_idealB_le` bounds the advantage by `|ε_{t,0}(n)| + |ε_{t,1}(n)| ≤ ε_B(n)`
     (`OT.exists_negligible_bob`).
5. **Together** (`OT.simulators_of_isOT`): `ε(n) = 2|δ(n)| + ε_B(n)`, with `δ` from `T.OneWay`'s `sampleClose`.
   `EnhancedHardCore` enters only through `enhancedHardCore_iff` (unchanged).

**Route differences from the frozen sketch** (statements unchanged; REPORT § 2.4). The predictor is the published
`tdpPredictor` around an `ofPolyTime` machine, not a new `NUPPT.exists_comp` composite. Each triple is hard-wired in
its own machine and the sixteen bounds are summed, instead of the worst triple as advice; `D`'s advice is kept.

The brief's edge cases: `b = 0, 1` (the branches of `realA_realCoins`, `realB_realCoins`, `idealB_simBCoins`, and the
block swap); all eight `(b, a₀, a₁)` (sixteen machines); the five-message layout and its two empty fillers
(`exec_five`, `transcriptWith_isOT`); non-canonical strings (`apply_of_decD` in `mask_eval`, canonical decoding in
`statClose_eval_sample` and `mask_raw`); the inverter's fixed all-`true` tape (`inv_runAtL_ones`, `OT.maskRaw`);
small `n` (`SampleClose δ` holds at every `n`, so Alice's bound has no threshold); the distinguisher's advice (kept by
`viewDist` and `tdpPredictor`).

**Statements.** decls2 from the issue base to the head gives **141 ADDED, 0 CHANGED, 0 REMOVED** (review
`statements/head-le/decls2-vs-base.tsv`; `decls2-vs-worker.tsv`, empty).
- The frozen check (`frozencheck.py`, at the LE head) compares the owned file's 52 base declarations: kind, name,
  order, header bytes, statement prose and every definition body, `EnhancedHardCore` included (G3-8). It finds **0
  differences** (52 → 55 declarations; `landing/frozen-check.txt`). Each of its 5 one-character controls reports
  exactly one difference (`statements/frozen/control-*`).
- `touched`: 2 CHANGED (the two targets: proofs and sketches only), 50 UNCHANGED, 3 ADDED in the owned file, 138 in the
  new files.
- Re-checked for this pack from git objects with `maintainer/tools/decls2.py`'s parser: 141 ADDED and 52 unchanged
  against both the issue base and `a334ec2e`; 0 rows for `b2e817ca..7a1fa29b` (LE-doc) and for `7a1fa29b..f62a25b3`
  (LE-reuse). The owned file's 52 base headers are byte-identical at the head, in order, with only the two targets'
  docstrings changed. `EnhancedHardCore`'s block and docstring are byte-identical (`pack-checks/headers.txt`).

## Rulings and records in force

1. **DL-48 (Seyoon, 2026-11-15): "ledger debt, disclosed."** It covers three items, deferred to the cleanup:
   - **F-02**: `OT.splitLen` / `splitLen_symm_ofFn` (`OT/Simulators.lean`) restate the public `coinsEquiv`, read
     backwards, and `ofFn_coinsEquiv` (`Asymptotic/EnsemblesLemmas.lean:141,145`). The body is also the private ElGamal
     `dlc_splitEquiv`. Reuse needs a new import and a definition change, so it is not landing-fixable. Cleanup:
     `(coinsEquiv h).symm`.
   - **F-04**: `OT.uprob_signedPredictor_false/_true` adapt `exists_pkPredictor`, because `pkPredictor` has no public
     reader. This is the disclosed, expected copy; a promotion with `pkPredictor_apply` is deferred.
   - **F-07**: undisclosed near-relatives, `GI.pairSndD_encodeMsgs` (for `getD_one_eq`) and `predict_eq`, and the
     promotion requests `negligible_finset_sum`, `statClose_prod_of_forall`, `exec_five` and `length_runAtL_le`.

   **Not a finding:** any item DL-48 lists.
2. **F-01 is fixed by LE-reuse.** `OT.pairSndD_nil'` (`pairSndD [] = []`) restated the public
   `BinArith.iterate_pairSndD_nil` at `1` (`Complexity/ClassP/BinaryArith/Words.lean:158`, already in `Efficiency`'s
   closure). It was not disclosed.
3. **Rule 10: a `CoeFun`/`Coe` instance whose body is a structure projection is notation (Seyoon, 2026-11-14).** This is
   `FinDist`'s `⟨FinDist.prob⟩`, the only projection coercion in this closure. The coe-variant seals are canonical; the
   strict variant is run and its differences attributed. **For this unit the seals agree in every row, strict and coe.**
   The strict *controls* differ only in `ctlCoeReader` (F-09, attributed).
4. **`PolyExpr.eval` is notation (Q1, the user, 2026-11-07).** Seal **A**, which exempts it, is **canonical**; seal B
   is run and reported because the brief asks for both. So **coe-A is the canonical variant**.
5. **The facade-completeness lint fix, #305 (Seyoon's ruling of 2026-11-14).** The baseline is **92 FAIL / 101 WARN**
   (Cryptography) and 25 / 391 (Complexity). At the final head both have line sets identical to the tip `a334ec2e`
   (review `lint/linediff-r3.txt`, empty).
6. **LE-doc (the maintainer's landing edit): docstrings only.** It adds formulas, in Lean argument order, to the 50 new
   public declarations the review's docaudit flagged NO-FORMULA: 3 in the owned file, 18 `Efficiency`, 6 `Predictor`,
   4 `Shape`, 11 `Simulators`, 1 `ViewA` and 7 `ViewB`. The frozen target `otProtocol_polyTime` keeps its base prose.
   Re-checked for this pack from git objects: `b2e817ca..7a1fa29b` touches the 7 files, each identical with doc
   comments deleted, with 50 docstrings changed and every line within 100 characters (`pack-checks/lecheck.txt`).
7. **LE-reuse (the maintainer's landing edit): proof only** (review finding F-01). `pairSndD_nil'`'s proof
   `List.eq_nil_of_length_eq_zero (Nat.le_zero.1 (length_pairSndD_le []))` becomes `BinArith.iterate_pairSndD_nil 1`.
   Its docstring's provenance parenthesis now names the public lemma. It is +2/−2, one file, no import. The statement is
   unchanged (`statements/head-le/decls2-vs-worker.tsv`, empty), and a trial build passed before the commit
   (`lereuse-trial/`: `Efficiency` rc 0, 0 warnings). Re-checked for this pack: `7a1fa29b..f62a25b3` touches
   `Efficiency.lean` only, in 2 hunks, with its 38 headers identical, only `pairSndD_nil'`'s docstring changed, and
   the imports identical (`pack-checks/lecheck.txt`).
8. **The landing edits are the maintainer's** (the ext-nosrc, cca2-ett, dl-crh, hash-sign, lamport, learning and
   prf-mac precedents).
9. **G3-8 is closed.** The enhanced hard-core predicate was ruled (A) on 2026-11-05 and applied in prong B.
   `EnhancedHardCore` is a frozen definition and a hypothesis of the target. Whether any collection has such a
   predicate limits the use of the result, not its proof (module docstring).

## What is frozen

- **The two targets' statements** (quoted in the brief), the 50 other pre-existing declarations of
  `ObliviousTransfer.lean` and their statement prose, in particular `EnhancedHardCore` and `enhancedHardCore_iff`, the
  protocol and simulator definitions with their readers, `otProtocol_outV/_outP` and `otProtocol_hbcSecure`. Also the
  global simp attributes.
- **Every file outside** `SecureComputation/ObliviousTransfer.lean` and `SecureComputation/ObliviousTransfer/`. That
  includes `SecureComputation/Defs.lean` (the functionality and `realA/B`, `idealA/B`), `Encryption/PublicKey/
  Trapdoor.lean` and `TrapdoorPredictor.lean` (`exists_pkPredictor`, `tdpPredictor`), `Asymptotic/Collections*.lean`
  and `Games/Efficiency.lean`.
- **The landing edits:** LE-doc 50 docstrings; LE-reuse one proof and one docstring parenthesis.

## Questions for the audit

**1. Correctness against [PS10, Protocol 160.4 and Proposition 161.5]**
- **`otProtocol_polyTime`:** do `OT.senderRaw` and `OT.receiverRaw` compute the parties' next-message functions on
  every history (cases `[]`, one, two, three or more messages; `senderRaw_advInput`, `receiverRaw_advInput`)? Are
  they polynomial-time with the stated coins? Is the message bound `B = Q₁ + (3(Q₂ + Q₃) + 2) + 5` correct for the
  five-message layout, including the two empty fillers and one-bit masks?
- **Alice's side:** is `OT.distAdv_realA_idealA_le` (≤ `2δ(n)` at every `n`) right?
  - Are `OT.realA_realCoins` and `OT.idealA_simACoins` the real and ideal samplers on `(r, s₁, s₂)`, for both `b`?
  - Is `OT.statClose_eval_sample` right: `δ` to the uniform element mapped by `encD ∘ perm`, `0` from `perm`, `δ`
    back by canonical decoding (`SamplerCanonical`)?
  - Is the dependent product `OT.statClose_prod_of_forall` (closeness for every value of a shared coordinate) sound?
  - Is the use of `acceptProb_comp_equiv` along the coin equivalences sound?
- **Bob's side:** is the route through `tdpPredictor`/`viewDist` with the signed identity right?
  - Is `OT.hcBit` exactly the bit `EnhancedHardCore` (through `enhancedHardCore_iff`) asks the predictor to guess,
    with the challenge `⟨i, s'⟩` and `s'` the sampler coins?
  - Does `viewDist` rebuild Bob's real view around the challenge, with Bob's tape `s₁ ++ s'` and `D`'s advice and
    coins kept (`distinguisherL_viewDist`)?
  - Is the signed-predictor identity `OT.uprob_signedPredictor_false/_true` (`1/2 ± (U₊ − U₋)/2` for uniform coin
    challenges) correct, and are `acceptProb_realB` (`E_r accB r B`) and `acceptProb_idealB`
    (`E_r (accB r B + accB r ¬B)/2`) right, with the masks read by `mask_eval` and `mask_raw` through
    `inv_runAtL_ones`, `inv_eq_encD`, `henc` and `apply_of_decD`?
  - Are the **16 `hEHC` instances** (8 triples × 2 signs) and their **sum** `ε_B` a negligible bound uniform over
    all inputs (`exists_negligible_bob`, `negligible_finset_sum`)?
- Does `OT.simulators_of_isOT` give the frozen statement with `ε(n) = 2|δ(n)| + ε_B(n)` for every `D`?
- Do `otProtocol_isOT`, `otSimA_isSimA` and `otSimB_isSimB` prove the shapes from the owned file's published
  readers only, and are the restated bodies (`OT.mask`, `senderNext`, `receiverNext`, `simAView`, `simBView`, …)
  exactly the owned definitions?
- Are the brief's edge cases covered (listed above)? Do the rewritten target sketches describe the delivered proof?

**2. Frozen-statement integrity**
- Are the two targets' headers and the other 50 pre-existing declarations byte-identical, with
  **`EnhancedHardCore` unchanged** (G3-8)? See `landing/frozen-check.txt`, `statements/frozen/` and
  `pack-checks/headers.txt`.
- In the owned file, did only the targets' bodies and sketches, the imports, the title ("(statement phase)" dropped),
  the `## Main results` lines and the new `## Contents` change?
- Is decls2 **141 ADDED / 0 CHANGED / 0 REMOVED**, is frozencheck **0** with 5 biting controls, and is every new
  declaration in the owned file or the permitted helper directory?

**3. Duplication (recent gates graded undisclosed re-proofs of public lemmas as majors)**
- Does any new declaration, or any part of a proof, duplicate a public TCSlib or Mathlib lemma, or copy a private one,
  beyond the worker's `## Overlap and reuse` table and **DL-48** (ruling 1)? F-01 is fixed by LE-reuse; F-02 and F-04
  are ruled debt (DL-48), and F-07's items are DL-48 notes.
- **Any further undisclosed duplicate of a public lemma is a major.** The recent majors of this class are G23-01,
  G24-01 (`inputWord_take` re-proving `take_ofFn_castLE`), prf-mac F-01, learning (`uprob_eq_point`), G29-01
  (`hj` = `OneWay.uexp_const`), G29-02 (`firstBit_of_pos` re-proving `LamportFill.headD_drop_ofFn`) and sc-ot F-01
  itself.
- Search in particular:
  - probability and closeness identities (`uprob_*`, `uexp_*`, `acceptProb_*`, `StatClose.*`, `statClose_*`,
    `distAdv_*`);
  - negligible-function closure (`Negligible.*`, finite sums);
  - coin equivalences and their `ofFn` readers (`splitCoins`, `coinsEquiv`, `owfCoinsEquiv`, `coinsEquivPoly`,
    `Fin.appendEquiv`);
  - history and list readings (`pairFstD`/`pairSndD`, `encodeMsgs`, `getD`/`headD`, `iterate_pairSndD_*`, now also
    the tip's `TCSlib.Cryptography.headD_drop_ofFn` from #316);
  - execution unfoldings (`exec_succ`, `exec_*`);
  - trapdoor readings (`inv_eq_encD`, `apply_of_decD`, `tdpPredictor`, `predProb_*Predictor_*`);
  - machine lengths (`runLenPoly`, `length_runAt*`).
- Are the disclosed relations accurate and their "why not reused" reasons valid? See in particular `hcBit` vs the
  private `tdpSampled`, `mask_eval`/`mask_raw` vs the private `tdpBitScheme_pkEncDist`, `getD_zero_eq`/`getD_one_eq'`,
  and the GI/3-col machine pattern of the raw functions. The review's independent search is
  `evidence/logs/duplication-review.txt`; the worker's are `worker/evidence/logs/{checkpoint1,final}-searches.log`.

**4. Rule 10**
- Do the seals, collected from the elaborated terms plus matchers, cover every touched declaration of the 7 files over
  the full closure, at the base and the head, in all four variants? See review `logs/seal-table-seals{,-coe}.txt` and
  `logs/seal-head-*.tsv`. Requests per file (coe A): owned 1721, `Shape` 1105, `Efficiency` 1109, `Simulators` 1109,
  `ViewA` 1124, `Predictor` 1706, `ViewB` 1711; strict = coe + 1, the instance (`logs/mkseals-*.log`).
- With **coe-A canonical** (rulings 3 and 4), does every file pass? The review has head A 7/7 and B 7/7 in both
  variants, base 1/1, and 0 new failing declarations; strict = coe.
- Do the paired controls bite? The coe records (canonical) have 20 probes and 61 sealed negatives, `logs/ctlcheck.log`
  ALL_OK. The rows are `PolyExpr.eval` (B), the `FinDist` CoeFun instance, `NUPPT.layout`, `Strategy.encodeMsgs`,
  `otFunctionality`, `OT.mask`, `OT.simSeg`, `OT.inA2`, `OT.bobView` and `OT.hcBit`.
  - The strict records have 20 probes and 71 sealed negatives. Every negative fails exactly once, but `ctlCoeReader`
    fails in the 10 strict sealed probes, a harness effect: the statement elaborates to `CoeFun.coe` (F-09,
    `logs/controls-strict-attribution.txt`). Is that attribution right?
  - F-09 also notes that the strict negative `ctlCoe` *does* fail once, against the worker's claim. Is that right?
- Explicit-unfold scan at r1 (`fb6075d8`; the unit's 128-module closure is byte-identical at the head,
  `pack-checks/rebase.txt`): 742 items, 645 theorems, 21 owned definitions, 76 local or unresolved, **0 foreign**
  (`logs/scan2-head.log`, `logs/scan-owned-and-local.txt`). The owned items are the base file's 18 pre-existing proofs
  and 3 in-file helper definitions (`viewDist`, `simACoins`, `simBCoins`).
  - Does any proof read a foreign definition other than through a published reader? Candidates: the
    `SecureComputation/Defs` functionality, `realA/B`, `idealA/B`, `distAdv`; `NUPPT.layout`, `advInput`,
    `ofPolyTime*`; `Strategy.encodeMsgs`, `exec`; `tdpPredictor`, `TrapdoorCollection.*`; `FinDist` internals; the
    owned file's definitions read from a helper; one helper's definitions read from another.

**5. The landing edits**
- **LE-doc (ruling 6):** does each of the 50 new formulas state what its declaration says, with arguments in the Lean
  order (review `landing/le-doc.diff`, `landing/le-doc-doconly.txt`)? Is it docstrings only?
- **LE-reuse (ruling 7):** is it proof only, plus the docstring parenthesis? Is `BinArith.iterate_pairSndD_nil 1` a
  correct instance (`pairSndD^[1] [] = []` is `pairSndD [] = []` by `Function.iterate_one`, definitionally)? See
  `landing/le-reuse.diff`.
- Were the seals, controls and scan, run at r1 `fb6075d8`, rightly carried to the head? `pack-checks/rebase.txt`: the
  range-diff `0e5e725d..fb6075d8` → `a334ec2e..f62a25b3` is 5/5 `=`, and all 128 modules of the unit's closure are
  byte-identical at `fb6075d8` and `f62a25b3`.

**6. The docstring and sketch rules**
- Does every new public declaration's docstring state its formula, with arguments in the Lean order and a `[PS10, …]`
  tag where it comes from the source? The review's docaudit after LE-doc (`statements/head-le/docaudit.tsv`) has
  110 OK, 25 LABEL (all state the equation) and 8 NO-FORMULA. The 8 are the frozen `otProtocol_polyTime`'s base prose
  and 7 docstrings stating a Prop formula without a relation symbol, such as `OT.IsOT T H (otProtocol T H)` and
  `PolyTimeComputable (genRaw T)`, which the tool does not accept. Are those 7 acceptable?
- Does every proof of 15 lines or more carry a `**Proof sketch.**`, and do the long proofs (`exists_negligible_bob`,
  `distAdv_realA_idealA_le`, the raw-machine efficiency proofs) have step comments? `statements/head-le/sketchaudit.txt`
  has 13 theorems and 1 flagged: `OT.receiverNext_eq`, a `:= rfl` under a 19-line statement, a tool artifact. A
  misstated formula or sketch is a minor.
- Does every new public `def` land with its readers (`_eq`, `_iff`, `_apply`, or for the coin equivalences `_ofFn`
  readers; lint check 8)? Is nothing new `@[simp]`, an instance, reducible or an abbreviation? The census has none
  (`logs/census-summary.txt`).

**7. The merge interaction**
- `git merge-tree --write-tree f62a25b3 <x>` is clean (`pack-checks/mergetrees.txt`). No path is shared with any of
  them, and the changed path sets of #318, #319 and (tip delta ∪ #313) are pairwise disjoint.

  | `<x>` | head | merged tree |
  |---|---|---|
  | the tip | `1321b9cb` | `fe5b9a3c` |
  | #313 | `94b31964` | `8baffe99` |
  | #316 (merged) | `c18afbe6` | `3c18fffc` |
  | #317 (merged) | `590d1a56` | `16633b31` |
  | #319 | `6421ac16` | `e59d63a7` |
- **Downstream** (`pack-checks/downstream.txt`):
  - **The tip.** Every unit module has #316's `Foundations/BitLists` in its closure. In the merged tree, 10 modules
    are downstream of both: the 7 unit modules, `SecureComputation`, `YaoReal` and root `TCSlib`. #317's files are
    not in the unit's closure.
  - **#313 and #319.** Neither changes a module in the unit's closure; root `TCSlib` is the only module downstream of
    both.
  - **The build.** Of the review's 139 built modules (`build-r3`, at this head), 137 have the tip-merged source. The
    other two are #317's `MAC/FromPRF` and #316's `Lamport/MachineSpec`. `BitLists` itself was not rebuilt, since it
    is unchanged from `a334ec2e` to this head. All 139 have #319's merged source, and 138 have #313's
    (`pack-checks/srcequality.txt`).
- **No name interaction:** none of the 141 new names is declared in a file the tip, #313, #316, #317 or #319 changed
  (`pack-checks/namecheck.txt`). The review's own open-PR check (`logs/open-pr-overlap.txt`) predates #316 and #317;
  this pack's check covers them.
- **Pending merge condition (not an audit item).** The combined trees are **not** built.
  - Because #316 and #317 merged after this branch's base, #318 needs an integration rebuild on the merged tip before
    it merges: the downstream of `BitLists`, `MachineSpec` and `MAC/FromPRF`, which contains every unit module.
  - Whichever of #318 and #319 merges second needs the same.
  - The maintainer runs those builds. Treat them as conditions on the merge, not as something for this audit to
    establish. What you can raise: a concrete reason a merged tree cannot build, or a name or instance interaction.

## Known dispositions (not findings)

- **F-03** (info): the 50 missing formulas, fixed by LE-doc. **F-05** (info): `COMMITS.tsv` hashes reproduce only
  with the environment's deterministic SSH signing (`logs/git-am-integrity*.log`), as prf-long F-03. **F-06** (info,
  disclosed): the helpers restate the owned file's definition bodies by design. **F-08** (info): the worker removed
  another fill's worktree on its own host, an environment matter on the worker's host. **F-09** (info): the strict
  `ctlCoeReader` harness effect, attributed.
- **Finding numbers in the evidence log.** The review's `logs/duplication-review.txt` numbers `pairSndD_nil'` as F-02
  and `splitLen` as F-03. The review's findings table (`review.md`) and DL-48 number them **F-01** and **F-02**; the
  table governs.
- **The probes ran at r1.** The seals, controls, scan and census probes ran at `fb6075d8` (on `0e5e725d`). The builds
  `build-r2` (on #314) and `build-r3` (on #315, at this head) and the whole-tree check (1250 modules, RESULT OK) came
  after. The unit's closure is unchanged throughout (question 5).
- **Admissions:** the issued 31 in 14 modules become 29; only `SecureComputation/ObliviousTransfer` changes (2 → 0;
  `logs/sorry-census-r3.txt`). The build's 12 sorry warnings are all in admitted base or base-delta modules.
- **`yaoProtocol_hbcSecure` keeps `sorryAx`** through Yao's admitted hybrid; base, not this unit.
- **Old (pre-#305) lint** shows 6 more lines of the facade class #305 fixed (`lint/oldlint-linediff.txt`); recorded,
  not a finding.
- **The worker's promotion and reader requests** are recorded for the deferred cleanup (DL-48). These are
  `uprob_signedPredictor_*` with `pkPredictor_apply`, `negligible_finset_sum`, `statClose_prod_of_forall`, `exec_five`,
  `length_runAtL_le`, and the readers `owpPair_apply`, `owpGen_apply` and `owpGenNot_apply`.

## Also check

**Axioms**
- At the head, `otProtocol_polyTime`, `otProtocol_simulators` and the consumer `otProtocol_hbcSecure` each print
  `[propext, Classical.choice, Quot.sound]`, and so do the helper endpoints. `pairSndD_nil'` uses no axioms
  (`landing/census-head.log`, `CensusHead.lean`). At the base the targets had `sorryAx`.
- The census has 234 stored constants in the 7 files (owned 70, `Shape` 15, `Efficiency` 49, `Simulators` 55, `ViewA`
  7, `Predictor` 15, `ViewB` 23, the worker's counts). The axiom union is the standard three, with no `sorryAx`. Against
  the base: 66 → 234, 0 removed, 0 type- or attribute-changed, 3 axiom-changed (the two targets and
  `otProtocol_hbcSecure`, `sorryAx` dropped; `logs/census-base-vs-head.tsv`).

**Sizes and widths:** every file has at most 748 lines and every line at most 100 characters (`source-head.json`;
review `statements/head-le/sizes-widths.txt`).

**Build:** at the head `f62a25b3`, the 139 modules have rc 0 and 0 errors in both diagnostic forms (G26-N1; substring
"error" 0). The modules are the downstream of every module changed since `eff2dcd0`, through root `TCSlib` and
`audits/pass-shelat/Checks` (`landing/root-checks.jsonl`, whose last line is the runner's `done` record;
`landing/build-summary.txt`). The unit modules have 0 warnings. The whole-tree check is at the head, 1250 modules,
RESULT OK (`landing/tree-check-head.txt`). The olean tree was restored to the base snapshot afterwards
(`restore/r3/snapshot-post.txt` = `tree/snapshot-pre.txt`, `457ba704…`). Every built module's `source_sha256` equals
the blob at `f62a25b3` (`pack-checks/srcequality.txt`).

## Evidence

- **`review.md`:** the maintainer's delivery review, verdict ACCEPT WITH LANDING EDITS (F-01–F-09).
- **`verification.zip`** (113 entries): every file the review cites and the pack uses, as byte-identical
  originals. Its `SHA256SUMS` lists every other entry, and `PROVENANCE.txt` gives each entry's source. It holds:
  - `review-evidence.zip` (`fills/sc-ot/final-r1/`, SHA-256 `aa3bcfc3…`) and `review-evidence-SHA256SUMS`, its
    manifest: 811 entries, all files, under `sc-ot-r1/` exactly the 810 manifest paths plus that folder's
    `SHA256SUMS` (byte-identical to the manifest); every hash verifies. It covers integrity, the landing and both
    landing edits, the three rebases, the builds (r1, LE, r2, r3) and the whole-tree checks with the restore, decls2,
    the frozen check with its controls, `touched`, the docstring and sketch audits, the census and axioms, the strict
    and coe seals at the base and the head, the paired controls, the scan, the lint, sizes and the duplication review;
  - `landing/` (13): the review's extracts (`final-r1/landing/`), each a byte copy of a ZIP entry: `PROVENANCE.txt`,
    the commits, the series log, the LE-doc and LE-reuse diffs and messages, the doc-only check, the rebase logs and
    the origin delta;
  - `records/` (14): the issue package `fills/sc-ot/issued-r1/`, the duplication ledger (DL-48), the decision log,
    the #305 record (README and patch) and the secure-computation plan (§ 2.1–2.2), at records
    `1321b9cb358867f5b51974b8c5d0781519a9cfdb`;
  - `evidence/` (54): byte copies of the ZIP entries this pack cites;
  - `worker/` (11): byte copies from exchange `a8972fa063a58ad2ffbfd221d625653d34a53ee8` (`inbox/fills/sc-ot/`):
    `patches/COMMITS.tsv`, the final axioms, both searches, the census and lint diffs, the repro, width and control
    logs, `seals-compare.log` and `scan-compare.log`;
  - `pack-checks/` (17): the re-checks for this pack, from git objects only (no Lean), with their scripts.
- **The worker's own evidence:** on the exchange at `a8972fa063a58ad2ffbfd221d625653d34a53ee8`, under
  `inbox/fills/sc-ot/`. Its top `SHA256SUMS` lists 219 files and `evidence/SHA256SUMS` 206, all delivered.
- **`landing/`:** byte copies of evidence-ZIP entries.
  - `root-checks.jsonl` (= `build-r3/results.jsonl`): the 139 modules, rc 0.
  - `build-summary.txt` (= `build-r3/summary.txt`).
  - `census-head.log` (= `probe-runs/CensusHead.log`): the axiom prints and the census rows at the head.
  - `frozen-check.txt` (= `statements/head-le/frozen-check.txt`): the frozen check at the LE head.
  - `tree-check-head.txt` (= `tree/r3/tree-check-head.txt`): the whole-tree check at the head.
- **`worker-report.md`:** the worker's `REPORT.md`, at exchange `a8972fa0`.
- **`pr-description.md`:** the PR #318 description as fetched from the GitHub REST API on 2026-11-15 (`.body`, raw).
- **`pr.diff.txt`:** `git diff` from the base to the head (7 paths, 2256 insertions, 40 deletions).
- **`source-head.json`:** the head hashes, line counts and over-width counts of the 7 changed files.
- **`sources.zip`:** the source closure at the head of every changed module, 128 files.
- **The bundle** adds, as context at the head:
  - `SecureComputation/Defs.lean` (the functionality, `realA/B`, `idealA/B`, `PolyTime`);
  - `Encryption/PublicKey/TrapdoorPredictor.lean` (`tdpPredictor`, `uprob_tdpPredictor`, `uexp_half_add/_sub`);
  - `Encryption/PublicKey/Trapdoor.lean` (`exists_pkPredictor` and the private `predProb_pkPredictor_eq`).

## Findings delivery

Return `gate34-sc-ot-findings.md` as a Markdown file in this chat. If you have several evidence files, return a ZIP.
The user dispatches and merges.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

**Severities**
- **blocker:** a false or unusable statement, a proof that does not establish the frozen statement, or a scope
  violation.
- **major:** a changed frozen statement, a forbidden read in a touched declaration not covered by the rulings, an
  undisclosed copied private lemma or undisclosed re-proof of a public one outside DL-48, or necessary evidence that
  cannot be verified.
- **minor:** documentation or API defects, including an inaccurate formula docstring or proof sketch.
- **note:** anything else.

Report the audited head and the counts by severity. The gate closes at zero blockers and zero majors.

## ===== briefs/pass-shelat-ch5-8/gates/34-sc-ot/review.md =====

# sc-ot · maintainer delivery review (r1)

**Verdict: ACCEPT WITH LANDING EDITS.** The edits are LE-doc, which adds 50 formula docstrings, and LE-reuse, which reproves one lemma from a public one. Draft [PR #318](https://github.com/Shilun-Allan-Li/tcslib/pull/318).

## Delivery and landing branch
- **Delivery.** A Claude worker proved `otProtocol_polyTime` and `otProtocol_simulators`, [PS10, Protocol 160.4, Proposition 161.5]. The final is at exchange `a8972fa063a58ad2ffbfd221d625653d34a53ee8`, and the issue base is `107f1e8c`.
- **Landing.** `land/pass-shelat-sc-ot`, head `f62a25b3eda099c9cf9371900664752e7b89007d`, tree `163be55a`. It was rebased r1 → r2 (#314) → r3 (#315) onto `a334ec2e`; every range-diff is identical.
  - **Commits.** The worker's are `8d429067`, `53969e06` and `b2e817ca`. LE-doc is `7a1fa29b` and LE-reuse is `f62a25b3`. All are signed.
- **Files.** 7 files, +2256/−40: the owned `ObliviousTransfer.lean` and six new helpers in `ObliviousTransfer/`.
- **Evidence.** `review-evidence.zip`, SHA-256 `aa3bcfc3dfa3d434904a80885c7f70b4093981abff2592ed5d1e85e34a3d2e4f`: 811 entries, the 810 manifest paths plus `SHA256SUMS`.

## Checks
- **Integrity.** The manifests verify 219/219 and 206/206. The package verifies 7/7 and its sources 159/159. `git am` reproduces the three worker hashes, but only with signing on (F-05). `src/` equals the 7 changed files.
- **Build.** The final r3 build covers 139 modules: rc 0, and 0 errors in both the `error:` and `error(` forms. The unit modules have 0 warnings. The whole-tree check covers 1250 modules: OK.
- **Statements.**
  - The frozen check finds 0 differences in headers, prose and every definition, `EnhancedHardCore` included, so G3-8 holds. Each of its 5 controls reports exactly 1 difference.
  - decls2 gives 141 ADDED, 0 CHANGED and 0 REMOVED. The only changes to existing declarations are the two targets' proofs and sketches.
- **Axioms.** The two targets and `otProtocol_hbcSecure` use only `propext`, `Classical.choice` and `Quot.sound`, and so do all 234 stored constants. `yaoProtocol_hbcSecure` keeps `sorryAx` through the admitted Yao hybrid.
- **Rule 10.** 28 seals at the head and 4 at the base pass in A and B, strict and coe, with 0 new failures. The coe controls are ALL_OK, and the strict ones are attributed (F-09). The scan finds 0 foreign definitions across 742 items.
- **Admissions.** 31 → 29, by exactly the two targets.
- **Lint.** 92/101 for Cryptography and 25/391 for Complexity, with identical line sets. All widths are ≤ 100 and every file has ≤ 1000 lines.
- **Content.** The proof matches the book.
  - Alice's side is bounded by 2δ(n) at every `n`.
  - Bob's side uses the published `tdpPredictor` around `viewDist`, together with the signed identity. `hEHC` is applied to 16 machines and the bounds are summed into one negligible ε_B.
- **Overlap.** No open PR touches a unit file, and the unit has no PR file in its 128-module closure. The trial merge with #313 is clean.
- **Restore.** `dl-oleans` is exactly `457ba704…` after every stage.

## Findings

| # | Severity | Finding | Disposition |
|---|---|---|---|
| F-01 | minor | `OT.pairSndD_nil'` restates the public `BinArith.iterate_pairSndD_nil` at `1`. It was not disclosed. | **Fixed** by LE-reuse: the proof only changes, with no new import. |
| F-02 | minor | `OT.splitLen` and `splitLen_symm_ofFn` restate the public `coinsEquiv` (used backwards) and `ofFn_coinsEquiv` (`EnsemblesLemmas.lean:141,145`). The body also matches the private ElGamal `dlc_splitEquiv`. This was not disclosed. Reuse needs a new import and a definition change. | **Ruling (Seyoon, 2026-11-15): ledger debt, disclosed.** Recorded as DL-48. The cleanup uses `(coinsEquiv h).symm`. |
| F-03 | info | 50 new public declarations had no formula in their docstring. | **Fixed** by LE-doc. |
| F-04 | info, disclosed | `OT.uprob_signedPredictor_false/_true` adapts `exists_pkPredictor`, because `pkPredictor` has no public reader. | DL-48. The worker's promotion request, with a `pkPredictor_apply` reader, is deferred. |
| F-05 | info | Signing is not recorded in `COMMITS.tsv`. | As prf-long F-03. |
| F-06 | info, disclosed | The helpers restate the owned file's definition bodies by design; the owned file proves the equalities from its readers. | None. |
| F-07 | info | There are near-relatives that were not disclosed: `GI.pairSndD_encodeMsgs` for `getD_one_eq`, and `predict_eq`. The promotion requests are `negligible_finset_sum`, `statClose_prod_of_forall`, `exec_five` and `length_runAtL_le`. | DL-48 notes. |
| F-08 | info | The worker removed another fill's worktree on its own host. | None. |
| F-09 | info | The strict `ctlCoeReader` fails when sealed, a harness effect. The worker's claim that no control can make strict fail is wrong: the strict negative `ctlCoe` fails once. | Attributed. |

## ===== briefs/pass-shelat-ch5-8/gates/34-sc-ot/worker-report.md =====

# Fill sc-ot — final (`otProtocol_polyTime` and `otProtocol_simulators`)

**Unit** `sc-ot` · **Worker** Claude · **Issue base** `107f1e8c218733eac12d6b9bee6fece441271317`
(`cryptography/pass-shelat-ch2-4`) · **Proof branch** `fill/sc-ot` (local), three commits:
`fc7d0366067738271851488a8d1d7d7240cb70f1` (checkpoint 1), `a643e566b57d450d4abdad7b8484215385179233`
(checkpoint 2), `e2c6f1a8f9e16d830e07f9cd3b1158553edb5500` (final) · **Lean** 4.25.0, Mathlib at the base's manifest.

## Target status

| Target | Status |
|---|---|
| `otProtocol_polyTime` | **proved** (`propext`, `Classical.choice`, `Quot.sound`) |
| `otProtocol_simulators` | **proved** (`propext`, `Classical.choice`, `Quot.sound`) |

Both statements are unchanged. Their consumer `otProtocol_hbcSecure` (unchanged) now depends on
the standard axioms only (`logs/final-axioms.log`). The sorry census of the final sweep is
`base-sorries.txt` minus exactly these two declarations (29 declarations in 13 modules).

## 1. Environment (addendum v1)

- **Preflight** (`evidence/logs/preflight.log`): 4 CPUs; cgroup v1 limit unlimited, so the
  headroom is `MemAvailable` = 16503980032 B = 15.37 GiB (floor 4 GiB); the clone's filesystem
  (ext4, `/dev/vda`) had 16496836608 B = 15.36 GiB free (floor 12 GiB): `PREFLIGHT PASS`. To get
  there the git worktree of this host's delivered `canonizer` fill (`/workspace/canon`, branch
  kept) was removed. No dependency tree was copied or moved.
- **Clone:** a new worktree `/workspace/scot` of the local repository, branch `fill/sc-ot` at the
  issue base; its sources match `SOURCE-SHA256SUMS` (159 files, `source-sha256.log`).
- **Cache:** the store (`~/.cache/mathlib`, `cache-store.log`) held 2403 archives (120576651 B)
  from this host's earlier fills of this campaign (not downloaded by this session). The narrowed
  `lake exe cache get` for the 74 roots (`mathlib-roots.txt`, the same list as `roots.txt`)
  reported "No files to download", decompressed 2082 files and exited 0 (`cache-get.log`). No
  zero-size olean among 2091 (`zero-size-oleans.log`); the probe importing
  `Mathlib.Algebra.BigOperators.Field` elaborates (`cache-probe.log`, `probes/CacheProbe.lean`).
- **Packages** (`packages-check.log`): `RESULT: all present packages match the manifest`
  (`doc-gen4`, `UnicodeBasic`, `BibtexQuery`, `MD4Lean` ABSENT; no module of the order imports
  them).
- **Bootstrap** (`bootstrap.log`): the 159 modules of `order.txt`, one `scripts/lean_check_tree.sh`
  call each (through `tools/check.sh`), in order: 159/159 status 0, no error; maximum RSS
  2726572 KiB. Sorry census = `base-sorries.txt` (31 declarations in 14 modules;
  `census-bootstrap.txt`, `census-bootstrap-vs-base.diff`: identical). The whole order was built
  before any check of the owned file.
- **Host restarts.** The VM restarted several times during the session (uptime resets). Every
  long run is resumable and was resumed from its last completed module or run; no log was moved
  or edited. An interrupted run leaves a module header without its end line in the raw log, and is
  rerun in full.
  In particular: one seal run of checkpoint 1 (rerun), a scratch check between the checkpoints,
  and the final sweep once (at module 90, `Asymptotic/OneWayYao`, which has a header without an
  end line in `final-sweep.log` and was then rerun; 166 headers, 165 `status=0`).

## 2. The proof

The helper modules cannot import the owned file (it imports them). So they state every result
for **every protocol and every pair of machines of the shapes** of Protocol 160.4 and of `S_A`,
`S_B`, given by predicates that restate the owned definitions' bodies, and the owned file proves
that `otProtocol`, `otSimA` and `otSimB` have these shapes from its published readers:

```lean
theorem otProtocol_polyTime : otFunctionality.PolyTime (otProtocol T H) :=
  OT.polyTime_of_isOT T hH (otProtocol_isOT T H)

theorem otProtocol_simulators (hT : T.OneWay) (hEHC : EnhancedHardCore T h) : … :=
  OT.simulators_of_isOT T H hH henc (otProtocol_isOT T H) (otProtocol_outV T H henc)
    (otProtocol_outP T H) (otSimA_isSimA T) (otSimB_isSimB T hH) hT
    ((enhancedHardCore_iff T h).1 hEHC)
```

### 2.1 Shape (`ObliviousTransfer/Shape.lean`)

`OT.IsOT T H π`: `π.P.next = OT.senderNext T H`, `π.V.next = OT.receiverNext T H` (the bodies
of `otSender`, `otReceiver` with `otMask` = `OT.mask`, `otKnown`, `otRaw` expanded), coins
`coins_Gen` and `coins_Sample + coins_Sample`, five messages, Alice first. `otProtocol_isOT`
(owned) proves it from `otSender_next`, `otReceiver_next`, `otMask_eq`, `otKnown_eq`, `otRaw_eq`,
`otSender_coins`, `otReceiver_coins`, `otProtocol_rounds`, `otProtocol_verifierFirst`. The module
gives the messages on histories of length 0, 1, 2, the five moves of a prover-first execution
(`OT.exec_five`) and the transcript `([y, []], [i, z, []])` (`OT.transcriptWith_isOT`: the
five-message layout with its two empty fillers).

### 2.2 Checkpoint 1: `otProtocol_polyTime` (`ObliviousTransfer/Efficiency.lean`)

- Alice's raw function `OT.senderRaw` reads the case off the encoded history `w` by the emptiness
  tests `w = []`, `snd w = []` (`polyTimeComputable_isNil`, `polyTimeComputable_ite`): `Gen`'s
  index (`OT.genRaw`), the two masks (`OT.maskRaw`: the inverter on the all-`true` tape
  `polyTimeComputable_unaryPoly`, `H`, XOR), or `[]`. Bob's `OT.receiverRaw` adds a third test and
  uses the sampler on the two coin blocks (`polyTimeComputable_pairTakePoly`/`DropPoly`) and
  `eval_poly`. `OT.senderRaw_advInput`, `OT.receiverRaw_advInput`: on the raw input of an
  activation they compute the next messages for every history (cases `[]`, `[m]`, two, three or
  more messages). So `NUPPT.ofPolyTimeUniform` of them, with the parties' coin polynomials,
  witnesses `Strategy.Efficient` for both.
- Messages (`OT.exists_messages_le`): `|i| ≤ Q₁(n)` (`Gen`'s `runLenPoly`), samples `≤ Q₂(n)`
  (the sampler's `runLenPoly` at `Q₁`), the evaluation `≤ Q₃(n)` (`eval_poly`'s bound at
  `2Q₁ + 2 + Q₂`), masks one bit each: `B = Q₁ + (3(Q₂ + Q₃) + 2) + 5`.

### 2.3 Checkpoint 2: Alice's side (`ObliviousTransfer/Simulators.lean`, `ObliviousTransfer/ViewA.lean`)

- `OT.IsSimA`, `OT.IsSimB` restate `otSimAFun`, `otSimBFun` (with `coinSeg`, `simIdx`,
  `simSample`, `otSimZ`, `otSimZb`) as `OT.simAView`, `OT.simBView`; the owned file proves
  `otSimA_isSimA`, `otSimB_isSimB` from `otSimA_coins`, `runAt_otSimA`, `otSimB_coins`,
  `runAt_otSimB` and the simulator-function readers. The coin spaces: `OT.splitLen` (a tape of
  length `a + b` as two blocks), `OT.realCoins` (the real
  `ExecCoins ≃ Coins_Gen × (Coins_Sample × Coins_Sample)`), `OT.simACoins`, `OT.simBCoins`, with
  `_ofFn` readers; the simulated views on assembled tapes (`OT.simAView_layout`,
  `OT.simBView_layout`); the OT inputs as bits (`OT.inA2`, `OT.inB1`, `OT.ofFn_f_fst`,
  `OT.ofFn_f_snd`, from the published `otFunctionality_*` readers).
- `OT.realA_realCoins`, `OT.idealA_simACoins`: on `(r, s₁, s₂)` Alice's real and ideal samplers are
  `W r y` with `y = ⟨eval ⟨i, w₁⟩, w₂⟩` (`⟨w₂, eval ⟨i, w₁⟩⟩` if `b`) and `y = ⟨w₁, w₂⟩`,
  `w_j = Sample(i; s_j)`, `i = index n r`.
- `OT.statClose_eval_sample`: at every generated index `eval ⟨i, Sample⟩` is `2δ(n)`-close to
  `Sample` under `SampleClose δ` (`δ` to the uniform element mapped by `encD ∘ perm`, `0` from
  `perm`, `δ` back by canonical decoding). `OT.statClose_prod_of_forall` lifts closeness for every
  value of a shared coordinate to the joint samplers.
- `OT.distAdv_realA_idealA_le`: Alice's side is at most `2δ(n)` for every distinguisher, `n` and
  inputs (`acceptProb_comp_equiv` along the coin equivalences, `StatClose.prod` with the identical
  raw sample, the blocks swapped when `b = 1`, `distAdv_le_of_statClose`).

### 2.4 Final: Bob's side (`ObliviousTransfer/Predictor.lean`, `ObliviousTransfer/ViewB.lean`)

- **The views.** `OT.bobView u b a₀ a₁ i s w β` is Bob's view (paired with Alice's `[]`) with
  tape `s`, index `i`, selected mask `H ⟨i, w⟩ ⊕ [a_b]` and unselected mask `[β ⊕ a_{1−b}]`.
  On `(r, s₁, s₂)` the real sampler is `bobView … (s₁ ++ s₂) (Sample(i; s₁)) (B s₂)` with the
  enhanced bit `B s₂ = OT.hcBit T h n r s₂ = h_i(perm_i⁻¹(dec_i(Sample(i; s₂))))`
  (`OT.realB_realCoins`: the selected mask by `OT.mask_eval`, the unselected one by
  `OT.mask_raw`, both through the inverter on the all-`true` tape `OT.inv_runAtL_ones`,
  `inv_eq_encD`, and `henc` extended to decodable strings by `apply_of_decD`); on
  `(r, s₁, s₂, c)` the ideal one is the same with `β = c ⊕ a_{1−b}` (`OT.idealB_simBCoins`).
- **Acceptance.** With `accB … r g = Pr[D(bobView … (g s₂)) = 1]`, the real acceptance is
  `E_r accB r B` (`OT.acceptProb_realB`) and the ideal one `E_r (accB r B + accB r ¬B)/2`
  (`OT.acceptProb_idealB`, `OT.uprob_xor_shear`).
- **The predictor.** `OT.viewDist D b a₀ a₁` (`NUPPT.ofPolyTime` of `OT.viewDistRaw`, `D`'s
  advice, coins `coins_Sample + coins_D`) reads `⟨i, ⟨s', [β]⟩⟩` and its coins `s₁ ++ ρ`, builds
  `bobView (1^n) b a₀ a₁ i (s₁ ++ s') (Sample(i; s₁)) β` and runs `D` on it with `ρ`
  (`OT.distinguisherL_viewDist`). The published `tdpPredictor (viewDist …) flip` of Algorithm
  104.3 is the predictor: by `uprob_tdpPredictor` and the signed-predictor identity for uniform
  coin challenges (`OT.uprob_signedPredictor_false`/`_true`), it predicts `B` from `⟨i, s'⟩` with
  probability `1/2 ± (accB r B − accB r ¬B)/2` (`OT.uprob_predictor_false`/`_true`).
- **The bound.** For the inputs' bits `t = (b, a₀, a₁)`, `hEHC` at the two predictors gives
  `|ε_{t,0}(n)| + |ε_{t,1}(n)|` (`OT.distAdv_realB_idealB_le`, `uexp_half_add`/`_sub`). Over the
  eight triples and two signs, `ε_B(n) = Σ_t Σ_fl |ε_{t,fl}(n)|` is negligible
  (`OT.negligible_finset_sum`) and bounds every input (`OT.exists_negligible_bob`).
- **Together** (`OT.simulators_of_isOT`): `ε(n) = 2|δ(n)| + ε_B(n)`, with `δ` from
  `T.OneWay`'s `sampleClose`.

**Edge cases** (the brief's list): `b = 0, 1` (the two branches of `realA_realCoins`,
`realB_realCoins`, `idealB_simBCoins` and the block swap in `distAdv_realA_idealA_le`); all eight
`(b, a₀, a₁)` (sixteen machines); the five-message layout and its two empty fillers
(`exec_five`, `transcriptWith_isOT`); non-canonical strings (`apply_of_decD` in `mask_eval`,
canonical decoding in `statClose_eval_sample` and `mask_raw`); the inverter's fixed all-`true`
tape (`inv_runAtL_ones`, and `OT.maskRaw` in the machine); small `n` (`SampleClose δ` holds at
every `n`, so Alice's bound needs no threshold; only the final `ε` is asymptotic); the
distinguisher's advice (`viewDist` and `tdpPredictor` keep `D`'s advice and advice polynomial).

**Route differences from the maintainer's sketch** (statements unchanged): the predictor machine
is the published `tdpPredictor` around `OT.viewDist` (an `ofPolyTime` machine) rather than a new
`NUPPT.exists_comp` composite; and instead of the worst of the eight triples as advice, each
triple is hard-wired in its own machine and the sixteen bounds are summed (equivalent, and it
keeps `D`'s advice untouched).

### 2.5 The owned file

`ObliviousTransfer.lean` (671 → 747 lines): the six helper imports (each directly), the title
without "(statement phase)", `## Main results` (the new `otProtocol_isOT`, `otSimA_isSimA`,
`otSimB_isSimB`; both targets proved), a `## Contents` list of the helpers, the two proofs, and the
two targets' `**Proof sketch.**` paragraphs rewritten to describe the delivered proofs (the
statement prose is unchanged). No other declaration changed.

### 2.6 New declarations (namespace `TCSlib.Cryptography.SecureComputation`)

- Owned file: `otProtocol_isOT`, `otSimA_isSimA`, `otSimB_isSimB`.
- `OT.` in `Shape.lean` (206 lines): `mask`, `mask_eq`, `senderNext`, `senderNext_eq`,
  `receiverNext`, `receiverNext_eq`, `IsOT`, `isOT_iff`, `senderNext_nil`, `senderNext_single`,
  `senderNext_pair`, `receiverNext_single`, `receiverNext_pair`, `exec_five`,
  `transcriptWith_isOT`.
- `OT.` in `Efficiency.lean` (526 lines): `headD_eq_pairFstD`, `pairSndD_nil'`, `getD_one_eq`,
  `runAtL_eq_layout`, `advInput_layout`, `genRaw`, `genRaw_eq`, `polyTimeComputable_genRaw`,
  `maskRaw`, `maskRaw_eq`, `polyTimeComputable_maskRaw`, `senderRaw`, `senderRaw_eq`,
  `polyTimeComputable_senderRaw`, `genRaw_layout`, `maskRaw_layout`, `getD_zero_eq`,
  `getD_one_eq'`, `senderRaw_advInput`, `knownRaw`, `knownRaw_eq`, `rawRaw`, `rawRaw_eq`,
  `outRaw`, `outRaw_eq`, `pairRaw`, `pairRaw_eq`, `receiverRaw`, `receiverRaw_eq`,
  `polyTimeComputable_receiverRaw`, `knownRaw_layout`, `rawRaw_layout`, `receiverRaw_advInput`,
  `length_runAtL_le`, `length_zipWith_singleton_le`, `length_mask_le`, `exists_messages_le`,
  `polyTime_of_isOT`.
- `OT.` in `Simulators.lean` (431 lines): `splitLen`, `splitLen_symm_ofFn`, `simSeg`,
  `simSeg_eq`, `simIndex`, `simIndex_eq`, `simSampled`, `simSampled_eq`, `simAView`,
  `simAView_eq`, `simZbit`, `simZbit_eq`, `simZpair`, `simZpair_eq`, `simBView`, `simBView_eq`,
  `IsSimA`, `isSimA_iff`, `IsSimB`, `isSimB_iff`, `simSeg_layout`, `length_ofFn_coins`,
  `simIndex_layout`, `simSampled_layout`, `simAView_layout`, `simBView_layout`, `realCoins`,
  `realCoins_symm_fst_ofFn`, `realCoins_symm_snd_ofFn`, `simACoins`, `simACoins_symm_ofFn`,
  `simBCoins`, `simBCoins_symm_ofFn`, `inA_eval`, `inB_eval`, `inA2`, `inA2_apply`, `ofFn_inA2`,
  `inB1`, `inB1_apply`, `ofFn_inB1`, `ofFn_eq_inB1`, `ofFn_f_fst`, `ofFn_f_snd`.
- `OT.` in `ViewA.lean` (186 lines): `statClose_prod_of_forall`, `statClose_eval_sample`,
  `realA_realCoins`, `idealA_simACoins`, `distAdv_realA_idealA_le`.
- `OT.` in `Predictor.lean` (206 lines): `bobView`, `bobView_eq`, `polyTimeComputable_bobView`,
  `viewRaw`, `viewRaw_eq`, `viewDistRaw`, `viewDistRaw_eq`, `polyTimeComputable_viewDistRaw`,
  `viewDist`, `viewDist_coins`, `viewDistCoins`, `viewDistCoins_symm_ofFn`, `runAtL_viewDist`,
  `distinguisherL_viewDist`.
- `OT.` in `ViewB.lean` (534 lines): `uprob_signedPredictor_false`, `uprob_signedPredictor_true`,
  `uprob_xor_shear`, `negligible_finset_sum`, `hcBit`, `hcBit_eq`, `inv_runAtL_ones`, `mask_eval`,
  `mask_raw`, `ofFn_inA2_eq`, `realB_realCoins`, `idealB_simBCoins`, `accB`, `accB_eq`,
  `acceptProb_realB`, `acceptProb_idealB`, `acceptProb_viewDist`, `uprob_predictor_false`,
  `uprob_predictor_true`, `distAdv_realB_idealB_le`, `exists_negligible_bob`, `simulators_of_isOT`.

Every public `def` has an `_eq`/`_iff` reader (or, for the coin equivalences, `_ofFn` readers
named after them, which lint check 8 accepts); every docstring states its formula; every proof
of 15 lines or more has a `**Proof sketch.**`; no `@[simp]` was added.

## 3. Overlap and reuse

Searches: `logs/checkpoint1-searches.log`, `logs/final-searches.log` (TCSlib at the base,
Mathlib/Batteries, Lean core). **Reused** (published, imported): `uprob_tdpPredictor`,
`tdpPredictor`, `uexp_half_add`, `uexp_half_sub` (`Encryption/PublicKey/TrapdoorPredictor.lean`);
`distAdv_le_of_statClose`, `StatClose.prod`, `.map`, `.trans`, `.refl`, `.comp_equiv_left`,
`abs_uexp_sub_le` (`Asymptotic/Sampling.lean`); `uprob_prod`, `uprob_comp_equiv`, `uprob_not`,
`uprob_bool_prod`; `acceptProb_comp_equiv`; `splitCoins`, `ofFn_splitCoins_symm`,
`NUPPT.runLenPoly`, `length_runAt_le_runLenPoly`; `inv_eq_encD`, `apply_of_decD`,
`evalSampled_iff`, `decD_eq_some_iff`, `f_perm`, `sampleClose_iff`; `Negligible.add`,
`.const_mul`, `.mono`, `negligible_zero`; `polyTimeComputable_isNil`, `_ite`, `_headD`, `_tail`,
`_pairXor`, `_pairTakePoly`, `_pairDropPoly`, `_unaryPoly`, `BinArith.polyTimeComputable_xor`,
`NUPPT.ofPolyTime`, `ofPolyTimeUniform` and their readers.

| New declaration | Nearest relative | Relation | Why not reused |
|---|---|---|---|
| `OT.uprob_signedPredictor_false`, `_true` | `predProb_pkPredictor_false`, `_true`, `exists_pkPredictor` (`Encryption/PublicKey/Trapdoor.lean:317,326,337`); `predProb_owpPredictor_false`, `_true` (`Pseudorandom/GeneratorFromPermutation.lean:131,172`) | **the expected adapted copy**: the same signed-predictor identity, for a uniform challenge `x` itself (the `⟨i, coins⟩` challenges, `f = id`), stated with the explicit predictor `(if D(x, c; ρ) then c else ¬c) ⊕ flip`; proved like `predProb_owpPredictor_false` | `pkPredictor` has no published reader and the bridge `predProb_pkPredictor_eq` is private; `owpPair`, `owpGen`, `owpGenNot` have no readers either. Under the rule-10 seals the identity cannot be read off them. **Promotion request** below |
| `OT.uprob_xor_shear` | `uprob_bool_prod` (`GeneratorFromPermutation.lean:59`) and the bijection inside `predProb_owpPredictor_false` | a re-centred form | no published lemma for a masked uniform bit |
| `OT.negligible_finset_sum` | `Negligible.add` (`Foundations/Negligible.lean:86`) | its finite-sum form, by induction | no finite-sum lemma exists (searched `Negligible.*∑`, `negligible_sum`) |
| `OT.hcBit` | the bit of `EnhancedHardCore`'s experiment (`ObliviousTransfer.lean:231`); private `tdpSampled` (`Trapdoor.lean:351`) | the bit, named | the helper cannot import the owned file; `tdpSampled` is private |
| `OT.inv_runAtL_ones` | `TrapdoorCollection.inv_eq_encD` (`Asymptotic/Collections.lean:415`); the same step inside `otProtocol_outV` | `inv_eq_encD` on the all-`true` list tape | the masks run the inverter on a list |
| `OT.mask_eval`, `OT.mask_raw` | steps of `otProtocol_outV`; private `tdpBitScheme_pkEncDist` (`Trapdoor.lean:357`) | the masks on Bob's real pair | needed as rewrite lemmas; the latter is private |
| `OT.bobView`, `OT.viewRaw`, `OT.viewDistRaw`, `OT.viewDist`, `OT.viewDistCoins` and lemmas | `tdpPredFun`, `tdpPredictor`, `predCoins` (`TrapdoorPredictor.lean`) | the same construction pattern for a different distinguisher; `tdpPredictor` itself is reused around it | a new machine |
| `OT.accB`, `OT.acceptProb_realB`, `OT.acceptProb_idealB`, `OT.acceptProb_viewDist`, `OT.uprob_predictor_false`, `_true`, `OT.distAdv_realB_idealB_le` | the steps `hclose`, `key`, `hf`, `ht` inside `TrapdoorCollection.tdpBitScheme_singleBitSecure` (`Trapdoor.lean:412`) | the analogous steps for Bob's view | different samplers |
| `OT.mask`, `OT.senderNext`, `OT.receiverNext`, `OT.simSeg`, `OT.simIndex`, `OT.simSampled`, `OT.simAView`, `OT.simZbit`, `OT.simZpair`, `OT.simBView` | `otMask`, `otSender`, `otReceiver`, `coinSeg`, `simIdx`, `simSample`, `otSimAFun`, `otSimZb`, `otSimZ`, `otSimBFun` (the owned file) | restatements of the bodies | the helpers cannot import the owned file; `otProtocol_isOT`, `otSimA_isSimA`, `otSimB_isSimB` prove the equalities from the published readers |
| `OT.exec_five`, `OT.transcriptWith_isOT` | `exec_succ`/`exec_zero` (`ZeroKnowledge/Interaction.lean:262,266`); the unfolding inside `otProtocol_outV` | the five-move unfolding, stated once | no five-move lemma exists |
| `OT.headD_eq_pairFstD` | `Strategy.pairFstD_encodeMsgs` (`Interaction.lean:143`) | its symmetric form | used as a left-to-right rewrite |
| `OT.pairSndD_nil'`, `OT.getD_one_eq` | private `pairSndD_nil` (`Asymptotic/BlockEncryptor.lean:156`); `GI.pairSndD_encodeMsgs`, `GI.encodeMsgs_eq_nil_iff` (`GraphIsomorphism/EfficiencyRep.lean:93,110`) | re-derived from the public `length_pairSndD_le` (`ClassNP/PolyTimeBlockLoop.lean:187`) | the first is private; `EfficiencyRep` comes after the owned module in `order.txt` |
| `OT.runAtL_eq_layout`, `OT.advInput_layout` | `NUPPT.runAtL_eq_output_layout` (`Randomized/Closure.lean:159`); `advInput_eq`, `layout_eq` | uniform specialization; composite | match `runAtL_ofPolyTimeUniform` |
| `OT.getD_zero_eq`, `OT.getD_one_eq'` | `List.getD_cons_zero`, `List.getD_cons_succ` (core `Init/Data/List/Lemmas.lean:330`) | the `headD` forms for every list | the core lemmas cover cons only |
| `OT.length_runAtL_le` | `NUPPT.length_runAt_le_runLenPoly` (`Asymptotic/CollectionsHelpers.lean:132`) | its list form, proved from it | the strategies' tapes are lists |
| `OT.length_zipWith_singleton_le`, `OT.length_mask_le` | `List.length_zipWith` | two-line consequences | — |
| raw functions `OT.genRaw` … `OT.receiverRaw` and lemmas | `GI.giProver_efficient`, the GI/3-col machines (`GraphIsomorphism/EfficiencyRep*.lean`, `ThreeColoring/Machines.lean`) | the same pattern (raw layout function, `ofPolyTimeUniform`) | specific to Protocol 160.4 |
| `OT.splitLen`, `OT.splitLen_symm_ofFn` | `splitCoins`, `ofFn_splitCoins_symm` (`CollectionsHelpers.lean:145,172`); `Fin.appendEquiv` | `splitCoins` after a length cast, proved from `ofFn_splitCoins_symm` | the coin lengths are `coinLen`/`PolyExpr.eval` terms, not syntactic sums |
| `OT.realCoins`, `OT.simACoins`, `OT.simBCoins`, `OT.length_ofFn_coins` | `Collection.owfCoinsEquiv`, `NUPPT.coinsEquivPoly` | coin equivalences of the same kind | specific layouts |
| `OT.inA2`, `OT.inB1`, `OT.ofFn_f_fst`, `OT.ofFn_f_snd`, `OT.ofFn_inA2_eq` | `otFunctionality_inA`, `_inB`, `_outA`, `_f_snd_apply` (`SecureComputation/Defs.lean:202–232`) | consequences of the published readers | inputs as `Fin 2`/`Fin 1` functions for `otProtocol_outV` |
| `OT.statClose_prod_of_forall` | `StatClose.prod`, `StatClose.abs_uprob_sub_le_prod` (`Sampling.lean:237,262`) | the dependent form | `StatClose.prod` needs independent coordinates |
| `OT.statClose_eval_sample` | `hclose` inside `tdpBitScheme_singleBitSecure` | a related use of `SampleClose` | different samplers |

No private lemma was copied. **Promotion requests** (general lemmas in this fill's helpers, for
landing; none is needed for the proofs to stand):
- `OT.uprob_signedPredictor_false`/`_true` beside `exists_pkPredictor` in
  `Encryption/PublicKey/Trapdoor.lean` (with a reader `pkPredictor_apply`, which would also let
  `predProb_pkPredictor_false` serve sealed consumers);
- `OT.negligible_finset_sum` in `Foundations/Negligible.lean`;
- `OT.statClose_prod_of_forall` beside `StatClose.prod` in `Asymptotic/Sampling.lean`;
- `OT.exec_five` beside `exec_succ` in `ZeroKnowledge/Interaction.lean`;
- `OT.length_runAtL_le` beside `NUPPT.length_runAt_le_runLenPoly` in
  `Asymptotic/CollectionsHelpers.lean`.

**Reader request** (optional, not used): `pkPredictor_apply`, `owpPair_apply`, `owpGen_apply`,
`owpGenNot_apply` would make the published predictor identities usable under the seals.

## 4. Scope requests

None. No frozen file was edited (`git diff --stat` from the base touches only the owned file and
the six new helpers under `SecureComputation/ObliviousTransfer/`). Seyoon was not asked anything.

## 5. Checks (final)

- **Owned module recheck** (`logs/final-owned-recheck.log`): status 0, no warning.
- **Final sweep** (`logs/final-sweep.log`, order `logs/final-order.txt`: `order.txt` with the six
  helpers inserted before `ObliviousTransfer`, 165 modules): every module status 0, 0 errors;
  maximum RSS 2645308 KiB.
- **Census** (`logs/final-census.txt`, `logs/final-census-vs-base.diff`): 29 declarations in 13
  modules; the only difference from `base-sorries.txt` is the row
  `SecureComputation/ObliviousTransfer: 2: otProtocol_simulators, otProtocol_polyTime`, absent
  at the final.
- **Axioms** (`logs/final-axioms.log`, `probes/AxiomsFinal.lean`): `otProtocol_polyTime`,
  `otProtocol_simulators` and `otProtocol_hbcSecure`: `[propext, Classical.choice, Quot.sound]`.
  Every stored constant of the owned module and the six helpers, enumerated from the environment
  (234 constants: 70 owned, 15 `Shape`, 49 `Efficiency`, 55 `Simulators`, 7 `ViewA`, 15
  `Predictor`, 23 `ViewB`, auxiliary constants included): **0 with a non-standard axiom**.
- **Seals** (`seals/`): whole-file seals of the seven changed or new files at the final, and of
  the owned file at the base (a verbatim copy, `base/ObliviousTransferBase.lean`, recorded under
  the original path), each over its full TCSlib import closure, in the four variants A-strict,
  A-coe, B-strict, B-coe (A: `PolyExpr.eval` excluded as notation; B: sealed; coe: projection
  coercions excluded, the only one in this closure being `FinDist.instCoeFunForallReal`):
  **every run status 0, 0 errors** (28 final runs, 4 base runs; `final-*.jsonl`, `base-*.jsonl`,
  raw `.out`, sealed copies in `seals/sources/`; errors counted with `error[:(]`). Comparison
  (`seals/seals-compare.log`): no new failing declaration against the base, and no difference
  between strict and coe, nor between A and B: nothing to attribute.
- **Paired controls** (`controls/`, `logs/controls-plain.log`, `seals/controls-*.jsonl`):
  `CtlUnfold` (`NUPPT.layout u y α r = ⟨⟨⟨u, y⟩, α⟩, r⟩ := rfl`, a foreign library definition)
  and `CtlUnfoldHelper` (`OT.mask … = … := rfl`, a helper definition, foreign to every other
  module): unsealed 0, **1 error in each of the four sealed variants**; `CtlEval`
  (`(PolyExpr.const 5).eval 3 = 5 := rfl`): unsealed 0, A 0, **B 1**; `CtlReader` (the same facts
  through `layout_eq`, `OT.mask_eq`, `eval_const`): 0 everywhere; `CtlCoe` (an explicit application
  of `FinDist.instCoeFunForallReal` by `rfl`): 0 everywhere, a documented probe, not a negative
  control (Lean reduces a projection of an instance even when the strict seal makes the instance
  irreducible). Each sealed negative fails exactly once; the positive passes.
- **Explicit-unfold scan** (`scan/`, `logs/scan-*.log`): every identifier given to
  `rw`/`simp`/`unfold`/… in the seven files, resolved: **0 foreign TCSlib definitions** at the
  final (392 rows) and at the base (47 rows); `scan/scan-compare.log`: "NEW foreign explicit
  unfolds: 0". The own-definition rows are the owned file's 14 at the base (unchanged:
  `otProtocol`, `otSender`, `otReceiver`, … inside the pre-existing correctness proofs) and three
  helper-internal ones (`viewDist`, `simACoins`, `simBCoins`, each in its own file).
- **Width and size** (`logs/final-width.log`): no line over 100 characters; the owned file has
  747 lines, the helpers 206, 526, 431, 186, 206 and 534.
- **Lint** (`logs/base-lint.log`, `logs/final-lint.log`, `logs/final-lint-vs-base.diff`):
  92 FAIL / 101 WARN at the base and at the final; the FAIL/WARN line sets are identical (no new
  line). The facade check is satisfied: the owned file imports each helper directly.
- **Patches** (`patches/`, `patches/COMMITS.tsv`): the three commits from the base. Reproduction
  (`logs/final-repro.log`): `git am` at the base in a scratch clone (`/tmp/scot-repro`, deleted
  afterwards), with the committer identity and date of `COMMITS.tsv`: every hash reproduced.
- **Checkpoints** (kept): `logs/checkpoint1-*`, `logs/checkpoint2-*`, `seal-cp1/`, `seal-cp2/`,
  `probes/AxiomsCP1.lean`, `probes/AxiomsCP2.lean`.

## 6. Evidence (`evidence/`, manifest `evidence/SHA256SUMS`)

- `logs/`: environment (`preflight.log`, `source-sha256.log`, `order.txt`, `mathlib-roots.txt`,
  `cache-store.log`, `cache-get.log`, `packages-check.log`, `zero-size-oleans.log`,
  `cache-probe.log`), bootstrap (`bootstrap.log`, `census-bootstrap.txt`,
  `census-bootstrap-vs-base.diff`), checkpoints 1 and 2 (`checkpoint{1,2}-checks.log`,
  `census-checkpoint{1,2}-checks.txt`, `checkpoint{1,2}-axioms.log`, `checkpoint{1,2}-width.log`,
  `checkpoint{1,2}-lint.log`, `checkpoint{1,2}-lint-diff.log`, `checkpoint{1,2}-repro.log`,
  `checkpoint1-searches.log`), final (`final-order.txt`, `final-owned-recheck.log`,
  `final-sweep.log`, `final-census.txt`, `final-census-vs-base.diff`, `final-axioms.log`,
  `final-width.log`, `final-lint.log`, `final-lint-vs-base.diff`, `final-repro.log`,
  `final-searches.log`, `final-pipeline.log`, `controls-plain.log`, `scan-final.ids.log`,
  `scan-final.raw.log`, `scan-base.ids.log`, `scan-base.raw.log`), `base-lint.log`.
- `seals/`: `final-*.jsonl`/`.out`, `base-*.jsonl`/`.out`, `controls-*.jsonl`/`.out` (four
  variants each), `seals-compare.log`, `sources/` (every sealed copy: `f*` final, `b*` base,
  `c*` controls).
- `seal-cp1/`, `seal-cp2/`: the checkpoint seals.
- `scan/`: `scan-final.tsv`, `scan-base.tsv`, `scan-compare.log`, `sources/` (the scan modules).
- `controls/`: `CtlUnfold.lean`, `CtlUnfoldHelper.lean`, `CtlEval.lean`, `CtlReader.lean`,
  `CtlCoe.lean`. `base/`: `ObliviousTransferBase.lean` (the base copy of the owned file).
- `probes/`: `CacheProbe.lean`, `AxiomsCP1.lean`, `AxiomsCP2.lean`, `AxiomsFinal.lean`.
- `tools/`: every script used (`check.sh`, `dev.sh`, `devall.sh`, `sweep_chunk.sh`, `census.py`,
  `cmpcensus.sh`, `pkgcheck.py`, `seal_gen.py`, `seal_run.py`, `seal_all.sh`, `seal_cp1.sh`,
  `seal_cp1b.sh`, `cp2_checks.sh`, `rwids.py`, `rwids_run.sh`, `cmp_scans.py`, `width_check.py`,
  `run_final.sh`, `final_pipeline.sh`, `payload.sh`, `repro_check.sh`, `manifest.sh`,
  `finalize.sh`).
- `patches/` (three patches and `COMMITS.tsv`), `src/` (the seven changed or new files at the
  final commit).

The top-level `SHA256SUMS` lists every delivered file under `inbox/fills/sc-ot/` except itself;
the delivered paths equal the manifest's (checked before the push).

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

## ===== briefs/pass-shelat-ch5-8/fills/sc-ot/issued-r1/brief.md =====

# Claude fill · oblivious transfer from trapdoor permutations (`otProtocol_polyTime` and `otProtocol_simulators`, Protocol 160.4 and Proposition 161.5)

**Issue base** `107f1e8c218733eac12d6b9bee6fece441271317` on `cryptography/pass-shelat-ch2-4` (the records tip after #303, #305, #306,
#308 and #309; records-only commits since `58a061c9`). **Unit** `sc-ot`. **Worker** Claude (standing ruling, 2026-11-11). **Lean** 4.25.0 and the
Mathlib revision in that commit's `lake-manifest.json`.

Prove the admitted theorems `otProtocol_polyTime` and `otProtocol_simulators` of [PS10, Protocol 160.4 and Proposition 161.5] in
`TCSlib/Cryptography/SecureComputation/ObliviousTransfer.lean`. The statements passed the prong B statement phase (ruling G3-8, applied in `587843c7`) and Gate 06B (closed PASS),
and are frozen. Each docstring holds the maintainer's proof sketch.

## Feasibility (maintainer's assessment)

Feasible as stated (plan §2.1–2.2: both statements well posed, G3-8 closed). The infrastructure is mostly present. The missing pieces are the five-move view equations, the coin-space equivalences, and an adapted `exists_pkPredictor`, which is an overlap to disclose. No dependency on an admitted target: the OT file is independent of every other secure-computation admission.

**Estimated size:** 2,000–3,400 lines (plan: `otProtocol_polyTime` 500–900, `otProtocol_simulators` 1,500–2,500), in 3–6 helper modules. `ObliviousTransfer.lean` is at 671 lines.

## Checkout and delivery

- Fetch `cryptography/pass-shelat-ch2-4`. Start a local branch `fill/sc-ot` at the exact issue base, and
  record the base in `REPORT.md`. Keep the proof branch local.
- Read `policy.md`, the attached environment addendum and `README.md`.
- Deliver every checkpoint and the final payload under `inbox/fills/sc-ot/` on `exchange/pass-shelat-ch5-8`:
  - `REPORT.md`;
  - `patches/`: the whole `git format-patch` series from the issue base;
  - `patches/COMMITS.tsv`: one row per commit, giving its hash, the author's name, email and date, and the
    committer's name, email and date, so that `git am` at the base reproduces every hash. Before you push,
    check the reproduction in a scratch clone and say so in `REPORT.md`. The last batch's worker hashes
    could not be reproduced, because no committer metadata was delivered;
  - `src/`: the changed and new files;
  - `evidence/`, with an `evidence/SHA256SUMS` manifest (see *Evidence completeness*);
  - a top-level `SHA256SUMS` listing every delivered file under `inbox/fills/sc-ot/` except itself. The
    delivered paths must equal the manifest's paths exactly, with nothing missing and nothing extra.
    Check this before each push.
- Commit as `fill sc-ot: checkpoint N` and `fill sc-ot: final`.
- Pull with rebase before pushing, push only your delivery path, and never force-push. Campaign changes land
  by a maintainer PR for Seyoon's approval.

## Base and parallel work

- **#307 (dl-crh) is not merged.** It changes `Candidates/DiscreteLog.lean`, the `Hashing.lean` facade and `Hashing/FromDiscreteLog*`. This unit edits none of them, and its closure contains none of them.
- The other fills of this batch (`prf-mac`, `learning`, `derand`, `seq-zk`, `canonizer`, `sc-compose`) start from the same base.
  Each edits only its own owned file and helper directory.

## Targets (frozen; quoted from the issue base)

```lean
theorem otProtocol_polyTime : otFunctionality.PolyTime (otProtocol T H) := by
  sorry
```

```lean
theorem otProtocol_simulators (hT : T.OneWay) (hEHC : EnhancedHardCore T h) :
    ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n (x : Fin (otFunctionality.inA.eval n) → Bool)
        (y : Fin (otFunctionality.inB.eval n) → Bool),
        distAdv (otFunctionality.realA (otProtocol T H) n x y)
            (otFunctionality.idealA (otSimA T) n x y) (D.distinguisherL n) ≤ ε n ∧
          distAdv (otFunctionality.realB (otProtocol T H) n x y)
            (otFunctionality.idealB (otSimB T hH) n x y) (D.distinguisherL n) ≤ ε n := by
  sorry
```

They live in namespace `TCSlib.Cryptography.SecureComputation`. The section variable is `(T : TrapdoorCollection)`. In the section `Security` the variables are
`{h : ∀ i, T.D i → Bool}`, `(H : List Bool → List Bool)`, `(hH : PolyTimeComputable H)` and
`(henc : ∀ i x, H ⟨i, encD i x⟩ = [h i x])`. `otProtocol_simulators` also takes `hT : T.OneWay` and
`hEHC : EnhancedHardCore T h`.

**The protocol** (five messages; owned, read through its lemmas): `otSender`, `otReceiver`, `otProtocol` and their
field equations, `otMask_eq`, `otKnown_eq`, `otRaw_eq`, the simulator functions and `otSimA`/`otSimB`
(`otSimA_coins`, `otSimA_uniform`, `runAt_otSimA`, and the same for `B`), `SamplerCanonical`, and the proved
correctness `otProtocol_outV`, `otProtocol_outP`. `otProtocol_hbcSecure` (proved from the two targets) is the
consumer, and through it `YaoReal.yaoProtocol_hbcSecure`.

**G3-8 is closed.** The enhanced hard-core predicate was ruled (A) on 2026-11-05 and applied in prong B
(`587843c76f95f10056c9ddc9174da9dc8fba8b54`). `EnhancedHardCore` is already a hypothesis of the frozen
`otProtocol_simulators`, `otProtocol_hbcSecure` and `yaoProtocol_hbcSecure`, and Gate 06B closed PASS with it.
Read the module docstring's deviations: five messages, random elements, and the enhanced predicate. (No collection
in the library is yet proved to have such a predicate; that limits use of the result, not its proof.)

**Analysis.** The maintainer's analysis is `briefs/pass-shelat-ch5-8/maintainer/securecomp-plan-2026-11-14/plan.md`,
§2.1 and §2.2. It checked both statements and found them well posed.

## Published interfaces

| Interface | Provider |
|---|---|
| the protocol and simulator readers listed above; `enhancedHardCore_iff`; `polyTimeComputable_coinSeg` and the other `polyTimeComputable_*` of the file | owned file |
| `polyTime_iff`, `hbcSecure_iff`, `realA_eq`, `realB_eq`, `idealA_eq`, `idealB_eq`, the `otFunctionality_*` readers | `SecureComputation/Defs.lean` (frozen) |
| `Collection.sample_spec`, `inv_spec`, `f_perm`, `apply_of_decD`, `eval_poly`, `SampleClose`; `runLenPoly` | `Asymptotic/Collections.lean`, `Asymptotic/CollectionsHelpers.lean` |
| `StatClose`, `distAdv_le_of_statClose`; `uprob_prod`, `uprob_comp_equiv`, `uprob_exists_le` | `Asymptotic/Sampling.lean`, `Foundations/Probability.lean` |
| `exists_pkPredictor` (the signed-predictor identity of Algorithm 104.3, stated for `f : α ≃ α` inputs) | `Encryption/PublicKey/Trapdoor.lean:337` |
| `NUPPT.ofPolyTimeUniform`, `exists_comp`, `exists_withAdvice`, `exists_split`, `polyTimeComputable_layout`, `polyTimeComputable_output`, `Computes.polyTimeComputable` | `Complexity/Randomized/{Closure,PPT}.lean` |
| `Strategy`, `efficient_iff`, `encodeMsgs`; history readers `pairSndD_encodeMsgs`; `polyTimeComputable_stateFind`; `countW` | `ZeroKnowledge/Interaction.lean`, `…/GraphIsomorphism/EfficiencyRep.lean`, `…/EncodingMachines.lean`, `Complexity/ClassP/BinaryArith/Words.lean` |
| `Negligible.add`, `const_mul`, `mono` | `Foundations/Negligible.lean` |
| `simulate` and `OracleComp` laws, `buildComp_*`, `CostBoundedBy`, `bitCodec_*`, `ProbComp.expect_*`, `advantage_eq`, `accept_eq` | `Games/*` |

## Proof route and checkpoints

1. **Checkpoint 1 · `otProtocol_polyTime` (plan §2.1).** Alice's and Bob's next-message functions branch only on the history length. Write each as a polynomial-time function on the raw layout (Gen, the sampler and the inverter are uniform machines, `eval` is `eval_poly`, `H` is `hH`), make it a uniform machine with `NUPPT.ofPolyTimeUniform`, and prove the message bound: the index (at most Gen's output, `runLenPoly`), two sampler outputs or evaluations, two one-bit masks, and empty fillers. Reuse the encoded-history readers; the plan estimates 500–900 lines. Send this checkpoint.
2. **Checkpoint 2 · Alice's side of `otProtocol_simulators` (sketch steps 1–2).** The view equations of the five-move execution (the pattern of `otProtocol_outV`), the coin-space equivalence between Alice's real tape and `S_A`'s, and the bound `2δ(n)` from `SampleClose` per generated index (`perm` is a bijection, `y_{1−b}` is canonical by `SamplerCanonical`) through `distAdv_le_of_statClose`. Send this checkpoint.
3. **Final · Bob's side (sketch steps 3–4).** The adapted signed predictor for `⟨i, s'⟩` challenges (disclosed, see above), the predictor machine by `NUPPT.exists_comp` with the worst of the eight triples `(b, a₀, a₁)` as advice, the bound `2 ε_EHC(n)` from `hEHC`, and one negligible `ε` covering both sides.

Check the edge cases: `b = 0` and `b = 1`; all eight `(b, a₀, a₁)`; the five-message layout and its two empty fillers; non-canonical strings (`apply_of_decD`); the inverter's fixed all-`true` tape; small `n` where `SampleClose` is only eventual; the distinguisher's advice.

If the sketch is wrong, or a target is false as stated, stop and escalate with the exact obligation: a
checkpoint with the counterexample or the missing fact. Do not weaken any statement.

**Partial delivery.** If you cannot finish every target, your final payload may prove a subset. Each proved
declaration must use only the standard axioms. The others keep their `sorry` and their statements,
and `REPORT.md` says which are proved and what remains for each of the others.

## Scope and proof discipline

- **Owned file.** You own `TCSlib/Cryptography/SecureComputation/ObliviousTransfer.lean` (671 lines at the issue base):
  - replace the targets' proof bodies and edit their sketches to describe the delivered proof;
  - update the module title (drop "(statement phase)" where present) and the `## Main results` status.
- **Helper modules.**
  - They are permitted under `TCSlib/Cryptography/SecureComputation/ObliviousTransfer/`. The owned file imports them precisely and gets a
    `## Contents` list.
  - **Facades.** After the facade-lint fix (#305), a new helper under `X/` is covered as long as `X.lean`
    imports it, so no parent facade needs an edit.
  - A helper may import `Encryption/PublicKey/Trapdoor`, `ZeroKnowledge/GraphIsomorphism/EfficiencyRep` and `ZeroKnowledge/EncodingMachines`. None depends on the owned file (checked at the issue base); the order includes their upstream closure. `SecureComputation/Defs.lean`, `Hybrid.lean`, `Compose.lean`, `ComposePhases.lean`, `SpecialEncryption.lean`, `GarblingSpecial.lean`, `YaoReal.lean`, `Yao.lean`, `Garbling*.lean`, the `FromPRF*` files and `Pseudorandom/*` are named frozen for this unit (with every other file).
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
- **No ℓ-output PRF.** This unit does not need the ℓ₂-output PRF machinery. Seyoon ruled that the PRF layer is generalized in a separate job, `prf-long`; do not build or copy any of it. If you find you need it, stop and escalate with the exact obligation.
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
  - **Nearest relatives here:** `exists_pkPredictor` (`Encryption/PublicKey/Trapdoor.lean:337`), the graph-isomorphism efficiency proofs (`giProver_efficient`, `ZeroKnowledge/GraphIsomorphism/EfficiencyRep.lean`), the history readers of `ZeroKnowledge/ThreeColoring/Machines.lean` (`iterate_pairSndD_encodeMsgs`), and the Algorithm 104.3 machines of `Encryption/PublicKey/Trapdoor.lean`. **Expected overlap:** the plan finds that Bob's side needs an adapted copy of `exists_pkPredictor` for `⟨i, coins⟩` challenges. State it in its general form in a helper, and disclose it as an overlap with `exists_pkPredictor` (and propose it for promotion), since `PublicKey/Trapdoor.lean` is frozen.
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
  - Bootstrap from `order.txt` (159 modules) and the narrow `roots.txt` (74), following the addendum.
  - Check one module per `scripts/lean_check_tree.sh` call, with one Lean process per olean tree.
  - Never run `lake build` or an unfiltered cache get. Run Python as `python3 -I`.
  - Insert helper modules before their consumers.
- **Sweep.**
  - Recheck the owned module, then sweep the supplied order with 0 errors.
  - Compare the `sorry` warnings with `base-sorries.txt` (31 declarations in 14 modules). The only change
    must be the removal of `otProtocol_polyTime` and `otProtocol_simulators`.
- **Axioms.**
  - Print the axioms of `otProtocol_polyTime` and `otProtocol_simulators`. Expect only `propext`, `Classical.choice` and `Quot.sound`.
  - Print them for every stored constant of the changed and new files.
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
| DL-47 | Gate 32 staging (2026-11-15), pre-existing: copies of `((List.ofFn f).drop i).headD d = f i` and of its getD form `(List.ofFn f).getD i d = f i`, at the tip `e9998722`. Inline chain: `Pseudorandom/NextBit.lean:454` (`headD_drop, List.getD_eq_getElem?_getD, List.getElem?_ofFn`, the remnant of NextBit's private `headD_drop_ofFn` that dl-consolidation L1 deleted). Index-0 cases: `headD_ofFn_one` (`Foundations/BitLists.lean:75`), `GIZK.headD_ofFn_block` (`ZeroKnowledge/GraphIsomorphismZK/Closeness.lean:280`), private `eq_const_headD` (`Encryption/PublicKey/NonMalleability/Simulation/SimIND.lean:88`). getD forms: `GI.getD_ofFn_lt'` (`ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean:61`), `GI.getD_ofFn_lt` (`ZeroKnowledge/GraphIsomorphism/Proofs.lean:818`), `GIZK.getD_ofFn_lt` (`ZeroKnowledge/GraphIsomorphismZK/Closeness.lean:110`), `ColProofs.ofFn_getD_lt` (`ZeroKnowledge/ThreeColoring/ProtocolProofs.lean:391`), Yao's private `getD_ofFn'` (`SecureComputation/Yao.lean:611`). Inline getD chains (`List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos …`): `ZeroKnowledge/ThreeColoring/Simulator.lean:861`, `ZeroKnowledge/ThreeColoring/Language.lean:429` (in private `ofFn_getD_tape`), `ZeroKnowledge/Encoding.lean:359`; the same getD chain also inline outside the cryptography files, in `TCSlib/Complexity/ClassNP/SAT.lean:149`, `TCSlib/Complexity/ClassNP/Tautology.lean:142` and `TCSlib/Complexity/SpaceComplexity/Codec/Word.lean:135` (`getD_encChunk`). **Extended by Gate 32 G32-01 (ruling Seyoon 2026-11-15: extend DL-47 and close), at the #316 head `c18afbe6`:** exact copy of the promoted statement: GGM `Pseudorandom/Functions/Asymptotic/GGM/Run.lean:449–450` (`step_eq`, local `hbit`, replacement `TCSlib.Cryptography.headD_drop_ofFn x ⟨d.i, hi⟩ false`); headD chain `Asymptotic/HardCoreLoops.lean:278–280` (`orbit_eq`); getD/ofFn computations: `SecureComputation/Garbling.lean:193–198` (private `map_range_getD_ofFn`) and `:375–380` (`garbledValues_getD`), `SecureComputation/Yao.lean:626–627` (`yaoBobTables_yaoMsg`), `Encryption/PublicKey/BitwiseCPA.lean:107–113` (private `ofFn_half`), `Encryption/PublicKey/OracleSecurity/PaddedCPA.lean:72–78` (private `ofFn_splitHalf_bit`), `Complexity/CircuitComplexity/CircuitEvalNP.lean:68–69` (`dagCktSatLang_mem_NP`), `PSubsetPPolyGadget.lean:188–190` (`runWith_embedGates_getD`), `PSubsetPPolyProgram.lean:383–387` (`progGates_values`), `PSubsetPPolyTableau.lean:127–132` (`snapEncode_injective`), `UniformTableauCircuit.lean:427–431` (private `tabSrc_eval`), `Complexity/Randomized/RandomWalk.lean:256–259` (`decodeIdx_succ_append`), `Complexity/ClassPSPACE/TQBF.lean:857–859` (private `codecRow_realize`), optional-access form `Cryptography/Encoding/BooleanVector.lean:168–171` (`expandPoly_encode`) and `Hashing/SIS/CollisionOutput.lean:237–243` (`collisionOutputPoly_pairEncode`). | `TCSlib.Cryptography.headD_drop_ofFn` (#316) | Open (deferred) | Ruling Seyoon 2026-11-15: pre-existing (merged before the promotion), recorded as debt and not re-pointed in #316. Re-point NextBit:454 and the index-0 cases onto `headD_drop_ofFn`, and the getD forms onto one shared getD reader, in the deferred cleanup. Yao's `getD_ofFn'` waits for sc-garble and sc-yao to land (`Yao.lean` is shared). **Cleanup plan (G32-01):** add one generic reader `(List.ofFn f).getD i d = f ⟨i, h⟩` (any type) derived from `headD_drop_ofFn` and `List.headD_drop`, then re-point every DL-47 copy onto it or onto `headD_drop_ofFn`, proof only, headers preserved, starting with the exact GGM copy; the `Garbling.lean`/`Yao.lean` copies wait for sc-garble and sc-yao to land. |
| DL-48 | sc-ot fill (delivery review 2026-11-15): F-02 `OT.splitLen` / `splitLen_symm_ofFn` (`SecureComputation/ObliviousTransfer/Simulators.lean`) restate public `coinsEquiv` (inverted) and `ofFn_coinsEquiv` (`Asymptotic/EnsemblesLemmas.lean:141,145`), body as private ElGamal `dlc_splitEquiv`; F-04 `OT.uprob_signedPredictor_false/_true` adapt `exists_pkPredictor` (`pkPredictor` has no public reader); F-07 near-relatives `GI.pairSndD_encodeMsgs` (for `getD_one_eq`), `predict_eq`, and promotion requests `negligible_finset_sum`, `statClose_prod_of_forall`, `exec_five`, `length_runAtL_le`. | `coinsEquiv`, `ofFn_coinsEquiv`; `exists_pkPredictor` | Open (deferred) | Ruling Seyoon 2026-11-15: ledger debt, disclosed (not fixed in the landing: reuse needs a new import and a definition change). Cleanup: replace `splitLen` by `(coinsEquiv h).symm`; publish `pkPredictor_apply` and re-derive the signed predictor from `exists_pkPredictor`; decide the promotion requests. |

## ===== briefs/pass-shelat-ch5-8/fills/sc-ot/final-r1/landing/PROVENANCE.txt =====

sc-ot (PS10 Protocol 160.4 and Proposition 161.5: otProtocol_polyTime, otProtocol_simulators) maintainer delivery review r1, 2026-11-15 UTC
$SP = /tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad. Paths below are relative to this directory.
Method: the common review brief (Updates 1-2) with the corrections for this job. Templates: records
  briefs/pass-shelat-ch5-8/fills/prf-long/final-r1/landing/PROVENANCE.txt and fills/learning/final-r1/landing/PROVENANCE.txt. Tools:
  $SP/review-tools-template/ plus the prf-long review zip's tools (records fills/prf-long/final-r1/review-evidence.zip: the
  G26-N1-fixed runner.py, frozencheck.py and the rest); changes under "tools". Nothing pushed, no PR opened, the records checkout
  only read (git fetch only). No lake build, no cache get. python3 -I throughout. One Lean process at a time, only on
  $SP/dl-oleans; dl-oleans-2 (in use by another job) was never touched.

brief: briefs/pass-shelat-ch5-8/fills/sc-ot/issued-r1/brief.md, SHA-256 b4b5c73a81b7bd5f590f1f53c6c793f898f81cb68889f4495c9b314eefdfd876
  (= dispatch.md's "Brief SHA-256"; logs/brief.md). Issue package SHA256SUMS 7/7 OK (logs/issue-package-check.txt);
  SOURCE-SHA256SUMS 159/159 OK at the issue base 107f1e8c218733eac12d6b9bee6fece441271317 (logs/source-sums-check.txt).
  Issued admissions base-sorries.txt: 31 in 14 modules.
delivery: exchange/pass-shelat-ch5-8 a8972fa063a58ad2ffbfd221d625653d34a53ee8 ("fill sc-ot: final"; checkpoints b55e341b, 13003ddf).
  The three commits touch only inbox/fills/sc-ot/; the one later exchange commit (419c4ceb, sc-compose cp1) does not touch it
  (logs/exchange-commits.txt). git archive into a fresh directory (removed after use); inventory logs/payload-inventory.sha256
  (220 files); cited extracts logs/delivery-extracts/ (patches/ with COMMITS.tsv, both manifests, final-axioms, census diff, lint
  diff, repro, preflight, searches, seals-compare), all byte-equal to the payload (logs/delivery-extract-hashes.txt, 13 EQUAL).
  Worker REPORT: logs/worker-REPORT.md.
integrity (logs/payload-check.txt, tools/mancheck.py, exact path-set equality, leading "./" stripped):
  - top SHA256SUMS 219/219 OK (220 delivered, manifest excluded); evidence/SHA256SUMS 206/206 OK; no missing, no extra.
  - git am of the 3 patches at 107f1e8c with committer name/email/date from patches/COMMITS.tsv (logs/git-am-integrity.log): all
    three worker hashes reproduce (fc7d0366, a643e566, e2c6f1a8f9e16d830e07f9cd3b1158553edb5500), tree 54166c99f2390858551727c58a9fe00014658931,
    but only with the environment's SSH commit signing on (the final commit carries a gpgsig). With commit.gpgsign=false the tree is
    identical and the ids differ (logs/git-am-integrity-unsigned.log). COMMITS.tsv has no signing column (finding F-05).
  - The 7 changed paths (M ObliviousTransfer.lean; A ObliviousTransfer/{Efficiency,Predictor,Shape,Simulators,ViewA,ViewB}.lean)
    are byte-identical to src/, which holds exactly these 7 files (logs/src-equality.txt). No other path changed: scope as briefed.
olean tree: $SP/dl-oleans. tree/snapshot-pre.txt (tools/snapshot.py): 1230 files, 0 empty dirs, SHA-256
  457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f = the required base value (byte-equal to the prf-long review's
  tree/snapshot-post.txt, whose tree-check-post was RESULT OK against the same tree/base-records.jsonl, copied here).
landing: branch land/pass-shelat-sc-ot (local, no upstream), worktree $SP/wt-land-sc-ot (sparse, briefs/ excluded; .lake/packages
  symlinked to /home/user/tcslib/.lake/packages).
  - r1: worker head e2c6f1a8 rebased onto origin/cryptography/pass-shelat-ch2-4 0e5e725dc80c94575ea27b863399ff1119926c96 (rc 0, no
    conflict, the 7 paths equal the worker head; landing/landing.log); LE-doc and LE-reuse committed on top (r1 head fb6075d8).
    Origin delta since the issue base: #307, #311, #312 and records (landing/origin-delta-since-issue-base.txt,
    origin-commits-since-issue-base.txt).
  - r2: #314 (prfAdv_eq_expect promotion) merged during the review (origin 59c2c1fbf8c1bb08f9d191012b7cdd7e15248531; Lean delta
    Pseudorandom/Functions/Defs.lean and EncryptThenTag/Reduction.lean). Rebased onto it (landing/rebase-r2.log): rc 0, range-diff
    5/5 identical, the 7 unit files and all 128 modules of the unit's import closure (order/unit-closure.txt) unchanged r1 -> r2.
    The r2 tree e40614e5f436295d6b1e665c3f0bf8c92a1f51ac equals the earlier merge-tree trial with #314's head.
  - r2 head 93c20338335c6afd10052ed0636d8f4ba26e9171, tree e40614e5f436295d6b1e665c3f0bf8c92a1f51ac (series landing/series-r2/).
  - r3: #315 (prf-long) merged at the end of the review (origin a334ec2e1d87dbde7eac40812286ba60e85c9078; Lean delta the 6 prf-long
    files). Rebased onto it (landing/rebase-r3.log): rc 0, range-diff 5/5 identical, the 7 unit files and the 128-module closure
    unchanged r2 -> r3. Integration build build-r3/ (below).
  - FINAL head f62a25b3eda099c9cf9371900664752e7b89007d, tree 163be55abcd012eac6595af41807ce5cc57ef8f3 on a334ec2e; commits
    landing/commits.txt, series landing/series/0001-0005; author = committer = Claude <noreply@anthropic.com>, SSH-signed by the
    environment default.
      8d429067 sc-ot: checkpoint 1   53969e06 sc-ot: checkpoint 2   b2e817ca sc-ot: final
      7a1fa29b sc-ot landing edit LE-doc   f62a25b3 sc-ot landing edit LE-reuse
    7 files, +2256/-40 vs origin (landing/changed-paths-vs-origin.txt).
LE-doc (386307d1; tools/ledoc_scot.py, 50 exact replacements; landing/le-doc.diff): formulas, in Lean argument order, for the 50 new
  public declarations that statements/docaudit.tsv flagged NO-FORMULA (3 owned file, 18 Efficiency, 6 Predictor, 4 Shape,
  11 Simulators, 1 ViewA, 7 ViewB). The frozen target
  otProtocol_polyTime keeps its base prose. landing/le-doc-doconly.txt (tools/doconly.py): code-identical True in all 7 files, same
  docstring counts, 50 docstrings changed, max width 100: RESULT OK. statements/head-le/docaudit.tsv: 110 OK, 25 LABEL (all state
  the equation), 8 NO-FORMULA = the frozen target's base prose + 7 whose docstring states a Prop formula without a relation symbol
  (`OT.IsOT T H (otProtocol T H)`, `PolyTimeComputable (genRaw T)`, …; the tool only accepts relation symbols).
LE-reuse (93c20338; tools/lereuse_scot.py; landing/le-reuse.diff): OT.pairSndD_nil' (`pairSndD [] = []`) is now
  `BinArith.iterate_pairSndD_nil 1` (public, Complexity/ClassP/BinaryArith/Words.lean:158, already in Efficiency's closure; no new
  import); its docstring's provenance parenthesis names it. Statement unchanged (statements/head-le/decls2-vs-worker.tsv empty).
  Trial build lereuse-trial/ (Efficiency rc 0, 0 warnings) before the commit.
build:
  - build/ (r1 pre-edit head 84742663, order/build-queue.txt from tools/downorder.py vs eff2dcd0): 73 modules = the downstream
    closure, through root TCSlib and audits/pass-shelat/Checks, of the 62 modules changed since eff2dcd0 (55 base delta: #303,
    #306-#309, #311, #312, order/basedelta/; 7 unit, order/unit-vs-origin/: unit downstream = the 7 + YaoReal, the
    SecureComputation facade, root TCSlib). build/summary.txt: 73/73 rc 0, 0 errors in the G26-N1 form, substring "error" 0, 452 s.
    Unit modules 0 warnings. Sorry warnings only in admitted base-delta modules (SeedMajority 2, SpecialEncryptionMulti 1).
    Linter warnings DDH 3, Lamport 7, Rejection 10, Extraction 2 (as in earlier reviews).
  - edit-build/ (r1 head fb6075d8, order/le-build-queue.txt): the 7 unit modules, YaoReal, SecureComputation, TCSlib: 10/10 rc 0,
    0 warnings.
  - build-r2/ (r2 head 93c20338, order/r2-build-queue.txt): #314's 2 modules and their downstream, 96 modules: 96/96 rc 0, 0 errors;
    sorry warnings only in admitted modules (MAC/FromPRF, SpecialEncryptionSecurity, SpecialEncryptionMulti, GarblingSecurity, Yao,
    Learning). Base-delta modules built: the 55 (#303-#312) and #314's 2.
  - build-r3/ (FINAL head f62a25b3, order/r3-build-queue.txt: the downstream of all 69 modules changed since eff2dcd0 at the final
    head = base delta #303-#312, #314, #315 + the unit, from the restored base tree): 139/139 rc 0, 0 errors (G26-N1), substring
    "error" 0, 779 s; sorry warnings only in admitted modules. tree/r3/tree-check-head.txt (order/headfull-order-r3.txt, 1250
    modules; records logs/records-head-r3.jsonl = base records + build-r3): RESULT OK. logs/sorry-census-r3.txt: 31 -> 29, only
    ObliviousTransfer differs. Backups tree/r3/backed-up.txt (88) and new tree/r3/new-oleans.txt (51); restore/r3/restore-log.txt:
    0 hash failures, 88 restored, 51 deleted, restore/r3/snapshot-post.txt byte-equal to tree/snapshot-pre.txt. Lint at the final
    head: lint/lint-landing-head-r3.txt 92/101 and lint-complexity-landing-head-r3.txt 25/391, line sets identical to the tip
    a334ec2e (lint/lint-records-tip-a334ec2e.txt, 92/101; lint-complexity-records-tip-a334ec2e.txt, 25/391; lint/linediff-r3.txt empty).
    Probes, seals and controls were run at r1 (fb6075d8): the 7 files and their closure are byte-identical at the final head.
  - Before building, the base oleans each run overwrote were copied aside (tree/backed-up.txt, 88 files, every hash equal to
    tree/snapshot-pre.txt) and the 50 new ones listed (tree/new-oleans.txt). The tree itself was not copied.
  - tree/tree-check-head.txt (tools/treecheck.py, order/headfull-order.txt = 1249 modules at the r2 head, records
    logs/records-head.jsonl = tree/base-records.jsonl + build + lereuse-trial + edit-build + build-r2): every module rc 0 at the head
    source and the tree's olean, no stray olean, no empty dir: RESULT OK (the 50 head-probe oleans deleted first,
    logs/probe-oleans-deleted-head.txt).
statements (base 107f1e8c; ObliviousTransfer.lean is identical at eff2dcd0, 107f1e8c and both origins):
  - statements/frozen/frozen-check.txt (r1) and statements/head-le/frozen-check.txt (LE head): every base declaration of the owned
    file present, same kind, name and order; header bytes, statement prose and every definition (EnhancedHardCore included, G3-8)
    identical: 0 differences (52 -> 55 declarations). Controls, each exactly 1 difference: statements/frozen/control-header-
    otProtocol_simulators.txt, control-header-otProtocol_hbcSecure.txt, control-body-otSender.txt, control-body-EnhancedHardCore.txt,
    control-prose-otProtocol_polyTime.txt. statements/frozen/topcmds.txt: no base top-level command removed; added: the 6 imports.
  - statements/head-le/touched.tsv: 2 CHANGED (the two targets: proofs and sketches only), 50 UNCHANGED, 3 ADDED (otProtocol_isOT,
    otSimA_isSimA, otSimB_isSimB), 138 in the new files. decls2-vs-base.tsv: 141 ADDED, 0 CHANGED, 0 REMOVED. No private
    declaration, no @[simp].
  - sketchaudit: 13 theorems with >= 15 proof lines, all with a sketch except receiverNext_eq, whose proof is `:= rfl` under a
    19-line statement (tool artifact). Sizes/widths (statements/head-le/sizes-widths.txt): owned file 748 lines, helpers 545, 212,
    216, 435, 186, 545; max width 100; 0 lines over 100.
axioms: probe-sources/head/CensusHead.lean (tools/mkcensus_scot.py) -> probe-runs/CensusHead.log (tools/probe.sh, nothing written
  to the tree): otProtocol_polyTime, otProtocol_simulators and the consumer otProtocol_hbcSecure: [propext, Classical.choice,
  Quot.sound] (the REPORT's claim holds); yaoProtocol_hbcSecure still has sorryAx (Yao.lean's admitted hybrid; base). The helper
  endpoints (polyTime_of_isOT, simulators_of_isOT, exists_negligible_bob, distAdv_realA_idealA_le, uprob_signedPredictor_false/_true,
  negligible_finset_sum) the standard three; pairSndD_nil' no axioms. logs/census-summary.txt (tools/censussum.py): 234 stored
  constants (OT 70, Shape 15, Efficiency 49, Simulators 55, ViewA 7, Predictor 15, ViewB 23 = the worker's counts), axiom union
  {propext, Classical.choice, Quot.sound}, no sorryAx, no simp, instance, reducible or abbrev.
  Base (probe-sources/base/CensusBase.lean, restored tree, base-probe-runs/): logs/census-base-vs-head.tsv (tools/censuscmp.py):
  66 -> 234; removed 0, type-changed 0, attr-changed 0, added 168 (141 named), axioms-changed 3 (the two targets and
  otProtocol_hbcSecure: sorryAx dropped).
admissions: logs/sorry-census.txt (tools/sorrycensus.py, records-head.jsonl): issued 31 in 14 modules -> 29; the only issued module
  differing is SecureComputation/ObliviousTransfer (2 -> 0). Outside the issued order only SeedMajority (#312) and
  SpecialEncryptionMulti (#311) changed since the issue base (base delta); all others unchanged sources.
Rule 10 (seals generated at r1 head fb6075d8; the 7 files and their 128-module closure are byte-identical at the r2 head):
  - Collector probe-sources/head/CollectHead.lean (tools/mkcollect.py) -> probe-runs/. Seals tools/mkseals_ab.py (strict) ->
    seals/{A,B}; tools/mkseals_coe.py (FinDist.instCoeFunForallReal as notation, canonical) -> seals-coe/{A,B}; logs/mkseals-*.log.
    Requests per file 1105-1723 (coe = strict - 1, the instance). 28 head probes seal-runs/ (order/seal-probes-head.txt).
  - logs/seal-head-{seals,seals-coe}-{A,B}.tsv (tools/sealsum.py): all 28 rc 0, 0 errors, install and EOF records present, no
    failing declaration. Base: CollectBase -> base-seals{,-coe}/{A,B}, 4 probes base-seal-runs/ on the restored tree: all pass.
  - logs/seal-table-seals.txt, seal-table-seals-coe.txt (tools/sealtable.py): head A 7/7, B 7/7 in both variants; base 1/1;
    new failing declarations 0; strict = coe. (Seals with PolyExpr.eval excluded = A, sealed = B.)
  - Paired controls tools/mkctl_scot.py (rows PolyExpr.eval, the FinDist CoeFun instance, NUPPT.layout, Strategy.encodeMsgs,
    otFunctionality, OT.mask, OT.simSeg, OT.inA2, OT.bobView, OT.hcBit; negative = rfl unfolding, positive = published reader) on the
    coe records -> controls/ (20 probes, 61 sealed negatives) and strict -> controls-strict/ (20 probes, 71), runs control-runs/
    (order/control-probes.txt). logs/ctlcheck.log: ALL_OK True. logs/ctlcheck-strict.log: every negative fails exactly once and
    every unsealed probe passes, but ctlCoeReader fails in the 10 strict sealed probes (the CoeFun statement elaborates to
    `CoeFun.coe`); attributed in logs/controls-strict-attribution.txt (same effect as learning-r1). The two seal-record directories
    were combined through temporary symlinks for the generator (removed).
  - Explicit-unfold scan (tools/scan1.py, scan2.py; probe-sources/head/ScanKindsHead.lean -> probe-runs/): scan/items-head.json,
    scan/explicit-head.json, logs/scan2-head.log: 742 items, 645 THEOREM, 21 OWNED_DEFINITION, 76 LOCAL_OR_UNRESOLVED, 0 foreign.
    logs/scan-owned-and-local.txt: the owned items are the base file's 18 (pre-existing proofs: otProtocol_outV/outP,
    polyTimeComputable_*, runAt_otSimA/B) and 3 in-file helper definitions (viewDist, simACoins, simBCoins); the unresolved heads
    are local hypotheses and `T.f_perm` field notation.
lint (scripts/campaign_style_lint.py --check8b, #305 version; identical in the records checkout and the worktrees):
  - Cryptography: records tip 0e5e725d 92 FAIL / 101 WARN (lint/lint-records-tip-0e5e725d.txt), new tip 59c2c1fb 92/101
    (lint-records-tip-59c2c1fb.txt, from a git-archive export, removed), r1 head 84742663 92/101, r2 head 93c20338 92/101;
    FAIL/WARN line sets identical (lint/linediff.txt, linediff-r2.txt: only the file count 344 -> 350). Complexity: 25 / 391 at both
    tips and the r2 head, identical line sets.
  - Old (pre-#305) lint for continuity (tools/campaign_style_lint_old_rooted.py): 235/101 -> 241/101; the +6 are the facade class
    "SecureComputation.lean does not import child module ObliviousTransfer.<helper>" (lint/oldlint-linediff.txt), the class #305
    fixed: recorded, not a finding.
content: every changed hunk and all six helpers read. otProtocol_polyTime = polyTime_of_isOT at otProtocol_isOT (raw machines
  ofPolyTimeUniform of senderRaw/receiverRaw, message bound Q₁ + 3(Q₂+Q₃) + 7); otProtocol_simulators = simulators_of_isOT:
  Alice's side ≤ 2δ(n) at every n (statClose_eval_sample, dependent product, distAdv_le_of_statClose); Bob's side through the
  enhanced predicate: the published tdpPredictor around viewDist (which rebuilds Bob's view around the challenge ⟨i, s'⟩, Bob's tape
  containing s'), the signed-predictor identity, hEHC at 16 machines (8 triples × 2 signs) summed into one negligible ε_B; ε = 2|δ| + ε_B.
  EnhancedHardCore enters only through enhancedHardCore_iff (unchanged). The edge cases listed in the brief are covered as the REPORT
  says (b = 0/1 branches, eight triples, empty fillers in exec_five/transcriptWith_isOT, apply_of_decD, the all-true inverter tape,
  SampleClose at every n, D's advice kept in viewDist).
duplication: logs/duplication-review.txt (independent searches). Findings F-01 (fixed by LE-reuse), F-02, F-04, F-06, F-07.
open PRs (logs/open-pr-overlap.txt; PR heads fetched by REST + git fetch): no PR touches a unit file and no PR file is in the unit's
  closure. git merge-tree --write-tree of the landing head (r1 fb6075d8) with each head: #313 94b31964 clean (795289cf; shared
  downstream: root TCSlib only); #314 a24a6313 clean (e40614e5; shared downstream YaoReal, SecureComputation, TCSlib; since merged,
  = r2 base delta, built here); #315 fbd37f44 clean (6dbe7e55; shared downstream YaoReal, SecureComputation, TCSlib). No name in the
  SecureComputation namespace and no short-name coincidence in any PR diff. The merge trees of #313/#315 were not built.
restore (restore/restore-log.txt, tools/restore.sh): 88 backups copied back (hashes checked, 0 failures), 50 new oleans deleted, the
  6 emptied directories pruned (restore/empty-dirs-before-prune.txt); SNAPSHOT EQUAL. Base probes then ran on the restored tree and
  their 6 oleans were deleted (restore/probe-oleans-deleted-base.txt). tree/snapshot-post.txt: 1230 files, SHA-256
  457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f, byte-identical to tree/snapshot-pre.txt; tree/tree-check-post.txt:
  1199 base modules at the eff2dcd0 source and record hashes, snapshot equal: RESULT OK.
tools/: copied from the prf-long-r1 zip (= review-tools-template + its changes). New here: mkcensus_scot.py (endpoints above),
  censussum.py, mkctl_scot.py (rows above), ledoc_scot.py, lereuse_scot.py. runner.py unchanged (G26-N1 fix).
worker environment note (REPORT §1): to pass preflight the worker removed the git worktree of its host's canonizer fill
  (/workspace/canon, branch kept). Environment-only, on the worker's host, not ours (F-08).
open PRs at the end: #315 merged (r3, built); #313 (learning) still open: merge-tree clean and no shared file or closure module
  (above; its shared downstream is root TCSlib only).
cleanup: payload extraction, olean backups (bk-scot, bk-scot3), the integrity worktree (git worktree remove --force) and the reference zip
  extract removed; PlProbe/ removed from the landing worktree, which is clean at f62a25b3. No base worktree was kept.
SHA256SUMS: every file here except itself (paths without "./"). ../sc-ot-r1-evidence.zip holds exactly the manifest's paths plus
  SHA256SUMS.

## ===== briefs/pass-shelat-ch5-8/gates/34-sc-ot/pr-description.md =====

This is the landing PR for the Pass–shelat `sc-ot` fill. It proves `otProtocol_polyTime` and `otProtocol_simulators` in `SecureComputation/ObliviousTransfer.lean` ([PS10, Protocol 160.4, Proposition 161.5]). With them, the consumer `otProtocol_hbcSecure` uses only the standard axioms.

- **Head:** `f62a25b3eda099c9cf9371900664752e7b89007d`.
- **Base:** `cryptography/pass-shelat-ch2-4` at `a334ec2e1d87dbde7eac40812286ba60e85c9078`, which includes #314 and #315.

## What changes
There are 7 Lean files, +2256/−40. The owned file is `ObliviousTransfer.lean`. Six helpers are new in `ObliviousTransfer/`: `Efficiency`, `Predictor`, `Shape`, `Simulators`, `ViewA` and `ViewB`.

**The proof:**
- **Alice's side** is bounded by 2δ(n) at every `n`.
- **Bob's side** uses the published `tdpPredictor` around `viewDist`, plus a signed identity. It applies `hEHC` to 16 machines (8 triples, each with 2 signs) and sums the bounds into one negligible ε_B.

## Commits
- Three Claude worker commits: checkpoint 1, checkpoint 2 and the final.
- **LE-doc** `7a1fa29b`: 50 formula docstrings. Only docstrings change; the code is identical.
- **LE-reuse** `f62a25b3`: `OT.pairSndD_nil'` is now proved from the public `BinArith.iterate_pairSndD_nil`. The change touches only the proof; the statement is unchanged and there is no new import.

## Review
The maintainer's review is in `briefs/pass-shelat-ch5-8/fills/sc-ot/final-r1/review.md`. Its verdict is **ACCEPT WITH LANDING EDITS**.
- **Statements:** the frozen check finds 0 differences, `EnhancedHardCore` included. decls2 gives 141 ADDED, 0 CHANGED, 0 REMOVED.
- **Axioms:** the two targets and `otProtocol_hbcSecure` use only the standard three. So do all 234 stored constants.
- **Build:** 139 modules give rc 0 and 0 errors in both forms. The whole-tree check covers 1250 modules: OK.
- **Rule 10:** the seals pass in A and B, strict and coe. The controls are attributed. The scan finds 0 foreign definitions.
- **Admissions:** 31 → 29.
- **Lint:** 92/101 and 25/391, unchanged.
- **Ledger, DL-48 (Seyoon's ruling, 2026-11-15: ledger debt, disclosed):**
  - F-02: `OT.splitLen` restates the public `coinsEquiv` (inverted) and `ofFn_coinsEquiv`. The deferred cleanup will replace it with `(coinsEquiv h).symm`.
  - F-04: the signed-predictor adaptation. `pkPredictor` has no public reader, and the promotion request is deferred.
  - F-07: near-relatives.

A Codex gate follows. Seyoon merges.

---
_Generated by [Claude Code](https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA)_

## ===== briefs/pass-shelat-ch5-8/gates/34-sc-ot/pr.diff.txt =====

diff --git a/TCSlib/Cryptography/SecureComputation/ObliviousTransfer.lean b/TCSlib/Cryptography/SecureComputation/ObliviousTransfer.lean
index c603fd84b..8e92fe8b0 100644
--- a/TCSlib/Cryptography/SecureComputation/ObliviousTransfer.lean
+++ b/TCSlib/Cryptography/SecureComputation/ObliviousTransfer.lean
@@ -4,13 +4,19 @@ Released under Apache 2.0 license as described in the file LICENSE.
 -/
 import TCSlib.Cryptography.SecureComputation.Defs
 import TCSlib.Cryptography.Asymptotic.Collections
+import TCSlib.Cryptography.SecureComputation.ObliviousTransfer.Shape
+import TCSlib.Cryptography.SecureComputation.ObliviousTransfer.Efficiency
+import TCSlib.Cryptography.SecureComputation.ObliviousTransfer.Simulators
+import TCSlib.Cryptography.SecureComputation.ObliviousTransfer.ViewA
+import TCSlib.Cryptography.SecureComputation.ObliviousTransfer.Predictor
+import TCSlib.Cryptography.SecureComputation.ObliviousTransfer.ViewB
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
 set_option autoImplicit false
 
 /-!
-# Oblivious transfer from trapdoor permutations (statement phase)
+# Oblivious transfer from trapdoor permutations
 
 [PS10, Protocol 160.4]: for a collection of trapdoor permutations `{f_i}` with a hard-core
 predicate `h`,
@@ -70,10 +76,31 @@ cost are passed explicitly, so this module needs only `Asymptotic/Collections`.
 * `SecureComputation.SamplerCanonical`: the sampler outputs canonical encodings.
 * `SecureComputation.otProtocol_outV`, `otProtocol_outP`: correctness: Bob outputs `a_b` and
   Alice outputs `⊥ = []`, on every coin string.
-* `SecureComputation.otProtocol_polyTime` (the parties run in polynomial time, stated; a `sorry`
-  under its sketch).
-* `SecureComputation.otProtocol_simulators` (Prop 161.5 with the explicit simulators, stated; a
-  `sorry` under its sketch), and `otProtocol_hbcSecure` (Prop 161.5, proved from the two).
+* `SecureComputation.otProtocol_isOT`: the protocol has the shape `OT.IsOT` of the helper
+  modules.
+* `SecureComputation.otProtocol_polyTime`: the parties run in polynomial time (proved,
+  `OT.polyTime_of_isOT`).
+* `SecureComputation.otSimA_isSimA`, `otSimB_isSimB`: the simulators have the shapes
+  `OT.IsSimA`, `OT.IsSimB` of the helper modules.
+* `SecureComputation.otProtocol_simulators`: Prop 161.5 with the explicit simulators (proved,
+  `OT.simulators_of_isOT`), and `otProtocol_hbcSecure` (Prop 161.5, proved from the two).
+
+## Contents
+
+The proofs are in the helper modules under `SecureComputation/ObliviousTransfer/`, which state
+them for every protocol of the shape of Protocol 160.4:
+* `ObliviousTransfer/Shape.lean`: the shape `OT.IsOT` (the next-message functions restated) and
+  the five moves of its executions.
+* `ObliviousTransfer/Efficiency.lean`: the parties' machines and the message bound
+  (`OT.polyTime_of_isOT`).
+* `ObliviousTransfer/Simulators.lean`: the simulators' shapes `OT.IsSimA`, `OT.IsSimB` (their raw
+  functions restated), the coin spaces, and the simulated views on assembled tapes.
+* `ObliviousTransfer/ViewA.lean`: Alice's side, the bound `2δ(n)`
+  (`OT.distAdv_realA_idealA_le`).
+* `ObliviousTransfer/Predictor.lean`: the view-building distinguisher `OT.viewDist` behind Bob's
+  side.
+* `ObliviousTransfer/ViewB.lean`: Bob's side through the signed predictor
+  (`OT.exists_negligible_bob`) and the two sides together (`OT.simulators_of_isOT`).
 
 ## References
 
@@ -211,6 +238,19 @@ theorem otProtocol_rounds (H : List Bool → List Bool) : (otProtocol T H).round
 theorem otProtocol_verifierFirst (H : List Bool → List Bool) :
     (otProtocol T H).verifierFirst = false := rfl
 
+/-- **Protocol 160.4 has the shape `OT.IsOT`**: its next-message functions are `OT.senderNext`
+and `OT.receiverNext` (the field equations, with `otMask_eq`, `otKnown_eq` and `otRaw_eq`), Alice
+uses `Gen`'s coins and Bob two sampler blocks, and it has five messages, Alice first:
+`OT.IsOT T H (otProtocol T H)`. -/
+theorem otProtocol_isOT (H : List Bool → List Bool) : OT.IsOT T H (otProtocol T H) := by
+  refine (OT.isOT_iff T H _).2 ⟨?_, ?_, by rw [otProtocol_P, otSender_coins],
+    by rw [otProtocol_V, otReceiver_coins], otProtocol_rounds T H, otProtocol_verifierFirst T H⟩
+  · funext x y r hist
+    rw [otProtocol_P, otSender_next, OT.senderNext_eq, otMask_eq, otMask_eq, OT.mask_eq,
+      OT.mask_eq]
+  · funext x z r hist
+    rw [otProtocol_V, otReceiver_next, OT.receiverNext_eq, otKnown_eq, otRaw_eq]
+
 /-- **The sampler outputs canonical encodings** [PS10, Definition 41.1 (2)]: at every generated
 index, every output of the domain sampler is `encD i x` for some `x ∈ D_i`
 (`Collection.sample_eq_encD`, from the sampler contract and canonical decoding). -/
@@ -586,6 +626,26 @@ theorem runAt_otSimB {H : List Bool → List Bool} (hH : PolyTimeComputable H)
   unfold otSimB
   rw [NUPPT.runAtL_ofPolyTimeUniform, NUPPT.advInput_eq, NUPPT.layout_eq]
 
+/-- **`S_A` has the shape `OT.IsSimA`**: its coins are `coins_Gen + (coins_Sample + coins_Sample)`
+and it computes `OT.simAView` (`otSimA_coins`, `runAt_otSimA`, and the readers of `otSimAFun`,
+`coinSeg`, `simIdx`, `simSample`): `OT.IsSimA T (otSimA T)`. -/
+theorem otSimA_isSimA : OT.IsSimA T (otSimA T) := by
+  refine (OT.isSimA_iff T _).2 ⟨otSimA_coins T, fun n y r => ?_⟩
+  rw [runAt_otSimA]
+  simp only [otSimAFun_eq, simSample_eq, simIdx_eq, coinSeg_eq, OT.simAView_eq, OT.simSampled_eq,
+    OT.simIndex_eq, OT.simSeg_eq]
+
+/-- **`S_B` has the shape `OT.IsSimB`**: its coins are
+`coins_Gen + (coins_Sample + (coins_Sample + 1))` and it computes `OT.simBView` (`otSimB_coins`,
+`runAt_otSimB`, and the readers of `otSimBFun`, `otSimZ`, `otSimZb`, `coinSeg`, `simIdx`,
+`simSample`): `OT.IsSimB T H (otSimB T hH)`. -/
+theorem otSimB_isSimB {H : List Bool → List Bool} (hH : PolyTimeComputable H) :
+    OT.IsSimB T H (otSimB T hH) := by
+  refine (OT.isSimB_iff T H _).2 ⟨otSimB_coins T hH, fun n y r => ?_⟩
+  rw [runAt_otSimB]
+  simp only [otSimBFun_eq, otSimZ_eq, otSimZb_eq, simSample_eq, simIdx_eq, coinSeg_eq,
+    OT.simBView_eq, OT.simZpair_eq, OT.simZbit_eq, OT.simSampled_eq, OT.simIndex_eq, OT.simSeg_eq]
+
 /-! ### Proposition 161.5 -/
 
 section Security
@@ -599,35 +659,44 @@ include henc in
 `S_A = otSimA` and `S_B = otSimB` simulate the two sides of Protocol 160.4 within a negligible
 advantage, uniformly over the inputs.
 
-**Proof sketch.**
+**Proof sketch.** The protocol and the simulators have the shapes `OT.IsOT`, `OT.IsSimA`,
+`OT.IsSimB` (`otProtocol_isOT`, `otSimA_isSimA`, `otSimB_isSimB`), and `OT.simulators_of_isOT`
+proves the statement for every protocol and simulators of these shapes.
 1. *Correctness* (`otProtocol_outV`, `otProtocol_outP`): the real outputs are `a_b` for Bob and
    `[]` for Alice on every coin string, which are the ideal outputs. So each side reduces to its
    view.
-2. *Alice's side* (`S_A`). Alice's real view differs from `S_A`'s only in Bob's message.
-   - Real: `y_b = encD(perm x)` for a sampled `x`, and `y_{1−b}` a sampled element.
-   - Simulated: two sampled elements, canonical by `SamplerCanonical`.
+2. *Alice's side* (`OT.distAdv_realA_idealA_le`). On the coins `(r, s₁, s₂)` (`OT.realCoins`,
+   `OT.simACoins`) Alice's real and simulated views differ only in Bob's message.
+   - Real: `⟨f_i(w₁), w₂⟩` (or `⟨w₂, f_i(w₁)⟩` when `b`), with `w_j = Sample(i; s_j)`.
+   - Simulated: `⟨w₁, w₂⟩`, two sampled elements, canonical by `SamplerCanonical`.
 
    The sampler is within `δ(n)` of uniform on `D_i` (`T.OneWay.sampleClose`), and `perm` is a
-   bijection, so each coordinate is within `δ(n)` of `encD` of a uniform element, independently
-   of `b`. The views are `2δ(n)`-close statistically, so any distinguisher's advantage is at most
-   `2δ(n)` (`distAdv_le_of_statClose`).
-3. *Bob's side* (`S_B`).
+   bijection, so at every generated index `f_i(w) = eval ⟨i, w⟩` is `2δ(n)`-close to a sampled
+   element (`OT.statClose_eval_sample`). The views are `2δ(n)`-close statistically, so any
+   distinguisher's advantage is at most `2δ(n)` (`distAdv_le_of_statClose`).
+3. *Bob's side* (`OT.exists_negligible_bob`).
    - Bob's real view is his tape, `i`, and `(z₁, z₂)` with `z_b = h(x) ⊕ a_b` and
-     `z_{1−b} = h(u) ⊕ a_{1−b}`, where `u = perm⁻¹(x')` for Bob's raw element `x'`.
-   - `S_B` produces the same, but with `z_{1−b}` a fresh coin.
+     `z_{1−b} = h(u) ⊕ a_{1−b}`, where `u = perm⁻¹(x')` for Bob's raw element `x'`
+     (`OT.mask_eval`, `OT.mask_raw`).
+   - `S_B` produces the same, but with `z_{1−b}` a fresh coin. Writing `P(β)` for `D`'s
+     acceptance with `z_{1−b} = β ⊕ a_{1−b}`, the advantage is `|E_r P(B) − E_r P(¬B)| / 2`
+     for `B = h(u)` (`OT.acceptProb_realB`, `OT.acceptProb_idealB`).
    - A distinguisher of the two gives a predictor of `h(u)` from `⟨i, s'⟩`, where `s'` are the
-     sampler coins of `x'`: build the view around the challenge (Bob's tape contains `s'`), run
-     the distinguisher, and flip according to `a_{1−b}` (the signed-predictor identity
-     `exists_pkPredictor` of Algorithm 104.3).
-   - Its advantage is at most `2 ε_EHC(n)` by `hEHC` (enhanced hard-core: the predictor sees the
-     sampler's coins, which the plain hard-core property would not allow).
-   - Building the selected mask also uses `a_b`, so take all eight triples `(b,a₀,a₁)`.
-     The maximum of their eight negligible bounds is negligible and uniform over the inputs;
-     fixing only the choice and unselected sender bit would not specify the complete view.
-4. *Efficiency.* The predictor runs Bob's sampler, the distinguisher, and one XOR: a machine by
-   composition (`NUPPT.exists_comp`).
-
-The source writes out `S_A` only and leaves `S_B` "as an exercise"; step 3 is that exercise. -/
+     sampler coins of `x'`: the machine `OT.viewDist` builds the view around the challenge (Bob's
+     tape contains `s'`) and runs the distinguisher, inside `tdpPredictor` of Algorithm 104.3. It
+     predicts with probability `1/2 ± (P(B) − P(¬B))/2` (the signed-predictor identity
+     `OT.uprob_signedPredictor_false`/`_true`, for uniform coin challenges).
+   - Its advantage is at most `|ε_false(n)| + |ε_true(n)|` by `hEHC` (enhanced hard-core: the
+     predictor sees the sampler's coins, which the plain hard-core property would not allow).
+   - Building the selected mask also uses `a_b`, so the bits `(b, a₀, a₁)` are fixed in the
+     machine: eight triples and two signs. The sum of the sixteen negligible bounds is negligible
+     and uniform over the inputs; fixing only the choice and unselected sender bit would not
+     specify the complete view.
+4. *Efficiency.* The predictor runs Bob's sampler, `H`, one XOR and the distinguisher (with its
+   advice): `NUPPT.ofPolyTime` of a polynomial-time raw function (`OT.viewDist`).
+
+The bound is `ε(n) = 2|δ(n)| + ε_B(n)`. The source writes out `S_A` only and leaves `S_B` "as an
+exercise"; step 3 is that exercise. -/
 theorem otProtocol_simulators (hT : T.OneWay) (hEHC : EnhancedHardCore T h) :
     ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
       ∀ n (x : Fin (otFunctionality.inA.eval n) → Bool)
@@ -635,25 +704,33 @@ theorem otProtocol_simulators (hT : T.OneWay) (hEHC : EnhancedHardCore T h) :
         distAdv (otFunctionality.realA (otProtocol T H) n x y)
             (otFunctionality.idealA (otSimA T) n x y) (D.distinguisherL n) ≤ ε n ∧
           distAdv (otFunctionality.realB (otProtocol T H) n x y)
-            (otFunctionality.idealB (otSimB T hH) n x y) (D.distinguisherL n) ≤ ε n := by
-  sorry
+            (otFunctionality.idealB (otSimB T hH) n x y) (D.distinguisherL n) ≤ ε n :=
+  OT.simulators_of_isOT T H hH henc (otProtocol_isOT T H) (otProtocol_outV T H henc)
+    (otProtocol_outP T H) (otSimA_isSimA T) (otSimB_isSimB T hH) hT
+    ((enhancedHardCore_iff T h).1 hEHC)
 
 include hH in
 /-- **Protocol 160.4 runs in polynomial time** (Definition 155.1's efficiency requirement,
 `Functionality.PolyTime`).
 
-**Proof sketch.**
+**Proof sketch.** The protocol has the shape `OT.IsOT` (`otProtocol_isOT`), and
+`OT.polyTime_of_isOT` proves the requirement for every protocol of that shape.
 1. *Alice.* On the empty history she outputs `Gen`'s index; on one message, the two masks (the
-   trapdoor inverter, `H` and one XOR each, paired); otherwise `[]`. `Gen` and the inverter are
-   uniform machines and `H` is polynomial-time, so a uniform machine computes her next-message
-   function by composition, as for Algorithm 104.3's machines.
-2. *Bob.* His sampler twice, `eval` and a pairing on one message; `[]` on two; `H` and one XOR on
-   his complete history. The same composition gives a uniform machine.
-3. *Messages.* The index has at most `Gen`'s output length (`NUPPT.runLenPoly`). Bob's pair is
-   two sampler outputs or evaluations, polynomial in `n` and the index. The masks have one bit
-   each, paired, and the fillers are empty. Their maximum is a polynomial `B`. -/
-theorem otProtocol_polyTime : otFunctionality.PolyTime (otProtocol T H) := by
-  sorry
+   trapdoor inverter, `H` and one XOR each, paired); otherwise `[]`. The raw machine
+   `OT.senderRaw` reads the case off the encoded history `w`: `w = []`, or `snd w = []`
+   (`polyTimeComputable_isNil`). `Gen` and the inverter are uniform machines and `H` is
+   polynomial-time, so `NUPPT.ofPolyTimeUniform` of it computes her next-message function
+   (`OT.senderRaw_advInput`), with `Gen`'s coins.
+2. *Bob.* His sampler on the two coin blocks, `eval` and a pairing on one message; `[]` on two;
+   `H` and one XOR otherwise (`OT.receiverRaw`, with a third emptiness test). The same
+   construction gives a uniform machine with two sampler blocks of coins.
+3. *Messages.* The transcript is `([y, []], [i, z, []])` (`OT.transcriptWith_isOT`). The index has
+   `|i| ≤ Q₁(n)`, `Gen`'s `NUPPT.runLenPoly`. Bob's pair `y` has two sampler outputs (`≤ Q₂(n)`,
+   the sampler's `runLenPoly` at `Q₁`) or evaluations (`≤ Q₃(n)`, `eval`'s polynomial bound), so
+   `|y| ≤ 3(Q₂ + Q₃) + 2`. The masks have one bit each, so `|z| ≤ 5`, and the fillers are empty.
+   So `B = Q₁ + (3(Q₂ + Q₃) + 2) + 5` (`OT.exists_messages_le`). -/
+theorem otProtocol_polyTime : otFunctionality.PolyTime (otProtocol T H) :=
+  OT.polyTime_of_isOT T hH (otProtocol_isOT T H)
 
 include henc hH in
 /-- **Proposition 161.5** [PS10]: Protocol 160.4 is an honest-but-curious one-out-of-two
diff --git a/TCSlib/Cryptography/SecureComputation/ObliviousTransfer/Efficiency.lean b/TCSlib/Cryptography/SecureComputation/ObliviousTransfer/Efficiency.lean
new file mode 100644
index 000000000..114733f1b
--- /dev/null
+++ b/TCSlib/Cryptography/SecureComputation/ObliviousTransfer/Efficiency.lean
@@ -0,0 +1,545 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.SecureComputation.ObliviousTransfer.Shape
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Oblivious transfer: Protocol 160.4 runs in polynomial time
+
+Both parties of a protocol of the shape of [PS10, Protocol 160.4] (`OT.IsOT`) are efficient
+strategies, and the messages of its honest executions are polynomially bounded: the
+efficiency requirement `Functionality.PolyTime` of Definition 155.1 for `otFunctionality`.
+
+Each next-message function branches on the number of messages received, which the raw machine
+reads off the encoded history `⟨m₁, ⟨m₂, …⟩⟩` by emptiness tests of its iterated second
+components (`polyTimeComputable_isNil`); the branches are compositions of `Gen`, the sampler and
+the inverter (uniform machines, `NUPPT.polyTimeComputable_output`), the evaluator (`eval_poly`),
+`H`, pairing and one XOR. The machines are `NUPPT.ofPolyTimeUniform` of these raw functions.
+
+## Main definitions
+
+* `OT.senderRaw`, `OT.receiverRaw`: the raw functions of the two parties' machines.
+
+## Main results
+
+* `OT.polyTimeComputable_senderRaw`, `OT.polyTimeComputable_receiverRaw`: they are
+  polynomial-time.
+* `OT.senderRaw_advInput`, `OT.receiverRaw_advInput`: they compute the next messages.
+* `OT.length_runAtL_le`: the output-length bound of a machine on an untyped tape.
+* `OT.polyTime_of_isOT`: [PS10, Protocol 160.4] runs in polynomial time.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §6.2, Definition 155.1 and Protocol 160.4 (book pp. 155, 160).
+-/
+
+namespace TCSlib.Cryptography.SecureComputation.OT
+
+open Complexity Turing TCSlib.Cryptography
+
+variable (T : TrapdoorCollection) (H : List Bool → List Bool)
+
+/-! ### Reading the encoded history -/
+
+/-- The first message of a history is the first projection of its encoding:
+`hist.headD [] = fst (encodeMsgs hist)` (`Strategy.pairFstD_encodeMsgs`). -/
+theorem headD_eq_pairFstD (hist : List (List Bool)) :
+    hist.headD [] = pairFstD (Strategy.encodeMsgs hist) :=
+  (Strategy.pairFstD_encodeMsgs hist).symm
+
+/-- The second projection of the empty word is empty, `pairSndD [] = []`
+(`BinArith.iterate_pairSndD_nil` at `1`). -/
+theorem pairSndD_nil' : pairSndD ([] : List Bool) = [] :=
+  BinArith.iterate_pairSndD_nil 1
+
+/-- The second message of a history is read off its encoding:
+`hist.getD 1 [] = fst (snd (encodeMsgs hist))`. -/
+theorem getD_one_eq (hist : List (List Bool)) :
+    hist.getD 1 [] = pairFstD (pairSndD (Strategy.encodeMsgs hist)) := by
+  rcases hist with _ | ⟨m, _ | ⟨m', rest⟩⟩
+  · rw [Strategy.encodeMsgs_nil, pairSndD_nil', pairFstD_nil]
+    rfl
+  · rw [Strategy.encodeMsgs_cons, Strategy.encodeMsgs_nil, pairSndD_pairEncode, pairFstD_nil]
+    rfl
+  · rw [Strategy.encodeMsgs_cons, Strategy.encodeMsgs_cons, pairSndD_pairEncode,
+      pairFstD_pairEncode]
+    rfl
+
+/-- A uniform machine's activation is its output on the layout with empty advice:
+`A.runAtL n y r = A.output (layout 1^n y [] r)` (`NUPPT.runAtL_eq_output_layout`). -/
+theorem runAtL_eq_layout {A : NUPPT} (hA : A.Uniform) (n : ℕ) (y r : List Bool) :
+    A.runAtL n y r = A.output (NUPPT.layout (List.replicate n true) y [] r) := by
+  rw [NUPPT.runAtL_eq_output_layout, NUPPT.Uniform.advice_eq hA]
+
+/-- The raw layout of a strategy activation: `⟨⟨advInput n a, []⟩, r⟩ = layout 1^n a [] r`. -/
+theorem advInput_layout (n : ℕ) (a r : List Bool) :
+    pairEncode (pairEncode (NUPPT.advInput n a) []) r =
+      NUPPT.layout (List.replicate n true) a [] r := by
+  rw [NUPPT.advInput_eq, NUPPT.layout_eq]
+
+/-! ### Alice's machine -/
+
+/-- `Gen`'s output on the raw layout `z`: `Gen(inParam z; inCoins z)` with empty argument,
+`genRaw T z = Gen.output (layout (inParam z) [] [] (inCoins z))`. -/
+def genRaw (z : List Bool) : List Bool :=
+  T.gen.output (NUPPT.layout (NUPPT.inParam z) [] [] (NUPPT.inCoins z))
+
+/-- The defining equation of `genRaw`: `genRaw T z = Gen.output (layout (inParam z) [] []
+(inCoins z))`. -/
+theorem genRaw_eq (z : List Bool) :
+    genRaw T z = T.gen.output (NUPPT.layout (NUPPT.inParam z) [] [] (NUPPT.inCoins z)) := rfl
+
+/-- `genRaw` is polynomial-time: `PolyTimeComputable (genRaw T)`. -/
+theorem polyTimeComputable_genRaw : PolyTimeComputable (genRaw T) :=
+  (T.gen.polyTimeComputable_output.comp' (NUPPT.polyTimeComputable_layout
+    NUPPT.polyTimeComputable_inParam (polyTimeComputable_const [])
+    (polyTimeComputable_const []) NUPPT.polyTimeComputable_inCoins)).congr
+    fun z => (genRaw_eq T z).symm
+
+/-- Alice's mask on the raw layout `z`, for the element `yj` and the bit word `bt`:
+`zipWith xor (H ⟨i, Inv(⟨t, yj⟩; 1^{inv})⟩) bt` with `⟨i, t⟩ = genRaw T z`. -/
+def maskRaw (z yj bt : List Bool) : List Bool :=
+  List.zipWith xor (H (pairEncode (pairFstD (genRaw T z))
+    (T.inv.output (NUPPT.layout (NUPPT.inParam z) (pairEncode (pairSndD (genRaw T z)) yj) []
+      (List.replicate (T.inv.coins.eval (NUPPT.inParam z).length) true))))) bt
+
+/-- The defining equation of `maskRaw`: `maskRaw T H z yj bt =
+zipWith xor (H ⟨i, Inv(inParam z, ⟨t, yj⟩; 1^{inv})⟩) bt` with `⟨i, t⟩ = genRaw T z`. -/
+theorem maskRaw_eq (z yj bt : List Bool) :
+    maskRaw T H z yj bt =
+      List.zipWith xor (H (pairEncode (pairFstD (genRaw T z))
+        (T.inv.output (NUPPT.layout (NUPPT.inParam z) (pairEncode (pairSndD (genRaw T z)) yj) []
+          (List.replicate (T.inv.coins.eval (NUPPT.inParam z).length) true))))) bt := rfl
+
+/-- The raw mask is polynomial-time in `z` for polynomial-time `yj` and `bt`:
+`PolyTimeComputable (fun z => maskRaw T H z (Y z) (B z))` for polynomial-time `H`, `Y`, `B`.
+
+**Proof sketch.** Pair the index (first projection of `genRaw`) with the inverter's output on
+the layout of `1^n`, `⟨t, yj⟩` and the all-`true` tape (`polyTimeComputable_unaryPoly`), apply
+`H`, pair with `bt` and XOR (`polyTimeComputable_pairXor`). -/
+theorem polyTimeComputable_maskRaw {H : List Bool → List Bool} (hH : PolyTimeComputable H)
+    {Y B : List Bool → List Bool} (hY : PolyTimeComputable Y) (hB : PolyTimeComputable B) :
+    PolyTimeComputable fun z => maskRaw T H z (Y z) (B z) := by
+  have hG := polyTimeComputable_genRaw T
+  have hinv := T.inv.polyTimeComputable_output.comp' (NUPPT.polyTimeComputable_layout
+    NUPPT.polyTimeComputable_inParam ((polyTimeComputable_pairSndD.comp' hG).pairEncode hY)
+    (polyTimeComputable_const [])
+    ((polyTimeComputable_unaryPoly T.inv.coins).comp' NUPPT.polyTimeComputable_inParam))
+  have h := polyTimeComputable_pairXor.comp'
+    ((hH.comp' ((polyTimeComputable_pairFstD.comp' hG).pairEncode hinv)).pairEncode hB)
+  refine h.congr fun z => ?_
+  rw [maskRaw_eq, pairFstD_pairEncode, pairSndD_pairEncode]
+
+/-- **Alice's raw function** on `z = layout 1^{|x|} ⟨⟨x, y⟩, w⟩ [] r` with `w` the encoded
+history: `fst (genRaw z)` if `w = []`; the two masks if `snd w = []`; else `[]`. -/
+def senderRaw (z : List Bool) : List Bool :=
+  if decide (pairSndD (NUPPT.inArg z) = []) then pairFstD (genRaw T z)
+  else if decide (pairSndD (pairSndD (NUPPT.inArg z)) = []) then
+    pairEncode
+      (maskRaw T H z (pairFstD (pairFstD (pairSndD (NUPPT.inArg z))))
+        [(pairSndD (pairFstD (NUPPT.inArg z))).headD false])
+      (maskRaw T H z (pairSndD (pairFstD (pairSndD (NUPPT.inArg z))))
+        [((pairSndD (pairFstD (NUPPT.inArg z))).drop 1).headD false])
+  else []
+
+/-- The defining equation of `senderRaw`: with `w = snd (inArg z)`, `fst (genRaw T z)` if
+`w = []`, the two raw masks if `snd w = []`, else `[]`. -/
+theorem senderRaw_eq (z : List Bool) :
+    senderRaw T H z =
+      if decide (pairSndD (NUPPT.inArg z) = []) then pairFstD (genRaw T z)
+      else if decide (pairSndD (pairSndD (NUPPT.inArg z)) = []) then
+        pairEncode
+          (maskRaw T H z (pairFstD (pairFstD (pairSndD (NUPPT.inArg z))))
+            [(pairSndD (pairFstD (NUPPT.inArg z))).headD false])
+          (maskRaw T H z (pairSndD (pairFstD (pairSndD (NUPPT.inArg z))))
+            [((pairSndD (pairFstD (NUPPT.inArg z))).drop 1).headD false])
+      else [] := rfl
+
+/-- **Alice's raw function is polynomial-time** (`polyTimeComputable_ite` on the two emptiness
+tests `polyTimeComputable_isNil`, `polyTimeComputable_maskRaw`, `polyTimeComputable_headD`,
+`polyTimeComputable_tail`): `PolyTimeComputable (senderRaw T H)` for polynomial-time `H`. -/
+theorem polyTimeComputable_senderRaw {H : List Bool → List Bool} (hH : PolyTimeComputable H) :
+    PolyTimeComputable (senderRaw T H) := by
+  have hw := polyTimeComputable_pairSndD.comp' NUPPT.polyTimeComputable_inArg
+  have hy := polyTimeComputable_pairSndD.comp'
+    (polyTimeComputable_pairFstD.comp' NUPPT.polyTimeComputable_inArg)
+  have hm := polyTimeComputable_pairFstD.comp' hw
+  have h₁ := polyTimeComputable_maskRaw T hH (polyTimeComputable_pairFstD.comp' hm)
+    (polyTimeComputable_headD.comp' hy)
+  have h₂ := polyTimeComputable_maskRaw T hH (polyTimeComputable_pairSndD.comp' hm)
+    (polyTimeComputable_headD.comp' (polyTimeComputable_tail.comp' hy))
+  have h := polyTimeComputable_ite (polyTimeComputable_isNil.comp' hw)
+    (polyTimeComputable_pairFstD.comp' (polyTimeComputable_genRaw T))
+    (polyTimeComputable_ite (polyTimeComputable_isNil.comp' (polyTimeComputable_pairSndD.comp' hw))
+      (h₁.pairEncode h₂) (polyTimeComputable_const []))
+  exact h.congr fun z => (senderRaw_eq T H z).symm
+
+/-- `Gen`'s output on the layout of an activation at `1^{|x|}` is `Gen(1^{|x|}; r)`:
+`genRaw T (layout 1^n a [] r) = Gen.runAtL n [] r`. -/
+theorem genRaw_layout (n : ℕ) (a r : List Bool) :
+    genRaw T (NUPPT.layout (List.replicate n true) a [] r) = T.gen.runAtL n [] r := by
+  rw [genRaw_eq, NUPPT.inParam_layout, NUPPT.inCoins_layout, runAtL_eq_layout T.gen_uniform]
+
+/-- The raw mask on the layout of an activation is Alice's mask:
+`maskRaw T H (layout 1^n a [] r) yj [c] = mask T H n i t yj c` with `⟨i, t⟩ = Gen(1^n; r)`. -/
+theorem maskRaw_layout (n : ℕ) (a r yj : List Bool) (c : Bool) :
+    maskRaw T H (NUPPT.layout (List.replicate n true) a [] r) yj [c] =
+      mask T H n (pairFstD (T.gen.runAtL n [] r)) (pairSndD (T.gen.runAtL n [] r)) yj c := by
+  rw [maskRaw_eq, genRaw_layout, NUPPT.inParam_layout, List.length_replicate, mask_eq,
+    runAtL_eq_layout T.inv_uniform]
+
+/-- `y.getD 0 false` is the head bit: `y.getD 0 false = y.headD false`. -/
+theorem getD_zero_eq (y : List Bool) : y.getD 0 false = y.headD false := by
+  cases y <;> rfl
+
+/-- `y.getD 1 false` is the head bit of `y.drop 1`:
+`y.getD 1 false = (y.drop 1).headD false`. -/
+theorem getD_one_eq' (y : List Bool) : y.getD 1 false = (y.drop 1).headD false := by
+  rcases y with _ | ⟨a, _ | ⟨b, t⟩⟩ <;> rfl
+
+/-- **Alice's raw function computes her next message**: on the raw input of the activation
+`⟨⟨advInput |x| ⟨⟨x, y⟩, encodeMsgs hist⟩, []⟩, r⟩` it returns `senderNext T H x y r hist`:
+`senderRaw T H ⟨⟨advInput |x| ⟨⟨x, y⟩, encodeMsgs hist⟩, []⟩, r⟩ =
+senderNext T H x y r hist`.
+
+**Proof sketch.** Cases on the history: `[]` (the encoding is empty), `[m]` (its second
+projection is empty), and two or more messages (neither is empty); `genRaw_layout`,
+`maskRaw_layout` and `getD_zero_eq`, `getD_one_eq'` identify the branches with
+`senderNext_nil`, `senderNext_single`, `senderNext_eq`. -/
+theorem senderRaw_advInput (x y r : List Bool) (hist : List (List Bool)) :
+    senderRaw T H (pairEncode (pairEncode (NUPPT.advInput x.length
+      (pairEncode (pairEncode x y) (Strategy.encodeMsgs hist))) []) r) =
+      senderNext T H x y r hist := by
+  rw [advInput_layout, senderRaw_eq, NUPPT.inArg_layout, genRaw_layout, pairSndD_pairEncode,
+    pairFstD_pairEncode, pairSndD_pairEncode]
+  rcases hist with _ | ⟨m, _ | ⟨m', rest⟩⟩
+  · rw [Strategy.encodeMsgs_nil, if_pos (by simp), senderNext_nil]
+  · rw [Strategy.encodeMsgs_cons, Strategy.encodeMsgs_nil, if_neg (by simp [pairEncode_ne_nil]),
+      pairSndD_pairEncode, if_pos (by simp), pairFstD_pairEncode, senderNext_single,
+      maskRaw_layout, maskRaw_layout, getD_zero_eq, getD_one_eq']
+  · rw [Strategy.encodeMsgs_cons, Strategy.encodeMsgs_cons, if_neg (by simp [pairEncode_ne_nil]),
+      pairSndD_pairEncode, if_neg (by simp [pairEncode_ne_nil]), senderNext_eq,
+      if_neg (by simp), if_neg (by simp)]
+
+/-! ### Bob's machine -/
+
+/-- Bob's sampled element on the raw layout `z`, at the index `i = fst w` of the encoded
+history `w = snd (inArg z)`: the sampler on the first `coins_Sample(n)` coins. -/
+def knownRaw (z : List Bool) : List Bool :=
+  T.sample.output (NUPPT.layout (NUPPT.inParam z) (pairFstD (pairSndD (NUPPT.inArg z))) []
+    ((NUPPT.inCoins z).take (T.sample.coins.eval (NUPPT.inParam z).length)))
+
+/-- The defining equation of `knownRaw`: `knownRaw T z = Sample(inParam z, fst w;
+(inCoins z).take coins_Sample(n))` with `w = snd (inArg z)`. -/
+theorem knownRaw_eq (z : List Bool) :
+    knownRaw T z =
+      T.sample.output (NUPPT.layout (NUPPT.inParam z) (pairFstD (pairSndD (NUPPT.inArg z))) []
+        ((NUPPT.inCoins z).take (T.sample.coins.eval (NUPPT.inParam z).length))) := rfl
+
+/-- Bob's raw element on the raw layout `z`: the sampler on the coins after the first block,
+`rawRaw T z = Sample(inParam z, fst w; (inCoins z).drop coins_Sample(n))` with
+`w = snd (inArg z)`. -/
+def rawRaw (z : List Bool) : List Bool :=
+  T.sample.output (NUPPT.layout (NUPPT.inParam z) (pairFstD (pairSndD (NUPPT.inArg z))) []
+    ((NUPPT.inCoins z).drop (T.sample.coins.eval (NUPPT.inParam z).length)))
+
+/-- The defining equation of `rawRaw`: `rawRaw T z = Sample(inParam z, fst w;
+(inCoins z).drop coins_Sample(n))` with `w = snd (inArg z)`. -/
+theorem rawRaw_eq (z : List Bool) :
+    rawRaw T z =
+      T.sample.output (NUPPT.layout (NUPPT.inParam z) (pairFstD (pairSndD (NUPPT.inArg z))) []
+        ((NUPPT.inCoins z).drop (T.sample.coins.eval (NUPPT.inParam z).length))) := rfl
+
+/-- Bob's output on the raw layout `z`: `H ⟨i, w⟩ ⊕ z_b` with `z_b` the second or first
+projection of the second message, by the choice bit `b`:
+`outRaw T H z = zipWith xor (H ⟨fst w, knownRaw T z⟩) z_b` with `w = snd (inArg z)`. -/
+def outRaw (z : List Bool) : List Bool :=
+  List.zipWith xor (H (pairEncode (pairFstD (pairSndD (NUPPT.inArg z))) (knownRaw T z)))
+    (if (pairSndD (pairFstD (NUPPT.inArg z))).headD false then
+      pairSndD (pairFstD (pairSndD (pairSndD (NUPPT.inArg z))))
+    else pairFstD (pairFstD (pairSndD (pairSndD (NUPPT.inArg z)))))
+
+/-- The defining equation of `outRaw`: `outRaw T H z = zipWith xor (H ⟨fst w, knownRaw T z⟩) z_b`
+with `z_b` the second or first projection of `fst (snd w)` by the choice bit. -/
+theorem outRaw_eq (z : List Bool) :
+    outRaw T H z =
+      List.zipWith xor (H (pairEncode (pairFstD (pairSndD (NUPPT.inArg z))) (knownRaw T z)))
+        (if (pairSndD (pairFstD (NUPPT.inArg z))).headD false then
+          pairSndD (pairFstD (pairSndD (pairSndD (NUPPT.inArg z))))
+        else pairFstD (pairFstD (pairSndD (pairSndD (NUPPT.inArg z))))) := rfl
+
+/-- Bob's ordered pair on the raw layout `z`: `⟨w', eval ⟨i, w⟩⟩` if `b`, else
+`⟨eval ⟨i, w⟩, w'⟩`, with `w = knownRaw T z`, `w' = rawRaw T z`, `i = fst (snd (inArg z))` and
+`b = (snd (fst (inArg z))).headD false`. -/
+def pairRaw (z : List Bool) : List Bool :=
+  if (pairSndD (pairFstD (NUPPT.inArg z))).headD false then
+    pairEncode (rawRaw T z)
+      (T.eval (pairEncode (pairFstD (pairSndD (NUPPT.inArg z))) (knownRaw T z)))
+  else
+    pairEncode (T.eval (pairEncode (pairFstD (pairSndD (NUPPT.inArg z))) (knownRaw T z)))
+      (rawRaw T z)
+
+/-- The defining equation of `pairRaw`: `⟨rawRaw, eval ⟨fst w, knownRaw⟩⟩` if `b`, else
+`⟨eval ⟨fst w, knownRaw⟩, rawRaw⟩`, i.e. `pairRaw T z = if b then ⟨rawRaw T z, eval ⟨fst w,
+knownRaw T z⟩⟩ else ⟨eval ⟨fst w, knownRaw T z⟩, rawRaw T z⟩` with `w = snd (inArg z)`. -/
+theorem pairRaw_eq (z : List Bool) :
+    pairRaw T z =
+      if (pairSndD (pairFstD (NUPPT.inArg z))).headD false then
+        pairEncode (rawRaw T z)
+          (T.eval (pairEncode (pairFstD (pairSndD (NUPPT.inArg z))) (knownRaw T z)))
+      else
+        pairEncode (T.eval (pairEncode (pairFstD (pairSndD (NUPPT.inArg z))) (knownRaw T z)))
+          (rawRaw T z) := rfl
+
+/-- **Bob's raw function** on `z = layout 1^{|x|} ⟨⟨x, z_B⟩, w⟩ [] r`: `outRaw` if `w = []`, the
+pair if `snd w = []`, `[]` if `snd (snd w) = []`, else `outRaw`. -/
+def receiverRaw (z : List Bool) : List Bool :=
+  if decide (pairSndD (NUPPT.inArg z) = []) then outRaw T H z
+  else if decide (pairSndD (pairSndD (NUPPT.inArg z)) = []) then pairRaw T z
+  else if decide (pairSndD (pairSndD (pairSndD (NUPPT.inArg z))) = []) then []
+  else outRaw T H z
+
+/-- The defining equation of `receiverRaw`: with `w = snd (inArg z)`, `outRaw` if `w = []`,
+`pairRaw` if `snd w = []`, `[]` if `snd (snd w) = []`, else `outRaw`. -/
+theorem receiverRaw_eq (z : List Bool) :
+    receiverRaw T H z =
+      if decide (pairSndD (NUPPT.inArg z) = []) then outRaw T H z
+      else if decide (pairSndD (pairSndD (NUPPT.inArg z)) = []) then pairRaw T z
+      else if decide (pairSndD (pairSndD (pairSndD (NUPPT.inArg z))) = []) then []
+      else outRaw T H z := rfl
+
+/-- **Bob's raw function is polynomial-time**: the sampler on the two coin blocks
+(`polyTimeComputable_pairTakePoly`, `polyTimeComputable_pairDropPoly`), `eval_poly`, `H`, XOR,
+pairing, and branches on the choice bit and three emptiness tests (`polyTimeComputable_ite`):
+`PolyTimeComputable (receiverRaw T H)` for polynomial-time `H`.
+
+**Proof sketch.** Build `knownRaw`, `rawRaw`, `outRaw`, `pairRaw` from the projections and the
+machines' output functions, then nest three `polyTimeComputable_ite`. -/
+theorem polyTimeComputable_receiverRaw {H : List Bool → List Bool} (hH : PolyTimeComputable H) :
+    PolyTimeComputable (receiverRaw T H) := by
+  have hU := NUPPT.polyTimeComputable_inParam
+  have hw := polyTimeComputable_pairSndD.comp' NUPPT.polyTimeComputable_inArg
+  have hi := polyTimeComputable_pairFstD.comp' hw
+  have hb := polyTimeComputable_headD.comp' (polyTimeComputable_pairSndD.comp'
+    (polyTimeComputable_pairFstD.comp' NUPPT.polyTimeComputable_inArg))
+  have htake := (polyTimeComputable_pairTakePoly T.sample.coins).comp'
+    (hU.pairEncode NUPPT.polyTimeComputable_inCoins)
+  have hdrop := (polyTimeComputable_pairDropPoly T.sample.coins).comp'
+    (hU.pairEncode NUPPT.polyTimeComputable_inCoins)
+  have hk : PolyTimeComputable (knownRaw T) :=
+    (T.sample.polyTimeComputable_output.comp' (NUPPT.polyTimeComputable_layout hU hi
+      (polyTimeComputable_const []) htake)).congr fun z => by
+        rw [knownRaw_eq, pairFstD_pairEncode, pairSndD_pairEncode]
+  have hr : PolyTimeComputable (rawRaw T) :=
+    (T.sample.polyTimeComputable_output.comp' (NUPPT.polyTimeComputable_layout hU hi
+      (polyTimeComputable_const []) hdrop)).congr fun z => by
+        rw [rawRaw_eq, pairFstD_pairEncode, pairSndD_pairEncode]
+  have he := T.eval_poly.comp' (hi.pairEncode hk)
+  have hm := polyTimeComputable_pairFstD.comp' (polyTimeComputable_pairSndD.comp' hw)
+  have ho : PolyTimeComputable (outRaw T H) :=
+    (polyTimeComputable_pairXor.comp' ((hH.comp' (hi.pairEncode hk)).pairEncode
+      (polyTimeComputable_ite hb (polyTimeComputable_pairSndD.comp' hm)
+        (polyTimeComputable_pairFstD.comp' hm)))).congr fun z => by
+      rw [outRaw_eq, pairFstD_pairEncode, pairSndD_pairEncode]
+  have hp : PolyTimeComputable (pairRaw T) :=
+    (polyTimeComputable_ite hb (hr.pairEncode he) (he.pairEncode hr)).congr
+      fun z => (pairRaw_eq T z).symm
+  have h := polyTimeComputable_ite (polyTimeComputable_isNil.comp' hw) ho
+    (polyTimeComputable_ite (polyTimeComputable_isNil.comp' (polyTimeComputable_pairSndD.comp' hw))
+      hp (polyTimeComputable_ite (polyTimeComputable_isNil.comp'
+        (polyTimeComputable_pairSndD.comp' (polyTimeComputable_pairSndD.comp' hw)))
+        (polyTimeComputable_const []) ho))
+  exact h.congr fun z => (receiverRaw_eq T H z).symm
+
+/-- On the layout of an activation, `knownRaw` is the sampler on the first coin block:
+`knownRaw T (layout 1^n ⟨u, encodeMsgs hist⟩ [] r) =
+Sample.runAtL n (hist.headD []) (r.take coins_Sample(n))`. -/
+theorem knownRaw_layout (n : ℕ) (u r : List Bool) (hist : List (List Bool)) :
+    knownRaw T
+        (NUPPT.layout (List.replicate n true) (pairEncode u (Strategy.encodeMsgs hist)) [] r) =
+      T.sample.runAtL n (hist.headD []) (r.take (T.sample.coins.eval n)) := by
+  rw [knownRaw_eq, NUPPT.inParam_layout, NUPPT.inArg_layout, NUPPT.inCoins_layout,
+    pairSndD_pairEncode, ← headD_eq_pairFstD, List.length_replicate,
+    runAtL_eq_layout T.sample_uniform]
+
+/-- On the layout of an activation, `rawRaw` is the sampler on the second coin block:
+`rawRaw T (layout 1^n ⟨u, encodeMsgs hist⟩ [] r) =
+Sample.runAtL n (hist.headD []) (r.drop coins_Sample(n))`. -/
+theorem rawRaw_layout (n : ℕ) (u r : List Bool) (hist : List (List Bool)) :
+    rawRaw T
+        (NUPPT.layout (List.replicate n true) (pairEncode u (Strategy.encodeMsgs hist)) [] r) =
+      T.sample.runAtL n (hist.headD []) (r.drop (T.sample.coins.eval n)) := by
+  rw [rawRaw_eq, NUPPT.inParam_layout, NUPPT.inArg_layout, NUPPT.inCoins_layout,
+    pairSndD_pairEncode, ← headD_eq_pairFstD, List.length_replicate,
+    runAtL_eq_layout T.sample_uniform]
+
+/-- **Bob's raw function computes his next message**: on the raw input of the activation
+`⟨⟨advInput |x| ⟨⟨x, z⟩, encodeMsgs hist⟩, []⟩, r⟩` it returns `receiverNext T H x z r hist`:
+`receiverRaw T H ⟨⟨advInput |x| ⟨⟨x, z⟩, encodeMsgs hist⟩, []⟩, r⟩ =
+receiverNext T H x z r hist`.
+
+**Proof sketch.** `knownRaw_layout`, `rawRaw_layout`, `headD_eq_pairFstD` and `getD_one_eq`
+identify `outRaw` with the last branch of `receiverNext` on every history and `pairRaw` with the
+first. Then cases on the history: `[]`, `[i]`, two messages, and three or more, by the emptiness
+of the iterated second projections of the encoding. -/
+theorem receiverRaw_advInput (x z r : List Bool) (hist : List (List Bool)) :
+    receiverRaw T H (pairEncode (pairEncode (NUPPT.advInput x.length
+      (pairEncode (pairEncode x z) (Strategy.encodeMsgs hist))) []) r) =
+      receiverNext T H x z r hist := by
+  rw [advInput_layout, receiverRaw_eq]
+  have hout : outRaw T H (NUPPT.layout (List.replicate x.length true)
+      (pairEncode (pairEncode x z) (Strategy.encodeMsgs hist)) [] r) =
+      List.zipWith xor (H (pairEncode (hist.headD [])
+        (T.sample.runAtL x.length (hist.headD []) (r.take (T.sample.coins.eval x.length)))))
+        (if z.headD false then pairSndD (hist.getD 1 []) else pairFstD (hist.getD 1 [])) := by
+    rw [outRaw_eq, knownRaw_layout, NUPPT.inArg_layout, pairSndD_pairEncode, pairFstD_pairEncode,
+      pairSndD_pairEncode, ← headD_eq_pairFstD, getD_one_eq]
+  have hpair : pairRaw T (NUPPT.layout (List.replicate x.length true)
+      (pairEncode (pairEncode x z) (Strategy.encodeMsgs hist)) [] r) =
+      receiverNext T H x z r [hist.headD []] := by
+    rw [pairRaw_eq, knownRaw_layout, rawRaw_layout, NUPPT.inArg_layout, pairSndD_pairEncode,
+      pairFstD_pairEncode, pairSndD_pairEncode, ← headD_eq_pairFstD, receiverNext_single]
+  rw [hout, hpair, NUPPT.inArg_layout, pairSndD_pairEncode]
+  rcases hist with _ | ⟨m, _ | ⟨m', _ | ⟨m'', rest⟩⟩⟩
+  · rw [Strategy.encodeMsgs_nil, if_pos (by simp), receiverNext_eq,
+      if_neg (show ¬([] : List (List Bool)).length = 1 by simp),
+      if_neg (show ¬([] : List (List Bool)).length = 2 by simp)]
+  · rw [Strategy.encodeMsgs_cons, Strategy.encodeMsgs_nil, if_neg (by simp [pairEncode_ne_nil]),
+      pairSndD_pairEncode, if_pos (by simp), List.headD_cons]
+  · rw [Strategy.encodeMsgs_cons, Strategy.encodeMsgs_cons, Strategy.encodeMsgs_nil,
+      if_neg (by simp [pairEncode_ne_nil]), pairSndD_pairEncode,
+      if_neg (by simp [pairEncode_ne_nil]), pairSndD_pairEncode, if_pos (by simp),
+      receiverNext_pair]
+  · rw [Strategy.encodeMsgs_cons, Strategy.encodeMsgs_cons, Strategy.encodeMsgs_cons,
+      if_neg (by simp [pairEncode_ne_nil]), pairSndD_pairEncode,
+      if_neg (by simp [pairEncode_ne_nil]), pairSndD_pairEncode,
+      if_neg (by simp [pairEncode_ne_nil]), receiverNext_eq,
+      if_neg (show ¬(m :: m' :: m'' :: rest).length = 1 by simp),
+      if_neg (show ¬(m :: m' :: m'' :: rest).length = 2 by simp)]
+
+/-! ### Message lengths -/
+
+/-- **The output-length bound on an untyped tape of the right length**: `|A(1^n, y; r)| ≤
+runLenPoly A Y (n)` whenever `|y| ≤ Y(n)` and `|r| = coins_A(n)` (the list form of
+`NUPPT.length_runAt_le_runLenPoly`, through `List.ofFn_get`). -/
+theorem length_runAtL_le (A : NUPPT) {Y : PolyExpr} (n : ℕ) {y r : List Bool}
+    (hy : y.length ≤ Y.eval n) (hr : r.length = A.coins.eval n) :
+    (A.runAtL n y r).length ≤ (A.runLenPoly Y).eval n := by
+  have hr' : r.length = A.coinLen n := hr.trans (A.coinLen_eq n).symm
+  have h := A.length_runAt_le_runLenPoly n hy (fun j => r.get (Fin.cast hr'.symm j))
+  rwa [NUPPT.runAt_eq, ← List.ofFn_congr hr' r.get, List.ofFn_get] at h
+
+/-- A mask has at most one bit: `|zipWith xor w [a]| ≤ 1`. -/
+theorem length_zipWith_singleton_le (w : List Bool) (a : Bool) :
+    (List.zipWith xor w [a]).length ≤ 1 := by
+  rw [List.length_zipWith, List.length_singleton]
+  exact Nat.min_le_right _ _
+
+/-- Alice's mask has at most one bit: `|mask T H n i t yj a| ≤ 1`. -/
+theorem length_mask_le (n : ℕ) (i t yj : List Bool) (a : Bool) :
+    (mask T H n i t yj a).length ≤ 1 := by
+  rw [mask_eq]
+  exact length_zipWith_singleton_le _ a
+
+/-- **The messages of Protocol 160.4 are polynomially bounded**: for a protocol of its shape there
+is a polynomial `B` with `|msg| ≤ B(n)` for every message of every honest execution on `1^n`.
+
+**Proof sketch.** The transcript is `([y, []], [i, z, []])` (`transcriptWith_isOT`). The index
+has `|i| ≤ Q₁(n)` (`Gen`'s `runLenPoly`); the two samples have `≤ Q₂(n)` (the sampler's
+`runLenPoly` at `Q₁`, the coin blocks having `coins_Sample(n)` bits); the evaluation has
+`≤ Q₃(n)` (the evaluator's polynomial bound at `2Q₁ + 2 + Q₂`); so `|y| ≤ 3(Q₂ + Q₃) + 2`.
+The masks have one bit each, so `|z| ≤ 5`. Take `B = Q₁ + (3(Q₂ + Q₃) + 2) + 5`. -/
+theorem exists_messages_le {π : Protocol} (hπ : IsOT T H π) :
+    ∃ B : PolyExpr, ∀ n (x : Fin (otFunctionality.inA.eval n) → Bool)
+      (y : Fin (otFunctionality.inB.eval n) → Bool) (r : π.ExecCoins π.P (List.replicate n true)),
+      ∀ msg ∈ (π.transcript (List.replicate n true) (List.ofFn x) (List.ofFn y) r).1 ++
+          (π.transcript (List.replicate n true) (List.ofFn x) (List.ofFn y) r).2,
+        msg.length ≤ B.eval n := by
+  obtain ⟨-, -, hPc, hVc, -, -⟩ := (isOT_iff T H π).1 hπ
+  obtain ⟨C, c, hC⟩ := T.eval_poly.output_length_le
+  set Q₁ : PolyExpr := T.gen.runLenPoly (.const 0) with hQ₁
+  set Q₂ : PolyExpr := T.sample.runLenPoly Q₁ with hQ₂
+  set Q₃ : PolyExpr := (PolyExpr.normal C c).subst
+    (.add (.add (.mul (.const 2) Q₁) (.const 2)) Q₂) with hQ₃
+  refine ⟨.add Q₁ (.add (.add (.mul (.const 3) (.add Q₂ Q₃)) (.const 2)) (.const 5)),
+    fun n x y r msg hmsg => ?_⟩
+  suffices key : ∀ (w a b : List Bool) (r : π.ExecCoins π.P w),
+      ∀ msg ∈ (π.transcript w a b r).1 ++ (π.transcript w a b r).2,
+        msg.length ≤ (PolyExpr.add Q₁ (.add (.add (.mul (.const 3) (.add Q₂ Q₃)) (.const 2))
+          (.const 5))).eval w.length by
+    have h := key _ _ _ r msg hmsg
+    rwa [List.length_replicate] at h
+  intro w a b r msg hmsg
+  rw [Protocol.transcript_eq_transcriptWith, transcriptWith_isOT T H hπ] at hmsg
+  -- the coin lengths
+  have hrA : (List.ofFn r.1).length = T.gen.coins.eval w.length := by
+    rw [List.length_ofFn, Strategy.coinLen_eq, hPc]
+  have hrB : (List.ofFn r.2).length =
+      T.sample.coins.eval w.length + T.sample.coins.eval w.length := by
+    rw [List.length_ofFn, Strategy.coinLen_eq, hVc, PolyExpr.eval_add]
+  -- the index
+  set i := pairFstD (T.gen.runAtL w.length [] (List.ofFn r.1)) with hi_def
+  have hi : i.length ≤ Q₁.eval w.length :=
+    (length_pairFstD_le _).trans (length_runAtL_le T.gen w.length (by simp) hrA)
+  -- the two samples
+  have hk : (T.sample.runAtL w.length i
+      ((List.ofFn r.2).take (T.sample.coins.eval w.length))).length ≤ Q₂.eval w.length :=
+    length_runAtL_le T.sample w.length hi (by rw [List.length_take, hrB]; omega)
+  have hd : (T.sample.runAtL w.length i
+      ((List.ofFn r.2).drop (T.sample.coins.eval w.length))).length ≤ Q₂.eval w.length :=
+    length_runAtL_le T.sample w.length hi (by rw [List.length_drop, hrB]; omega)
+  -- the evaluation
+  have he : (T.eval (pairEncode i (T.sample.runAtL w.length i
+      ((List.ofFn r.2).take (T.sample.coins.eval w.length))))).length ≤ Q₃.eval w.length := by
+    refine (hC _).trans ?_
+    rw [hQ₃, PolyExpr.eval_subst, PolyExpr.eval_normal]
+    apply Nat.mul_le_mul_left
+    apply Nat.pow_le_pow_left
+    simp only [length_pairEncode, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
+    omega
+  have hB : ∀ k, k ≤ Q₁.eval w.length + (3 * (Q₂.eval w.length + Q₃.eval w.length) + 2) + 5 →
+      k ≤ (PolyExpr.add Q₁ (.add (.add (.mul (.const 3) (.add Q₂ Q₃)) (.const 2))
+        (.const 5))).eval w.length := by
+    intro k hk'
+    simpa only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const] using hk'
+  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
+    or_false] at hmsg
+  refine hB _ ?_
+  rcases hmsg with h | h | h | h | h <;> subst h
+  · -- Bob's pair
+    rw [receiverNext_single]
+    split_ifs <;> simp only [length_pairEncode] <;> omega
+  · simp
+  · omega
+  · -- Alice's masks
+    rw [senderNext_single, length_pairEncode]
+    refine le_trans (Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul_left 2
+      (length_mask_le T H _ _ _ _ _)) 2) (length_mask_le T H _ _ _ _ _)) ?_
+    omega
+  · simp
+
+/-- **Protocol 160.4 runs in polynomial time** [PS10, Definition 155.1, efficiency]: for a
+protocol of its shape with a polynomial-time `H`, both parties are efficient strategies (the
+machines `ofPolyTimeUniform` of `senderRaw` and `receiverRaw`) and the honest messages are
+polynomially bounded (`exists_messages_le`): `IsOT T H π → otFunctionality.PolyTime π`. -/
+theorem polyTime_of_isOT {H : List Bool → List Bool} (hH : PolyTimeComputable H) {π : Protocol}
+    (hπ : IsOT T H π) : otFunctionality.PolyTime π := by
+  obtain ⟨hP, hV, hPc, hVc, -, -⟩ := (isOT_iff T H π).1 hπ
+  refine (Functionality.polyTime_iff _ _).2 ⟨?_, ?_, exists_messages_le T H hπ⟩
+  · refine (Strategy.efficient_iff _).2 ⟨NUPPT.ofPolyTimeUniform (polyTimeComputable_senderRaw T hH)
+      T.gen.coins, NUPPT.ofPolyTimeUniform_uniform _ _,
+      hPc.trans (NUPPT.coins_ofPolyTimeUniform _ _).symm, fun x z r hist => ?_⟩
+    rw [Strategy.ofNUPPT_next, NUPPT.runAtL_ofPolyTimeUniform, senderRaw_advInput, hP]
+  · refine (Strategy.efficient_iff _).2 ⟨NUPPT.ofPolyTimeUniform
+      (polyTimeComputable_receiverRaw T hH) (.add T.sample.coins T.sample.coins),
+      NUPPT.ofPolyTimeUniform_uniform _ _,
+      hVc.trans (NUPPT.coins_ofPolyTimeUniform _ _).symm, fun x z r hist => ?_⟩
+    rw [Strategy.ofNUPPT_next, NUPPT.runAtL_ofPolyTimeUniform, receiverRaw_advInput, hV]
+
+end TCSlib.Cryptography.SecureComputation.OT
diff --git a/TCSlib/Cryptography/SecureComputation/ObliviousTransfer/Predictor.lean b/TCSlib/Cryptography/SecureComputation/ObliviousTransfer/Predictor.lean
new file mode 100644
index 000000000..6e1fc93ab
--- /dev/null
+++ b/TCSlib/Cryptography/SecureComputation/ObliviousTransfer/Predictor.lean
@@ -0,0 +1,212 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.SecureComputation.ObliviousTransfer.Simulators
+import TCSlib.Cryptography.Encryption.PublicKey.Trapdoor
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Oblivious transfer: the view-building distinguisher behind Bob's side
+
+On Bob's side of [PS10, Proposition 161.5] a distinguisher `D` of Bob's real and simulated views
+becomes a predictor of the enhanced hard-core bit `h(f_i⁻¹(y_{1−b}))` from `⟨i, s'⟩`, `s'` the
+sampler coins of `y_{1−b}`. The predictor is the machine `tdpPredictor D' flip` of Algorithm
+104.3's proof, run on the distinguisher `D'` built here: on `⟨i, ⟨s', [β]⟩⟩` with its own coins
+`s₁ ++ ρ`, `D'` assembles Bob's view with tape `s₁ ++ s'`, index `i`, the selected mask
+`z_b = H ⟨i, Sample(i; s₁)⟩ ⊕ a_b` and the unselected mask `z_{1−b} = β ⊕ a_{1−b}` (`OT.bobView`),
+and runs `D` on it with the coins `ρ`. The choice and sender bits `(b, a₀, a₁)` are fixed in the
+machine.
+
+## Main definitions
+
+* `OT.bobView`: Bob's view (paired with Alice's empty output) with a given unselected mask bit.
+* `OT.viewRaw`, `OT.viewDistRaw`: the raw functions of the view and of `D'`.
+* `OT.viewDist`: the machine `D'`; `OT.viewDistCoins`: its coins as `Coins_Sample × Coins_D`.
+
+## Main results
+
+* `OT.polyTimeComputable_bobView`, `OT.polyTimeComputable_viewDistRaw`: they are
+  polynomial-time.
+* `OT.distinguisherL_viewDist`: `D'` accepts `⟨i, ⟨s', [β]⟩⟩` on `(s₁, ρ)` iff `D` accepts the
+  view `bobView … β` on `ρ`.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §6.2.4, Proposition 161.5, and Theorem 104.4 (the predictor), book pp. 104, 161–162.
+-/
+
+namespace TCSlib.Cryptography.SecureComputation.OT
+
+open Complexity Turing TCSlib.Cryptography
+
+variable (T : TrapdoorCollection) (H : List Bool → List Bool)
+
+/-- **Bob's view with the unselected mask bit `β`** [PS10, Proposition 161.5], paired with
+Alice's empty output: `⟨⟨⟨u, [b]⟩, ⟨s, [i, Z, []]⟩⟩, []⟩` with
+`Z = ⟨[β ⊕ a₀], H ⟨i, w⟩ ⊕ [a₁]⟩` if `b`, else `⟨H ⟨i, w⟩ ⊕ [a₀], [β ⊕ a₁]⟩`. -/
+def bobView (u : List Bool) (b a₀ a₁ : Bool) (i s w : List Bool) (β : Bool) : List Bool :=
+  pairEncode (pairEncode (pairEncode u [b]) (pairEncode s (pairEncode i (pairEncode
+    (if b then pairEncode [xor β a₀] (List.zipWith xor (H (pairEncode i w)) [a₁])
+      else pairEncode (List.zipWith xor (H (pairEncode i w)) [a₀]) [xor β a₁])
+    (pairEncode [] []))))) []
+
+/-- The defining equation of `bobView`: `bobView H u b a₀ a₁ i s w β =
+⟨⟨⟨u, [b]⟩, ⟨s, [i, Z, []]⟩⟩, []⟩` with `Z` ordered by `b`. -/
+theorem bobView_eq (u : List Bool) (b a₀ a₁ : Bool) (i s w : List Bool) (β : Bool) :
+    bobView H u b a₀ a₁ i s w β =
+      pairEncode (pairEncode (pairEncode u [b]) (pairEncode s (pairEncode i (pairEncode
+        (if b then pairEncode [xor β a₀] (List.zipWith xor (H (pairEncode i w)) [a₁])
+          else pairEncode (List.zipWith xor (H (pairEncode i w)) [a₀]) [xor β a₁])
+        (pairEncode [] []))))) [] := rfl
+
+/-- **Bob's view is polynomial-time** in its string arguments, for polynomial-time `H`
+(pairing, one XOR of bits `BinArith.polyTimeComputable_xor`, `polyTimeComputable_pairXor`, a
+branch on the fixed bit `b`): `PolyTimeComputable (fun z =>
+bobView H (U z) b a₀ a₁ (I z) (S z) (W z) ((B z).headD false))`. -/
+theorem polyTimeComputable_bobView {H : List Bool → List Bool} (hH : PolyTimeComputable H)
+    (b a₀ a₁ : Bool) {U I S W B : List Bool → List Bool} (hU : PolyTimeComputable U)
+    (hI : PolyTimeComputable I) (hS : PolyTimeComputable S) (hW : PolyTimeComputable W)
+    (hB : PolyTimeComputable B) :
+    PolyTimeComputable fun z => bobView H (U z) b a₀ a₁ (I z) (S z) (W z) ((B z).headD false) := by
+  have hβ := polyTimeComputable_headD.comp' hB
+  have hx : ∀ a : Bool, PolyTimeComputable fun z => [xor ((B z).headD false) a] := fun a =>
+    BinArith.polyTimeComputable_xor hβ (polyTimeComputable_const [a])
+  have hm : ∀ a : Bool, PolyTimeComputable fun z =>
+      List.zipWith xor (H (pairEncode (I z) (W z))) [a] := fun a =>
+    (polyTimeComputable_pairXor.comp' ((hH.comp' (hI.pairEncode hW)).pairEncode
+      (polyTimeComputable_const [a]))).congr fun z => by
+        rw [pairFstD_pairEncode, pairSndD_pairEncode]
+  have hZ := polyTimeComputable_ite (p := fun _ => b) (polyTimeComputable_const [b])
+    ((hx a₀).pairEncode (hm a₁)) ((hm a₀).pairEncode (hx a₁))
+  have h := ((hU.pairEncode (polyTimeComputable_const [b])).pairEncode (hS.pairEncode
+    (hI.pairEncode (hZ.pairEncode (polyTimeComputable_const (pairEncode [] [])))))).pairEncode
+    (polyTimeComputable_const [])
+  exact h.congr fun z => (bobView_eq H _ _ _ _ _ _ _ _).symm
+
+/-- The view built by `D'` on the raw layout `z = layout u ⟨i, ⟨s', [β]⟩⟩ α (s₁ ++ ρ)`:
+`bobView u b a₀ a₁ i (s₁ ++ s') (Sample(u, i; s₁)) β`, with `s₁` the first `coins_Sample(|u|)`
+coins. -/
+def viewRaw (b a₀ a₁ : Bool) (z : List Bool) : List Bool :=
+  bobView H (NUPPT.inParam z) b a₀ a₁ (pairFstD (NUPPT.inArg z))
+    ((NUPPT.inCoins z).take (T.sample.coins.eval (NUPPT.inParam z).length) ++
+      pairFstD (pairSndD (NUPPT.inArg z)))
+    (T.sample.output (NUPPT.layout (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)) []
+      ((NUPPT.inCoins z).take (T.sample.coins.eval (NUPPT.inParam z).length))))
+    ((pairSndD (pairSndD (NUPPT.inArg z))).headD false)
+
+/-- The defining equation of `viewRaw`: `viewRaw T H b a₀ a₁ z = bobView H u b a₀ a₁ i
+(s₁ ++ s') (Sample(u, i; s₁)) β` read off the layout `z`. -/
+theorem viewRaw_eq (b a₀ a₁ : Bool) (z : List Bool) :
+    viewRaw T H b a₀ a₁ z =
+      bobView H (NUPPT.inParam z) b a₀ a₁ (pairFstD (NUPPT.inArg z))
+        ((NUPPT.inCoins z).take (T.sample.coins.eval (NUPPT.inParam z).length) ++
+          pairFstD (pairSndD (NUPPT.inArg z)))
+        (T.sample.output (NUPPT.layout (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)) []
+          ((NUPPT.inCoins z).take (T.sample.coins.eval (NUPPT.inParam z).length))))
+        ((pairSndD (pairSndD (NUPPT.inArg z))).headD false) := rfl
+
+/-- The raw function of `D'`: `D` on the layout of `1^n`, the built view, the advice and the
+coins after the first `coins_Sample(n)`: `viewDistRaw T H D b a₀ a₁ z = D.output (layout
+(inParam z) (viewRaw T H b a₀ a₁ z) (inAdvice z) ((inCoins z).drop coins_Sample(n)))`. -/
+def viewDistRaw (D : NUPPT) (b a₀ a₁ : Bool) (z : List Bool) : List Bool :=
+  D.output (NUPPT.layout (NUPPT.inParam z) (viewRaw T H b a₀ a₁ z) (NUPPT.inAdvice z)
+    ((NUPPT.inCoins z).drop (T.sample.coins.eval (NUPPT.inParam z).length)))
+
+/-- The defining equation of `viewDistRaw`: `viewDistRaw T H D b a₀ a₁ z = D.output (layout
+(inParam z) (viewRaw T H b a₀ a₁ z) (inAdvice z) ((inCoins z).drop coins_Sample(n)))`. -/
+theorem viewDistRaw_eq (D : NUPPT) (b a₀ a₁ : Bool) (z : List Bool) :
+    viewDistRaw T H D b a₀ a₁ z =
+      D.output (NUPPT.layout (NUPPT.inParam z) (viewRaw T H b a₀ a₁ z) (NUPPT.inAdvice z)
+        ((NUPPT.inCoins z).drop (T.sample.coins.eval (NUPPT.inParam z).length))) := rfl
+
+/-- **The raw function of `D'` is polynomial-time** (`polyTimeComputable_bobView`, the sampler's
+and `D`'s output functions, `polyTimeComputable_pairTakePoly`, `polyTimeComputable_pairDropPoly`,
+`PolyTimeComputable.append`): `PolyTimeComputable (viewDistRaw T H D b a₀ a₁)`.
+
+**Proof sketch.** Build the projections, the first coin block and the remaining coins, the sampled
+element on the first block, the tape `s₁ ++ s'` and the built view (`polyTimeComputable_bobView`),
+then `D`'s output on the layout; match the definition by the pairing readers. -/
+theorem polyTimeComputable_viewDistRaw {H : List Bool → List Bool} (hH : PolyTimeComputable H)
+    (D : NUPPT) (b a₀ a₁ : Bool) : PolyTimeComputable (viewDistRaw T H D b a₀ a₁) := by
+  have hU := NUPPT.polyTimeComputable_inParam
+  have hi := polyTimeComputable_pairFstD.comp' NUPPT.polyTimeComputable_inArg
+  have htake := (polyTimeComputable_pairTakePoly T.sample.coins).comp'
+    (hU.pairEncode NUPPT.polyTimeComputable_inCoins)
+  have hdrop := (polyTimeComputable_pairDropPoly T.sample.coins).comp'
+    (hU.pairEncode NUPPT.polyTimeComputable_inCoins)
+  have hs := htake.append (polyTimeComputable_pairFstD.comp'
+    (polyTimeComputable_pairSndD.comp' NUPPT.polyTimeComputable_inArg))
+  have hw := T.sample.polyTimeComputable_output.comp' (NUPPT.polyTimeComputable_layout hU hi
+    (polyTimeComputable_const []) htake)
+  have hβ := polyTimeComputable_pairSndD.comp'
+    (polyTimeComputable_pairSndD.comp' NUPPT.polyTimeComputable_inArg)
+  have hv := polyTimeComputable_bobView hH b a₀ a₁ hU hi hs hw hβ
+  have h := D.polyTimeComputable_output.comp' (NUPPT.polyTimeComputable_layout hU hv
+    NUPPT.polyTimeComputable_inAdvice hdrop)
+  refine h.congr fun z => ?_
+  simp only [viewDistRaw_eq, viewRaw_eq, pairFstD_pairEncode, pairSndD_pairEncode]
+
+/-- **The view-building distinguisher `D'`** for the fixed bits `(b, a₀, a₁)`: `D`'s advice and
+coins `coins_Sample + coins_D`: `viewDist T hH D b a₀ a₁ = NUPPT.ofPolyTime
+(polyTimeComputable_viewDistRaw T hH D b a₀ a₁) (.add T.sample.coins D.coins) D.adv D.advice
+D.advice_length`. -/
+noncomputable def viewDist {H : List Bool → List Bool} (hH : PolyTimeComputable H) (D : NUPPT)
+    (b a₀ a₁ : Bool) : NUPPT :=
+  NUPPT.ofPolyTime (polyTimeComputable_viewDistRaw T hH D b a₀ a₁) (.add T.sample.coins D.coins)
+    D.adv D.advice D.advice_length
+
+/-- The coin polynomial of `D'` is `coins_Sample + coins_D`:
+`(viewDist T hH D b a₀ a₁).coins = .add T.sample.coins D.coins`. -/
+theorem viewDist_coins {H : List Bool → List Bool} (hH : PolyTimeComputable H) (D : NUPPT)
+    (b a₀ a₁ : Bool) : (viewDist T hH D b a₀ a₁).coins = .add T.sample.coins D.coins :=
+  NUPPT.coins_ofPolyTime _ _ _ _ _
+
+/-- **`D'`'s coins** as a sampler block and `D`'s coins:
+`(viewDist T hH D b a₀ a₁).Coins n ≃ T.sample.Coins n × D.Coins n` (`splitLen`). -/
+noncomputable def viewDistCoins {H : List Bool → List Bool} (hH : PolyTimeComputable H) (D : NUPPT)
+    (b a₀ a₁ : Bool) (n : ℕ) : (viewDist T hH D b a₀ a₁).Coins n ≃ T.sample.Coins n × D.Coins n :=
+  splitLen (by rw [NUPPT.coinLen_eq, viewDist_coins, PolyExpr.eval_add, NUPPT.coinLen_eq,
+    NUPPT.coinLen_eq])
+
+/-- The tape of `D'` from blocks: `ofFn ((viewDistCoins …).symm (s₁, ρ)) = ofFn s₁ ++ ofFn ρ`. -/
+theorem viewDistCoins_symm_ofFn {H : List Bool → List Bool} (hH : PolyTimeComputable H)
+    (D : NUPPT) (b a₀ a₁ : Bool) (n : ℕ) (p : T.sample.Coins n × D.Coins n) :
+    List.ofFn ((viewDistCoins T hH D b a₀ a₁ n).symm p) = List.ofFn p.1 ++ List.ofFn p.2 :=
+  splitLen_symm_ofFn _ p
+
+/-- **`D'` runs `D` on the built view**: on `⟨i, ⟨s', [β]⟩⟩` with coins `s₁ ++ ρ`,
+`D'(1^n, ⟨i, ⟨s', [β]⟩⟩; s₁ ++ ρ) = D(1^n, bobView (1^n) b a₀ a₁ i (s₁ ++ s') w β; ρ)` with
+`w = Sample(1^n, i; s₁)`. -/
+theorem runAtL_viewDist {H : List Bool → List Bool} (hH : PolyTimeComputable H) (D : NUPPT)
+    (b a₀ a₁ : Bool) (n : ℕ) (i s' : List Bool) (β : Bool) (s₁ : T.sample.Coins n)
+    (ρ : List Bool) :
+    (viewDist T hH D b a₀ a₁).runAtL n (pairEncode i (pairEncode s' [β])) (List.ofFn s₁ ++ ρ) =
+      D.runAtL n (bobView H (List.replicate n true) b a₀ a₁ i (List.ofFn s₁ ++ s')
+        (T.sample.runAt n i s₁) β) ρ := by
+  have hl : (List.ofFn s₁).length = T.sample.coins.eval (List.replicate n true).length := by
+    rw [length_ofFn_coins, List.length_replicate]
+  unfold viewDist
+  rw [NUPPT.runAtL_ofPolyTime, NUPPT.advInput_eq, ← NUPPT.layout_eq, viewDistRaw_eq, viewRaw_eq,
+    NUPPT.inParam_layout, NUPPT.inArg_layout, NUPPT.inAdvice_layout, NUPPT.inCoins_layout,
+    List.take_left' hl, List.drop_left' hl, pairFstD_pairEncode, pairSndD_pairEncode,
+    pairFstD_pairEncode, pairSndD_pairEncode, List.headD_cons, NUPPT.runAtL_eq_output_layout,
+    NUPPT.runAt_eq, NUPPT.runAtL_eq_output_layout, NUPPT.Uniform.advice_eq T.sample_uniform]
+
+/-- **`D'` accepts iff `D` accepts the built view**: `D'.distinguisherL n ⟨i, ⟨s', [β]⟩⟩ (s₁, ρ) =
+D.distinguisherL n (bobView (1^n) b a₀ a₁ i (s₁ ++ s') (Sample(1^n, i; s₁)) β) ρ`. -/
+theorem distinguisherL_viewDist {H : List Bool → List Bool} (hH : PolyTimeComputable H)
+    (D : NUPPT) (b a₀ a₁ : Bool) (n : ℕ) (i s' : List Bool) (β : Bool)
+    (p : T.sample.Coins n × D.Coins n) :
+    (viewDist T hH D b a₀ a₁).distinguisherL n (pairEncode i (pairEncode s' [β]))
+        ((viewDistCoins T hH D b a₀ a₁ n).symm p) =
+      D.distinguisherL n (bobView H (List.replicate n true) b a₀ a₁ i (List.ofFn p.1 ++ s')
+        (T.sample.runAt n i p.1) β) p.2 := by
+  rw [NUPPT.distinguisherL_eq, NUPPT.distinguisherL_eq, NUPPT.runAt_eq, NUPPT.runAt_eq,
+    viewDistCoins_symm_ofFn, runAtL_viewDist]
+
+end TCSlib.Cryptography.SecureComputation.OT
diff --git a/TCSlib/Cryptography/SecureComputation/ObliviousTransfer/Shape.lean b/TCSlib/Cryptography/SecureComputation/ObliviousTransfer/Shape.lean
new file mode 100644
index 000000000..528b6ff59
--- /dev/null
+++ b/TCSlib/Cryptography/SecureComputation/ObliviousTransfer/Shape.lean
@@ -0,0 +1,216 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.SecureComputation.Defs
+import TCSlib.Cryptography.Asymptotic.Collections
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Oblivious transfer: the shape of Protocol 160.4 and its five moves
+
+The proofs of [PS10, Proposition 161.5] are carried out for every protocol of the shape of
+Protocol 160.4, stated here by its next-message functions. This module cannot import
+`SecureComputation/ObliviousTransfer.lean`, which imports it, so the shape restates the bodies of
+`otSender` and `otReceiver` (with `otMask`, `otKnown` and `otRaw` expanded); the owned file proves
+that `otProtocol` has this shape from its published field equations.
+
+## Main definitions
+
+* `OT.mask`, `OT.senderNext`, `OT.receiverNext`: Alice's mask and the two next-message
+  functions of [PS10, Protocol 160.4].
+* `OT.IsOT`: a protocol of the shape of Protocol 160.4.
+
+## Main results
+
+* `OT.senderNext_nil`, `OT.senderNext_single`, `OT.senderNext_pair`, `OT.receiverNext_single`,
+  `OT.receiverNext_pair`: the messages on histories of length `0`, `1` and `2`.
+* `OT.exec_five`: the five moves of a prover-first execution.
+* `OT.transcriptWith_isOT`: the transcript of a protocol of the shape of Protocol 160.4.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §6.2.4, Protocol 160.4 (book p. 160).
+-/
+
+namespace TCSlib.Cryptography.SecureComputation.OT
+
+open Complexity Turing TCSlib.Cryptography
+
+variable (T : TrapdoorCollection) (H : List Bool → List Bool)
+
+/-- **Alice's mask** [PS10, Protocol 160.4]: `z_j = h(f_i⁻¹(y_j)) ⊕ a_j`, computed as
+`zipWith xor (H ⟨i, Inv(1^n, ⟨t, y_j⟩; 1^{inv(n)})⟩) [a]` (the body of `otMask`). -/
+def mask (n : ℕ) (i t yj : List Bool) (a : Bool) : List Bool :=
+  List.zipWith xor (H (pairEncode i (T.inv.runAtL n (pairEncode t yj)
+    (List.replicate (T.inv.coins.eval n) true)))) [a]
+
+/-- The defining equation of `mask`: `mask T H n i t yj a =
+zipWith xor (H ⟨i, Inv(1^n, ⟨t, yj⟩; 1^{inv(n)})⟩) [a]`. -/
+theorem mask_eq (n : ℕ) (i t yj : List Bool) (a : Bool) :
+    mask T H n i t yj a =
+      List.zipWith xor (H (pairEncode i (T.inv.runAtL n (pairEncode t yj)
+        (List.replicate (T.inv.coins.eval n) true)))) [a] := rfl
+
+/-- **Alice's next message** [PS10, Protocol 160.4] (the body of `otSender`): on the empty
+history `i = fst Gen(1^{|x|}; r)`; on one message `m`, `⟨mask (fst m) y₀, mask (snd m) y₁⟩` with
+`⟨i, t⟩ = Gen(1^{|x|}; r)`; otherwise `[]`. -/
+def senderNext (x y r : List Bool) (hist : List (List Bool)) : List Bool :=
+  if hist.length = 0 then pairFstD (T.gen.runAtL x.length [] r)
+  else if hist.length = 1 then
+    pairEncode
+      (mask T H x.length (pairFstD (T.gen.runAtL x.length [] r))
+        (pairSndD (T.gen.runAtL x.length [] r)) (pairFstD (hist.headD [])) (y.getD 0 false))
+      (mask T H x.length (pairFstD (T.gen.runAtL x.length [] r))
+        (pairSndD (T.gen.runAtL x.length [] r)) (pairSndD (hist.headD [])) (y.getD 1 false))
+  else []
+
+/-- The defining equation of `senderNext`: `[]` ↦ `i`, `[m]` ↦ the two masks, else `[]`, i.e.
+`senderNext T H x y r hist = if |hist| = 0 then i else if |hist| = 1 then
+⟨mask (fst m) y₀, mask (snd m) y₁⟩ else []` with `i = fst Gen(1^{|x|}; r)` and
+`m = hist.headD []`. -/
+theorem senderNext_eq (x y r : List Bool) (hist : List (List Bool)) :
+    senderNext T H x y r hist =
+      if hist.length = 0 then pairFstD (T.gen.runAtL x.length [] r)
+      else if hist.length = 1 then
+        pairEncode
+          (mask T H x.length (pairFstD (T.gen.runAtL x.length [] r))
+            (pairSndD (T.gen.runAtL x.length [] r)) (pairFstD (hist.headD [])) (y.getD 0 false))
+          (mask T H x.length (pairFstD (T.gen.runAtL x.length [] r))
+            (pairSndD (T.gen.runAtL x.length [] r)) (pairSndD (hist.headD [])) (y.getD 1 false))
+      else [] := rfl
+
+/-- **Bob's next message** [PS10, Protocol 160.4] (the body of `otReceiver`): on one message
+`i`, the pair of `f_i(w) = eval ⟨i, w⟩` (with `w` sampled from the first coin block) and the raw
+sample `w'` (from the rest), ordered by the choice bit `b = z.headD false`; on two messages `[]`;
+otherwise `H ⟨i, w⟩ ⊕ z_b`. -/
+def receiverNext (x z r : List Bool) (hist : List (List Bool)) : List Bool :=
+  if hist.length = 1 then
+    if z.headD false then
+      pairEncode (T.sample.runAtL x.length (hist.headD []) (r.drop (T.sample.coins.eval x.length)))
+        (T.eval (pairEncode (hist.headD [])
+          (T.sample.runAtL x.length (hist.headD []) (r.take (T.sample.coins.eval x.length)))))
+    else
+      pairEncode (T.eval (pairEncode (hist.headD [])
+          (T.sample.runAtL x.length (hist.headD []) (r.take (T.sample.coins.eval x.length)))))
+        (T.sample.runAtL x.length (hist.headD []) (r.drop (T.sample.coins.eval x.length)))
+  else if hist.length = 2 then []
+  else List.zipWith xor (H (pairEncode (hist.headD [])
+      (T.sample.runAtL x.length (hist.headD []) (r.take (T.sample.coins.eval x.length)))))
+    (if z.headD false then pairSndD (hist.getD 1 []) else pairFstD (hist.getD 1 []))
+
+/-- The defining equation of `receiverNext`: `[i]` ↦ the ordered pair, two messages ↦ `[]`,
+else `H ⟨i, w⟩ ⊕ z_b`, i.e. `receiverNext T H x z r hist = if |hist| = 1 then P else
+if |hist| = 2 then [] else H ⟨i, w⟩ ⊕ z_b` with `P` the pair `⟨f_i(w), w'⟩` (or `⟨w', f_i(w)⟩`
+when `b`), `i = hist.headD []` and `z_b` read off `hist.getD 1 []`. -/
+theorem receiverNext_eq (x z r : List Bool) (hist : List (List Bool)) :
+    receiverNext T H x z r hist =
+      if hist.length = 1 then
+        if z.headD false then
+          pairEncode
+            (T.sample.runAtL x.length (hist.headD []) (r.drop (T.sample.coins.eval x.length)))
+            (T.eval (pairEncode (hist.headD [])
+              (T.sample.runAtL x.length (hist.headD []) (r.take (T.sample.coins.eval x.length)))))
+        else
+          pairEncode (T.eval (pairEncode (hist.headD [])
+              (T.sample.runAtL x.length (hist.headD []) (r.take (T.sample.coins.eval x.length)))))
+            (T.sample.runAtL x.length (hist.headD []) (r.drop (T.sample.coins.eval x.length)))
+      else if hist.length = 2 then []
+      else List.zipWith xor (H (pairEncode (hist.headD [])
+          (T.sample.runAtL x.length (hist.headD []) (r.take (T.sample.coins.eval x.length)))))
+        (if z.headD false then pairSndD (hist.getD 1 []) else pairFstD (hist.getD 1 [])) := rfl
+
+/-- **A protocol of the shape of Protocol 160.4** [PS10]: `P.next = senderNext T H`,
+`V.next = receiverNext T H`, `P.coins = coins_Gen`, `V.coins = coins_Sample + coins_Sample`,
+five messages, Alice first. -/
+def IsOT (π : Protocol) : Prop :=
+  π.P.next = senderNext T H ∧ π.V.next = receiverNext T H ∧ π.P.coins = T.gen.coins ∧
+    π.V.coins = .add T.sample.coins T.sample.coins ∧ π.rounds = .const 5 ∧
+      π.verifierFirst = false
+
+/-- The defining property of `IsOT`: `IsOT T H π` iff the six field equations hold,
+`IsOT T H π ↔ P.next = senderNext T H ∧ V.next = receiverNext T H ∧ P.coins = coins_Gen ∧
+V.coins = coins_Sample + coins_Sample ∧ rounds = 5 ∧ verifierFirst = false`. -/
+theorem isOT_iff (π : Protocol) :
+    IsOT T H π ↔
+      π.P.next = senderNext T H ∧ π.V.next = receiverNext T H ∧ π.P.coins = T.gen.coins ∧
+        π.V.coins = .add T.sample.coins T.sample.coins ∧ π.rounds = .const 5 ∧
+          π.verifierFirst = false := Iff.rfl
+
+/-! ### Messages on short histories -/
+
+/-- Alice's first message is the index: `senderNext T H x y r [] = fst Gen(1^{|x|}; r)`. -/
+theorem senderNext_nil (x y r : List Bool) :
+    senderNext T H x y r [] = pairFstD (T.gen.runAtL x.length [] r) := by
+  rw [senderNext_eq, if_pos List.length_nil]
+
+/-- Alice's second message is the pair of masks:
+`senderNext T H x y r [m] = ⟨mask (fst m) y₀, mask (snd m) y₁⟩`. -/
+theorem senderNext_single (x y r m : List Bool) :
+    senderNext T H x y r [m] =
+      pairEncode
+        (mask T H x.length (pairFstD (T.gen.runAtL x.length [] r))
+          (pairSndD (T.gen.runAtL x.length [] r)) (pairFstD m) (y.getD 0 false))
+        (mask T H x.length (pairFstD (T.gen.runAtL x.length [] r))
+          (pairSndD (T.gen.runAtL x.length [] r)) (pairSndD m) (y.getD 1 false)) := by
+  rw [senderNext_eq, if_neg (by simp), if_pos List.length_singleton, List.headD_cons]
+
+/-- Alice's third message is empty: `senderNext T H x y r [m, m'] = []`. -/
+theorem senderNext_pair (x y r m m' : List Bool) : senderNext T H x y r [m, m'] = [] := by
+  rw [senderNext_eq, if_neg (by simp), if_neg (by simp)]
+
+/-- Bob's first message is the ordered pair `⟨f_i(w), w'⟩` (or `⟨w', f_i(w)⟩` when `b`):
+`receiverNext T H x z r [i] = if b then ⟨w', eval ⟨i, w⟩⟩ else ⟨eval ⟨i, w⟩, w'⟩` with
+`w = Sample(1^{|x|}, i; r.take coins_Sample)`, `w' = Sample(1^{|x|}, i; r.drop coins_Sample)`
+and `b = z.headD false`. -/
+theorem receiverNext_single (x z r i : List Bool) :
+    receiverNext T H x z r [i] =
+      if z.headD false then
+        pairEncode (T.sample.runAtL x.length i (r.drop (T.sample.coins.eval x.length)))
+          (T.eval (pairEncode i
+            (T.sample.runAtL x.length i (r.take (T.sample.coins.eval x.length)))))
+      else
+        pairEncode
+          (T.eval (pairEncode i
+            (T.sample.runAtL x.length i (r.take (T.sample.coins.eval x.length)))))
+          (T.sample.runAtL x.length i (r.drop (T.sample.coins.eval x.length))) := by
+  rw [receiverNext_eq, if_pos List.length_singleton, List.headD_cons]
+
+/-- Bob's second message is empty: `receiverNext T H x z r [m, m'] = []`. -/
+theorem receiverNext_pair (x z r m m' : List Bool) : receiverNext T H x z r [m, m'] = [] := by
+  rw [receiverNext_eq, if_neg (by simp), if_pos (by simp)]
+
+/-! ### The five moves -/
+
+/-- **The five moves of a prover-first execution** [PS10, §4.4]: with
+`m₁ = P([])`, `m₂ = V([m₁])`, `m₃ = P([m₂])`, `m₄ = V([m₁, m₃])`, `m₅ = P([m₂, m₄])`,
+`exec P V false x zP zV rP rV 5 = ([m₂, m₄], [m₁, m₃, m₅])`. -/
+theorem exec_five (P V : Strategy) (x zP zV rP rV : List Bool) {m₁ m₂ m₃ m₄ m₅ : List Bool}
+    (h₁ : P.next x zP rP [] = m₁) (h₂ : V.next x zV rV [m₁] = m₂)
+    (h₃ : P.next x zP rP [m₂] = m₃) (h₄ : V.next x zV rV [m₁, m₃] = m₄)
+    (h₅ : P.next x zP rP [m₂, m₄] = m₅) :
+    exec P V false x zP zV rP rV 5 = ([m₂, m₄], [m₁, m₃, m₅]) := by
+  simp only [exec_succ, exec_zero, moverIsV_false]
+  simp [h₁, h₂, h₃, h₄, h₅]
+
+/-- **The transcript of a protocol of the shape of Protocol 160.4**: with
+`i = fst Gen(1^{|x|}; r₁)`, `y = receiverNext [i]` and `z = senderNext [y]`, the messages received
+are `([y, []], [i, z, []])`. -/
+theorem transcriptWith_isOT {π : Protocol} (hπ : IsOT T H π) (x y z : List Bool)
+    (r : π.ExecCoins π.P x) :
+    π.transcriptWith π.P x y z r =
+      ([receiverNext T H x z (List.ofFn r.2)
+          [pairFstD (T.gen.runAtL x.length [] (List.ofFn r.1))], []],
+        [pairFstD (T.gen.runAtL x.length [] (List.ofFn r.1)),
+          senderNext T H x y (List.ofFn r.1) [receiverNext T H x z (List.ofFn r.2)
+            [pairFstD (T.gen.runAtL x.length [] (List.ofFn r.1))]], []]) := by
+  obtain ⟨hP, hV, -, -, hr, hf⟩ := (isOT_iff T H π).1 hπ
+  rw [Protocol.transcriptWith_eq, hr, hf, PolyExpr.eval_const]
+  exact exec_five _ _ _ _ _ _ _ (by rw [hP, senderNext_nil]) (by rw [hV]) (by rw [hP])
+    (by rw [hV, receiverNext_pair]) (by rw [hP, senderNext_pair])
+
+end TCSlib.Cryptography.SecureComputation.OT
diff --git a/TCSlib/Cryptography/SecureComputation/ObliviousTransfer/Simulators.lean b/TCSlib/Cryptography/SecureComputation/ObliviousTransfer/Simulators.lean
new file mode 100644
index 000000000..c6ddd88bb
--- /dev/null
+++ b/TCSlib/Cryptography/SecureComputation/ObliviousTransfer/Simulators.lean
@@ -0,0 +1,435 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.SecureComputation.ObliviousTransfer.Shape
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Oblivious transfer: the shape of the simulators of Proposition 161.5
+
+The simulators `S_A` and `S_B` of [PS10, Proposition 161.5] restated for the helper modules
+(which cannot import `SecureComputation/ObliviousTransfer.lean`, the owned file that imports them):
+the coin segments, the simulated index and samples, and the two simulated views, with the
+predicates `OT.IsSimA` and `OT.IsSimB` that the owned file proves for `otSimA` and `otSimB`.
+On a tape assembled from typed coin blocks (`OT.splitLen`), the simulated views are computed
+explicitly (`OT.simAView_layout`, `OT.simBView_layout`).
+
+## Main definitions
+
+* `OT.splitLen`: a coin string of length `c = a + b` as an `a`-bit and a `b`-bit string.
+* `OT.simSeg`, `OT.simIndex`, `OT.simSampled`: a coin segment, the simulated index and a
+  simulated sample (the bodies of `coinSeg`, `simIdx`, `simSample`).
+* `OT.simAView`, `OT.simZbit`, `OT.simZpair`, `OT.simBView`: the simulators' raw functions (the
+  bodies of `otSimAFun`, `otSimZb`, `otSimZ`, `otSimBFun`).
+* `OT.IsSimA`, `OT.IsSimB`: machines of the simulators' shape.
+
+## Main results
+
+* `OT.splitLen_symm_ofFn`: the assembled tape is the concatenation of the blocks.
+* `OT.simSeg_layout`, `OT.simIndex_layout`, `OT.simSampled_layout`: the pieces on such a tape.
+* `OT.simAView_layout`, `OT.simBView_layout`: the simulated views on such a tape.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §6.2.4, Proposition 161.5 (book pp. 160–162).
+-/
+
+namespace TCSlib.Cryptography.SecureComputation.OT
+
+open Complexity Turing TCSlib.Cryptography
+
+variable (T : TrapdoorCollection) (H : List Bool → List Bool)
+
+/-! ### Splitting coin strings -/
+
+/-- **A coin string of length `c = a + b` split** into its first `a` and last `b` bits:
+`splitCoins a b` after the length cast `Fin c ≃ Fin (a + b)`. -/
+def splitLen {a b c : ℕ} (h : c = a + b) : (Fin c → Bool) ≃ (Fin a → Bool) × (Fin b → Bool) :=
+  (Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)).trans (splitCoins a b)
+
+/-- The tape assembled from two blocks is their concatenation:
+`ofFn ((splitLen h).symm (r₁, r₂)) = ofFn r₁ ++ ofFn r₂` (`ofFn_splitCoins_symm`). -/
+theorem splitLen_symm_ofFn {a b c : ℕ} (h : c = a + b) (p : (Fin a → Bool) × (Fin b → Bool)) :
+    List.ofFn ((splitLen h).symm p) = List.ofFn p.1 ++ List.ofFn p.2 := by
+  rw [← ofFn_splitCoins_symm]
+  exact (List.ofFn_congr h _).trans rfl
+
+/-! ### The simulators restated -/
+
+/-- The coin segment of length `q(n)` after the first `p(n)` coins of a raw layout `z` (the body
+of `coinSeg`): `(inCoins z).drop p(|inParam z|) |>.take q(|inParam z|)`. -/
+def simSeg (p q : PolyExpr) (z : List Bool) : List Bool :=
+  ((NUPPT.inCoins z).drop (p.eval (NUPPT.inParam z).length)).take (q.eval (NUPPT.inParam z).length)
+
+/-- The defining equation of `simSeg`: `simSeg p q z =
+((inCoins z).drop p(|inParam z|)).take q(|inParam z|)`. -/
+theorem simSeg_eq (p q : PolyExpr) (z : List Bool) :
+    simSeg p q z =
+      ((NUPPT.inCoins z).drop (p.eval (NUPPT.inParam z).length)).take
+        (q.eval (NUPPT.inParam z).length) := rfl
+
+/-- The simulated index (the body of `simIdx`):
+`simIndex T z = fst Gen(inParam z; simSeg 0 coins_Gen z)`. -/
+def simIndex (z : List Bool) : List Bool :=
+  pairFstD (T.gen.output (NUPPT.layout (NUPPT.inParam z) [] []
+    (simSeg (.const 0) T.gen.coins z)))
+
+/-- The defining equation of `simIndex`: `simIndex T z =
+fst Gen.output (layout (inParam z) [] [] (simSeg 0 coins_Gen z))`. -/
+theorem simIndex_eq (z : List Bool) :
+    simIndex T z = pairFstD (T.gen.output (NUPPT.layout (NUPPT.inParam z) [] []
+      (simSeg (.const 0) T.gen.coins z))) := rfl
+
+/-- A simulated sample after `p(n)` coins (the body of `simSample`):
+`simSampled T p z = Sample(inParam z, simIndex z; simSeg p coins_Sample z)`. -/
+def simSampled (p : PolyExpr) (z : List Bool) : List Bool :=
+  T.sample.output (NUPPT.layout (NUPPT.inParam z) (simIndex T z) [] (simSeg p T.sample.coins z))
+
+/-- The defining equation of `simSampled`: `simSampled T p z =
+Sample.output (layout (inParam z) (simIndex T z) [] (simSeg p coins_Sample z))`. -/
+theorem simSampled_eq (p : PolyExpr) (z : List Bool) :
+    simSampled T p z =
+      T.sample.output (NUPPT.layout (NUPPT.inParam z) (simIndex T z) []
+        (simSeg p T.sample.coins z)) := rfl
+
+/-- **`S_A`'s raw function** [PS10, Proposition 161.5] (the body of `otSimAFun`):
+`simAView T z = ⟨⟨1^n, ⟨a₁, a₂⟩⟩, ⟨r_Gen, [⟨y₁, y₂⟩, []]⟩⟩` with two simulated samples
+`y₁, y₂`. -/
+def simAView (z : List Bool) : List Bool :=
+  pairEncode (pairEncode (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)))
+    (pairEncode (simSeg (.const 0) T.gen.coins z)
+      (pairEncode (pairEncode (simSampled T T.gen.coins z)
+          (simSampled T (.add T.gen.coins T.sample.coins) z))
+        (pairEncode [] [])))
+
+/-- The defining equation of `simAView`: `simAView T z = ⟨⟨inParam z, fst (inArg z)⟩,
+⟨simSeg 0 coins_Gen z, [⟨y₁, y₂⟩, []]⟩⟩` with the two simulated samples `y₁, y₂`. -/
+theorem simAView_eq (z : List Bool) :
+    simAView T z =
+      pairEncode (pairEncode (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)))
+        (pairEncode (simSeg (.const 0) T.gen.coins z)
+          (pairEncode (pairEncode (simSampled T T.gen.coins z)
+              (simSampled T (.add T.gen.coins T.sample.coins) z))
+            (pairEncode [] []))) := rfl
+
+/-- `S_B`'s mask `z_b = h(x) ⊕ a_b` (the body of `otSimZb`). -/
+def simZbit (z : List Bool) : List Bool :=
+  List.zipWith xor (H (pairEncode (simIndex T z) (simSampled T T.gen.coins z)))
+    (pairSndD (NUPPT.inArg z))
+
+/-- The defining equation of `simZbit`: `simZbit T H z =
+zipWith xor (H ⟨simIndex T z, simSampled T coins_Gen z⟩) (snd (inArg z))`. -/
+theorem simZbit_eq (z : List Bool) :
+    simZbit T H z =
+      List.zipWith xor (H (pairEncode (simIndex T z) (simSampled T T.gen.coins z)))
+        (pairSndD (NUPPT.inArg z)) := rfl
+
+/-- `S_B`'s pair `(z₁, z₂)` (the body of `otSimZ`): `z_b` from `simZbit`, `z_{1−b}` one coin,
+`simZpair T H z = ⟨c, z_b⟩` if the choice bit is set, else `⟨z_b, c⟩`. -/
+def simZpair (z : List Bool) : List Bool :=
+  if (pairFstD (NUPPT.inArg z)).headD false then
+    pairEncode (simSeg (.add T.gen.coins (.add T.sample.coins T.sample.coins)) (.const 1) z)
+      (simZbit T H z)
+  else
+    pairEncode (simZbit T H z)
+      (simSeg (.add T.gen.coins (.add T.sample.coins T.sample.coins)) (.const 1) z)
+
+/-- The defining equation of `simZpair`: `⟨c, z_b⟩` if the choice bit is set, else `⟨z_b, c⟩`,
+with `c` the last coin segment and `z_b = simZbit T H z`. -/
+theorem simZpair_eq (z : List Bool) :
+    simZpair T H z =
+      if (pairFstD (NUPPT.inArg z)).headD false then
+        pairEncode (simSeg (.add T.gen.coins (.add T.sample.coins T.sample.coins)) (.const 1) z)
+          (simZbit T H z)
+      else
+        pairEncode (simZbit T H z)
+          (simSeg (.add T.gen.coins (.add T.sample.coins T.sample.coins)) (.const 1) z) := rfl
+
+/-- **`S_B`'s raw function** [PS10, Proposition 161.5] (the body of `otSimBFun`):
+`simBView T H z = ⟨⟨1^n, [b]⟩, ⟨r_B, [i, ⟨z₁, z₂⟩, []]⟩⟩`. -/
+def simBView (z : List Bool) : List Bool :=
+  pairEncode (pairEncode (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)))
+    (pairEncode (simSeg T.gen.coins (.add T.sample.coins T.sample.coins) z)
+      (pairEncode (simIndex T z) (pairEncode (simZpair T H z) (pairEncode [] []))))
+
+/-- The defining equation of `simBView`: `simBView T H z = ⟨⟨inParam z, fst (inArg z)⟩,
+⟨simSeg coins_Gen (2 coins_Sample) z, [simIndex T z, simZpair T H z, []]⟩⟩`. -/
+theorem simBView_eq (z : List Bool) :
+    simBView T H z =
+      pairEncode (pairEncode (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)))
+        (pairEncode (simSeg T.gen.coins (.add T.sample.coins T.sample.coins) z)
+          (pairEncode (simIndex T z) (pairEncode (simZpair T H z) (pairEncode [] [])))) := rfl
+
+/-- **A machine of `S_A`'s shape**: coins `coins_Gen + (coins_Sample + coins_Sample)`, and
+`S(1^n, y; r) = simAView T (layout 1^n y [] r)`. -/
+def IsSimA (S : NUPPT) : Prop :=
+  S.coins = .add T.gen.coins (.add T.sample.coins T.sample.coins) ∧
+    ∀ n y (r : S.Coins n),
+      S.runAt n y r = simAView T (NUPPT.layout (List.replicate n true) y [] (List.ofFn r))
+
+/-- The defining property of `IsSimA`: `IsSimA T S` iff `S.coins = coins_Gen + (coins_Sample +
+coins_Sample)` and `S(1^n, y; r) = simAView T (layout 1^n y [] r)`. -/
+theorem isSimA_iff (S : NUPPT) :
+    IsSimA T S ↔
+      S.coins = .add T.gen.coins (.add T.sample.coins T.sample.coins) ∧
+        ∀ n y (r : S.Coins n),
+          S.runAt n y r = simAView T (NUPPT.layout (List.replicate n true) y [] (List.ofFn r)) :=
+  Iff.rfl
+
+/-- **A machine of `S_B`'s shape**: coins `coins_Gen + (coins_Sample + (coins_Sample + 1))`, and
+`S(1^n, y; r) = simBView T H (layout 1^n y [] r)`. -/
+def IsSimB (S : NUPPT) : Prop :=
+  S.coins = .add T.gen.coins (.add T.sample.coins (.add T.sample.coins (.const 1))) ∧
+    ∀ n y (r : S.Coins n),
+      S.runAt n y r = simBView T H (NUPPT.layout (List.replicate n true) y [] (List.ofFn r))
+
+/-- The defining property of `IsSimB`: `IsSimB T H S` iff its coins are `coins_Gen +
+(coins_Sample + (coins_Sample + 1))` and `S(1^n, y; r) = simBView T H (layout 1^n y [] r)`. -/
+theorem isSimB_iff (S : NUPPT) :
+    IsSimB T H S ↔
+      S.coins = .add T.gen.coins (.add T.sample.coins (.add T.sample.coins (.const 1))) ∧
+        ∀ n y (r : S.Coins n),
+          S.runAt n y r = simBView T H (NUPPT.layout (List.replicate n true) y [] (List.ofFn r)) :=
+  Iff.rfl
+
+/-! ### The simulators on assembled tapes -/
+
+/-- A coin segment of a tape `A ++ (B ++ C)` with `|A| = p(|u|)` and `|B| = q(|u|)` is `B`. -/
+theorem simSeg_layout {p q : PolyExpr} (u y α : List Bool) {A B : List Bool} (C : List Bool)
+    (hA : A.length = p.eval u.length) (hB : B.length = q.eval u.length) :
+    simSeg p q (NUPPT.layout u y α (A ++ (B ++ C))) = B := by
+  rw [simSeg_eq, NUPPT.inCoins_layout, NUPPT.inParam_layout, List.drop_left' hA,
+    List.take_left' hB]
+
+/-- The typed tape of a machine as a list has the coin length: `|ofFn r| = coins_A(n)`. -/
+theorem length_ofFn_coins (A : NUPPT) (n : ℕ) (r : A.Coins n) :
+    (List.ofFn r).length = A.coins.eval n := by
+  rw [List.length_ofFn, NUPPT.coinLen_eq]
+
+/-- On a tape starting with `Gen`'s coins `r`, the simulated index is `index n r`:
+`simIndex T (layout 1^n y [] (ofFn r ++ B)) = T.index n r`. -/
+theorem simIndex_layout (n : ℕ) (y : List Bool) (r : T.gen.Coins n) (B : List Bool) :
+    simIndex T (NUPPT.layout (List.replicate n true) y [] (List.ofFn r ++ B)) = T.index n r := by
+  have h := simSeg_layout (p := .const 0) (q := T.gen.coins) (List.replicate n true) y [] B
+    (A := []) (B := List.ofFn r) (by rw [PolyExpr.eval_const, List.length_nil])
+    (by rw [length_ofFn_coins, List.length_replicate])
+  rw [List.nil_append] at h
+  rw [simIndex_eq, h, NUPPT.inParam_layout, Collection.index_eq, NUPPT.runAt_eq,
+    NUPPT.runAtL_eq_output_layout, NUPPT.Uniform.advice_eq T.gen_uniform]
+
+/-- On a tape `r ++ (A ++ (s ++ C))` with `|A| = p(n) - coins_Gen(n)`, the simulated sample
+after `p(n)` coins is `Sample(1^n, index n r; s)`. -/
+theorem simSampled_layout {p : PolyExpr} (n : ℕ) (y : List Bool) (r : T.gen.Coins n)
+    (A : List Bool) (s : T.sample.Coins n) (C : List Bool)
+    (hA : (List.ofFn r ++ A).length = p.eval n) :
+    simSampled T p
+        (NUPPT.layout (List.replicate n true) y [] (List.ofFn r ++ (A ++ (List.ofFn s ++ C)))) =
+      T.sample.runAt n (T.index n r) s := by
+  have h := simSeg_layout (p := p) (q := T.sample.coins) (List.replicate n true) y []
+    (A := List.ofFn r ++ A) (B := List.ofFn s) C (by rw [hA, List.length_replicate])
+    (by rw [length_ofFn_coins, List.length_replicate])
+  rw [List.append_assoc] at h
+  rw [simSampled_eq, h, NUPPT.inParam_layout, simIndex_layout,
+    NUPPT.runAt_eq, NUPPT.runAtL_eq_output_layout, NUPPT.Uniform.advice_eq T.sample_uniform]
+
+/-- **`S_A`'s view on the tape `r ++ (s₁ ++ s₂)`**:
+`⟨⟨1^n, fst y⟩, ⟨r, [⟨Sample(i; s₁), Sample(i; s₂)⟩, []]⟩⟩` with `i = index n r`. -/
+theorem simAView_layout (n : ℕ) (y : List Bool) (r : T.gen.Coins n)
+    (s₁ s₂ : T.sample.Coins n) :
+    simAView T (NUPPT.layout (List.replicate n true) y []
+        (List.ofFn r ++ (List.ofFn s₁ ++ List.ofFn s₂))) =
+      pairEncode (pairEncode (List.replicate n true) (pairFstD y))
+        (pairEncode (List.ofFn r)
+          (pairEncode (pairEncode (T.sample.runAt n (T.index n r) s₁)
+              (T.sample.runAt n (T.index n r) s₂))
+            (pairEncode [] []))) := by
+  have h₀ := simSeg_layout (p := .const 0) (q := T.gen.coins) (List.replicate n true) y []
+    (A := []) (B := List.ofFn r) (List.ofFn s₁ ++ List.ofFn s₂)
+    (by rw [PolyExpr.eval_const, List.length_nil])
+    (by rw [length_ofFn_coins, List.length_replicate])
+  rw [List.nil_append] at h₀
+  have h₁ := simSampled_layout T (p := T.gen.coins) n y r [] s₁ (List.ofFn s₂)
+    (by rw [List.append_nil, length_ofFn_coins])
+  have h₂ := simSampled_layout T (p := .add T.gen.coins T.sample.coins) n y r
+    (List.ofFn s₁) s₂ [] (by rw [List.length_append, length_ofFn_coins, length_ofFn_coins,
+      PolyExpr.eval_add])
+  rw [List.nil_append] at h₁
+  rw [List.append_nil] at h₂
+  rw [simAView_eq, NUPPT.inParam_layout, NUPPT.inArg_layout, h₀, h₁, h₂]
+
+/-- **`S_B`'s view on the tape `r ++ (s₁ ++ (s₂ ++ c))`**:
+`⟨⟨1^n, fst y⟩, ⟨s₁ ++ s₂, [i, Z, []]⟩⟩` with `i = index n r`, `z_b = H ⟨i, Sample(i; s₁)⟩ ⊕ snd y`
+and `Z = ⟨c, z_b⟩` if `(fst y).headD false`, else `⟨z_b, c⟩`.
+
+**Proof sketch.** The coin segments of the tape are `s₁ ++ s₂` and `c` (`simSeg_layout`), the
+simulated index is `index n r` (`simIndex_layout`) and the first simulated sample is
+`Sample(i; s₁)` (`simSampled_layout`); rewrite `simBView`, `simZpair` and `simZbit` with them. -/
+theorem simBView_layout (n : ℕ) (y : List Bool) (r : T.gen.Coins n)
+    (s₁ s₂ : T.sample.Coins n) (c : Fin 1 → Bool) :
+    simBView T H (NUPPT.layout (List.replicate n true) y []
+        (List.ofFn r ++ (List.ofFn s₁ ++ (List.ofFn s₂ ++ List.ofFn c)))) =
+      pairEncode (pairEncode (List.replicate n true) (pairFstD y))
+        (pairEncode (List.ofFn s₁ ++ List.ofFn s₂)
+          (pairEncode (T.index n r)
+            (pairEncode
+              (if (pairFstD y).headD false then
+                pairEncode (List.ofFn c)
+                  (List.zipWith xor (H (pairEncode (T.index n r)
+                    (T.sample.runAt n (T.index n r) s₁))) (pairSndD y))
+              else
+                pairEncode (List.zipWith xor (H (pairEncode (T.index n r)
+                    (T.sample.runAt n (T.index n r) s₁))) (pairSndD y))
+                  (List.ofFn c))
+              (pairEncode [] [])))) := by
+  have hs := simSeg_layout (p := T.gen.coins) (q := .add T.sample.coins T.sample.coins)
+    (List.replicate n true) y [] (A := List.ofFn r) (B := List.ofFn s₁ ++ List.ofFn s₂)
+    (List.ofFn c) (by rw [length_ofFn_coins, List.length_replicate])
+    (by rw [List.length_append, length_ofFn_coins, length_ofFn_coins, PolyExpr.eval_add,
+      List.length_replicate])
+  rw [List.append_assoc] at hs
+  have hc := simSeg_layout (p := .add T.gen.coins (.add T.sample.coins T.sample.coins))
+    (q := .const 1) (List.replicate n true) y []
+    (A := List.ofFn r ++ (List.ofFn s₁ ++ List.ofFn s₂)) (B := List.ofFn c) []
+    (by rw [List.length_append, List.length_append, length_ofFn_coins, length_ofFn_coins,
+      length_ofFn_coins, PolyExpr.eval_add, PolyExpr.eval_add, List.length_replicate])
+    (by rw [List.length_ofFn, PolyExpr.eval_const])
+  rw [List.append_nil, List.append_assoc, List.append_assoc] at hc
+  have hi := simIndex_layout T n y r (List.ofFn s₁ ++ (List.ofFn s₂ ++ List.ofFn c))
+  have h₁ := simSampled_layout T (p := T.gen.coins) n y r [] s₁ (List.ofFn s₂ ++ List.ofFn c)
+    (by rw [List.append_nil, length_ofFn_coins])
+  rw [List.nil_append] at h₁
+  rw [simBView_eq, simZpair_eq, simZbit_eq, NUPPT.inParam_layout, NUPPT.inArg_layout, hs, hc,
+    hi, h₁]
+
+/-! ### The coin spaces -/
+
+/-- **The real coins of a protocol of the shape of Protocol 160.4**: Alice's tape is `Gen`'s
+coins and Bob's two sampler blocks, `ExecCoins ≃ Coins_Gen × (Coins_Sample × Coins_Sample)`. -/
+def realCoins {π : Protocol} (hπ : IsOT T H π) (n : ℕ) :
+    π.ExecCoins π.P (List.replicate n true) ≃
+      T.gen.Coins n × (T.sample.Coins n × T.sample.Coins n) :=
+  Equiv.prodCongr
+    (Equiv.arrowCongr (finCongr (by
+      rw [Strategy.coinLen_eq, ((isOT_iff T H π).1 hπ).2.2.1, List.length_replicate,
+        NUPPT.coinLen_eq])) (Equiv.refl Bool))
+    (splitLen (by
+      rw [Strategy.coinLen_eq, ((isOT_iff T H π).1 hπ).2.2.2.1, List.length_replicate,
+        PolyExpr.eval_add, NUPPT.coinLen_eq]))
+
+/-- Alice's real tape is `Gen`'s coins: `ofFn ((realCoins hπ n).symm p).1 = ofFn p.1`. -/
+theorem realCoins_symm_fst_ofFn {π : Protocol} (hπ : IsOT T H π) (n : ℕ)
+    (p : T.gen.Coins n × (T.sample.Coins n × T.sample.Coins n)) :
+    List.ofFn ((realCoins T H hπ n).symm p).1 = List.ofFn p.1 :=
+  (List.ofFn_congr (by rw [Strategy.coinLen_eq, ((isOT_iff T H π).1 hπ).2.2.1,
+    List.length_replicate, NUPPT.coinLen_eq]) _).trans rfl
+
+/-- Bob's real tape is the two sampler blocks:
+`ofFn ((realCoins hπ n).symm p).2 = ofFn p.2.1 ++ ofFn p.2.2`. -/
+theorem realCoins_symm_snd_ofFn {π : Protocol} (hπ : IsOT T H π) (n : ℕ)
+    (p : T.gen.Coins n × (T.sample.Coins n × T.sample.Coins n)) :
+    List.ofFn ((realCoins T H hπ n).symm p).2 = List.ofFn p.2.1 ++ List.ofFn p.2.2 :=
+  splitLen_symm_ofFn _ p.2
+
+/-- **`S_A`'s coins**: `Coins_S ≃ Coins_Gen × (Coins_Sample × Coins_Sample)` for a machine of
+`S_A`'s shape. -/
+def simACoins {S : NUPPT} (hS : IsSimA T S) (n : ℕ) :
+    S.Coins n ≃ T.gen.Coins n × (T.sample.Coins n × T.sample.Coins n) :=
+  (splitLen (by rw [NUPPT.coinLen_eq, ((isSimA_iff T S).1 hS).1, PolyExpr.eval_add,
+    NUPPT.coinLen_eq])).trans
+    (Equiv.prodCongr (Equiv.refl _) (splitLen (by rw [PolyExpr.eval_add, NUPPT.coinLen_eq])))
+
+/-- `S_A`'s tape from blocks: `ofFn ((simACoins hS n).symm p) = ofFn p.1 ++ (ofFn p.2.1 ++
+ofFn p.2.2)`. -/
+theorem simACoins_symm_ofFn {S : NUPPT} (hS : IsSimA T S) (n : ℕ)
+    (p : T.gen.Coins n × (T.sample.Coins n × T.sample.Coins n)) :
+    List.ofFn ((simACoins T hS n).symm p) =
+      List.ofFn p.1 ++ (List.ofFn p.2.1 ++ List.ofFn p.2.2) := by
+  rw [simACoins, Equiv.symm_trans_apply, splitLen_symm_ofFn, Equiv.prodCongr_symm,
+    Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.refl_symm, Equiv.refl_apply,
+    splitLen_symm_ofFn]
+
+/-- **`S_B`'s coins**: `Coins_S ≃ Coins_Gen × (Coins_Sample × (Coins_Sample × {0,1}))` for a
+machine of `S_B`'s shape. -/
+def simBCoins {S : NUPPT} (hS : IsSimB T H S) (n : ℕ) :
+    S.Coins n ≃ T.gen.Coins n × (T.sample.Coins n × (T.sample.Coins n × (Fin 1 → Bool))) :=
+  (splitLen (by rw [NUPPT.coinLen_eq, ((isSimB_iff T H S).1 hS).1, PolyExpr.eval_add,
+    NUPPT.coinLen_eq])).trans
+    (Equiv.prodCongr (Equiv.refl _) ((splitLen (by rw [PolyExpr.eval_add, NUPPT.coinLen_eq])).trans
+      (Equiv.prodCongr (Equiv.refl _)
+        (splitLen (by rw [PolyExpr.eval_add, NUPPT.coinLen_eq, PolyExpr.eval_const])))))
+
+/-- `S_B`'s tape from blocks: `ofFn ((simBCoins hS n).symm p) =
+ofFn p.1 ++ (ofFn p.2.1 ++ (ofFn p.2.2.1 ++ ofFn p.2.2.2))`. -/
+theorem simBCoins_symm_ofFn {S : NUPPT} (hS : IsSimB T H S) (n : ℕ)
+    (p : T.gen.Coins n × (T.sample.Coins n × (T.sample.Coins n × (Fin 1 → Bool)))) :
+    List.ofFn ((simBCoins T H hS n).symm p) =
+      List.ofFn p.1 ++ (List.ofFn p.2.1 ++ (List.ofFn p.2.2.1 ++ List.ofFn p.2.2.2)) := by
+  rw [simBCoins, Equiv.symm_trans_apply, splitLen_symm_ofFn, Equiv.prodCongr_symm,
+    Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.refl_symm, Equiv.refl_apply,
+    Equiv.symm_trans_apply, splitLen_symm_ofFn, Equiv.prodCongr_symm, Equiv.prodCongr_apply,
+    Prod.map_fst, Prod.map_snd, Equiv.refl_symm, Equiv.refl_apply, splitLen_symm_ofFn]
+
+/-! ### The OT inputs and outputs -/
+
+/-- Alice's OT input length is `2`, `otFunctionality.inA.eval n = 2` (`otFunctionality_inA`). -/
+theorem inA_eval (n : ℕ) : otFunctionality.inA.eval n = 2 := by
+  rw [otFunctionality_inA, PolyExpr.eval_const]
+
+/-- Bob's OT input length is `1`, `otFunctionality.inB.eval n = 1` (`otFunctionality_inB`). -/
+theorem inB_eval (n : ℕ) : otFunctionality.inB.eval n = 1 := by
+  rw [otFunctionality_inB, PolyExpr.eval_const]
+
+/-- Alice's OT input read as two bits: `inA2 a j = a (cast j)`. -/
+def inA2 {n : ℕ} (a : Fin (otFunctionality.inA.eval n) → Bool) : Fin 2 → Bool :=
+  fun j => a (Fin.cast (inA_eval n).symm j)
+
+/-- The defining equation of `inA2`: `inA2 a j = a (Fin.cast (inA_eval n).symm j)`. -/
+theorem inA2_apply {n : ℕ} (a : Fin (otFunctionality.inA.eval n) → Bool) (j : Fin 2) :
+    inA2 a j = a (Fin.cast (inA_eval n).symm j) := rfl
+
+/-- Reading the input as two bits keeps its string: `ofFn (inA2 a) = ofFn a`. -/
+theorem ofFn_inA2 {n : ℕ} (a : Fin (otFunctionality.inA.eval n) → Bool) :
+    List.ofFn (inA2 a) = List.ofFn a :=
+  ((List.ofFn_congr (inA_eval n) a).trans rfl).symm
+
+/-- Bob's OT input read as one bit: `inB1 b j = b (cast j)`. -/
+def inB1 {n : ℕ} (b : Fin (otFunctionality.inB.eval n) → Bool) : Fin 1 → Bool :=
+  fun j => b (Fin.cast (inB_eval n).symm j)
+
+/-- The defining equation of `inB1`: `inB1 b j = b (Fin.cast (inB_eval n).symm j)`. -/
+theorem inB1_apply {n : ℕ} (b : Fin (otFunctionality.inB.eval n) → Bool) (j : Fin 1) :
+    inB1 b j = b (Fin.cast (inB_eval n).symm j) := rfl
+
+/-- Reading the input as one bit keeps its string: `ofFn (inB1 b) = ofFn b`. -/
+theorem ofFn_inB1 {n : ℕ} (b : Fin (otFunctionality.inB.eval n) → Bool) :
+    List.ofFn (inB1 b) = List.ofFn b :=
+  ((List.ofFn_congr (inB_eval n) b).trans rfl).symm
+
+/-- Bob's choice string is the one-bit list `[inB1 b 0]`: `List.ofFn b = [inB1 b 0]`. -/
+theorem ofFn_eq_inB1 {n : ℕ} (b : Fin (otFunctionality.inB.eval n) → Bool) :
+    List.ofFn b = [inB1 b 0] := by
+  rw [← ofFn_inB1, List.ofFn_succ, List.ofFn_zero]
+
+/-- Alice's OT output is empty: `ofFn (f n a b).1 = []`. -/
+theorem ofFn_f_fst (n : ℕ) (a : Fin (otFunctionality.inA.eval n) → Bool)
+    (b : Fin (otFunctionality.inB.eval n) → Bool) :
+    List.ofFn (otFunctionality.f n a b).1 = [] :=
+  List.eq_nil_of_length_eq_zero
+    (by rw [List.length_ofFn, otFunctionality_outA, PolyExpr.eval_const])
+
+/-- Bob's OT output is the chosen bit: `ofFn (f n a b).2 = [a_b]` with
+`a_b = inA2 a (if inB1 b 0 then 1 else 0)` (`otFunctionality_f_snd_apply`). -/
+theorem ofFn_f_snd (n : ℕ) (a : Fin (otFunctionality.inA.eval n) → Bool)
+    (b : Fin (otFunctionality.inB.eval n) → Bool) :
+    List.ofFn (otFunctionality.f n a b).2 = [inA2 a (if inB1 b 0 then 1 else 0)] := by
+  have h : otFunctionality.outB.eval n = 1 := by
+    rw [otFunctionality_outB, PolyExpr.eval_const]
+  rw [List.ofFn_congr h, List.ofFn_succ, List.ofFn_zero, otFunctionality_f_snd_apply]
+  rfl
+
+end TCSlib.Cryptography.SecureComputation.OT
diff --git a/TCSlib/Cryptography/SecureComputation/ObliviousTransfer/ViewA.lean b/TCSlib/Cryptography/SecureComputation/ObliviousTransfer/ViewA.lean
new file mode 100644
index 000000000..d11c5678f
--- /dev/null
+++ b/TCSlib/Cryptography/SecureComputation/ObliviousTransfer/ViewA.lean
@@ -0,0 +1,186 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.SecureComputation.ObliviousTransfer.Simulators
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Oblivious transfer: Alice's side of Proposition 161.5
+
+Alice's real view of Protocol 160.4 differs from `S_A`'s only in Bob's message: the real pair holds
+`y_b = f_i(x) = eval ⟨i, w⟩` for a sampled `w` and a raw sample `y_{1−b}`, the simulated pair two
+raw samples. For every generated index `i`, `eval ⟨i, w⟩` is within `2δ(n)` of a raw sample when
+the sampler is within `δ(n)` of uniform (`perm_i` is a bijection), so any distinguisher's
+advantage is at most `2δ(n)` [PS10, Proposition 161.5, proof].
+
+## Main results
+
+* `OT.statClose_prod_of_forall`: closeness for every value of a shared first coordinate gives
+  closeness of the joint samplers.
+* `OT.statClose_eval_sample`: `eval ⟨i, Sample(i; s)⟩` is `2δ(n)`-close to `Sample(i; s)`.
+* `OT.realA_realCoins`, `OT.idealA_simACoins`: Alice's real and ideal samplers on typed coins.
+* `OT.distAdv_realA_idealA_le`: the bound `2δ(n)` on Alice's side.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §6.2.4, Proposition 161.5 (book pp. 161–162).
+-/
+
+namespace TCSlib.Cryptography.SecureComputation.OT
+
+open Complexity Turing TCSlib.Cryptography
+
+variable (T : TrapdoorCollection) (H : List Bool → List Bool)
+
+/-- **Closeness with a shared first coordinate**: if `X r` is `c`-close to `Y r` for every `r`
+(and `0 ≤ c`), then `(r, X r s)` is `c`-close to `(r, Y r t)` over uniform `(r, s)` and `(r, t)`
+(`uprob_prod`, `abs_uexp_sub_le`). -/
+theorem statClose_prod_of_forall {ρ σ τ γ : Type*} [Fintype ρ] [Fintype σ] [Fintype τ]
+    {X : ρ → σ → γ} {Y : ρ → τ → γ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ r, StatClose (X r) (Y r) c) :
+    StatClose (fun z : ρ × σ => (z.1, X z.1 z.2)) (fun z : ρ × τ => (z.1, Y z.1 z.2)) c := by
+  refine (statClose_iff _ _ _).2 fun P => ?_
+  rw [uprob_prod, uprob_prod]
+  exact abs_uexp_sub_le hc fun r => (statClose_iff _ _ _).1 (h r) fun g => P (r, g)
+
+/-- **The evaluated sample is close to a raw sample** [PS10, Proposition 161.5, proof]: at every
+generated index `i = index n r`, `eval ⟨i, Sample(i; s)⟩` is `2δ(n)`-close to `Sample(i; s)` when
+the sampler is within `δ` of uniform.
+
+**Proof sketch.** Decoding the sample is `δ`-close to the uniform element (`SampleClose`). Mapping
+by `x ↦ encD (perm x)` gives `eval ⟨i, Sample⟩` (`evalSampled`, `f_perm`) against
+`encD (perm x)`, which is `0`-close to `encD x` (`perm` is a bijection, `comp_equiv_left`).
+Mapping by `encD` gives `Sample` (canonical decoding) against `encD x`. Chain the three. -/
+theorem statClose_eval_sample {δ : ℕ → ℝ} (hδ : T.SampleClose δ) (n : ℕ) (r : T.gen.Coins n) :
+    StatClose (fun s : T.sample.Coins n =>
+        T.eval (pairEncode (T.index n r) (T.sample.runAt n (T.index n r) s)))
+      (fun s => T.sample.runAt n (T.index n r) s) (2 * δ n) := by
+  have h₁ := (Collection.sampleClose_iff _ _).1 hδ n r
+  have hA : StatClose (fun s : T.sample.Coins n => T.encD (T.index n r) (T.perm (T.index n r)
+      ((T.decD (T.index n r) (T.sample.runAt n (T.index n r) s)).getD default)))
+      (fun x => T.encD (T.index n r) (T.perm (T.index n r) x)) (δ n) :=
+    h₁.map fun o => T.encD (T.index n r) (T.perm (T.index n r) (o.getD default))
+  have hC : StatClose (fun s : T.sample.Coins n => T.encD (T.index n r)
+      ((T.decD (T.index n r) (T.sample.runAt n (T.index n r) s)).getD default))
+      (fun x => T.encD (T.index n r) x) (δ n) :=
+    h₁.map fun o => T.encD (T.index n r) (o.getD default)
+  have eA : (fun s : T.sample.Coins n => T.encD (T.index n r) (T.perm (T.index n r)
+      ((T.decD (T.index n r) (T.sample.runAt n (T.index n r) s)).getD default))) =
+      fun s => T.eval (pairEncode (T.index n r) (T.sample.runAt n (T.index n r) s)) := by
+    funext s
+    obtain ⟨x, hx, hev⟩ := (Collection.evalSampled_iff _).1 T.toCollection.evalSampled n r s
+    rw [hx, Option.getD_some, hev, T.f_perm]
+  have eC : (fun s : T.sample.Coins n => T.encD (T.index n r)
+      ((T.decD (T.index n r) (T.sample.runAt n (T.index n r) s)).getD default)) =
+      fun s => T.sample.runAt n (T.index n r) s := by
+    funext s
+    obtain ⟨x, hx, -⟩ := (Collection.evalSampled_iff _).1 T.toCollection.evalSampled n r s
+    rw [hx, Option.getD_some, ((Collection.decD_eq_some_iff _).1 hx).symm]
+  rw [eA] at hA
+  rw [eC] at hC
+  have hB : StatClose (fun x => T.encD (T.index n r) (T.perm (T.index n r) x))
+      (fun x => T.encD (T.index n r) x) 0 :=
+    (StatClose.refl fun x => T.encD (T.index n r) x).comp_equiv_left (T.perm (T.index n r))
+  exact ((hA.trans hB).trans hC.symm).mono (by linarith)
+
+/-- **Alice's real sampler on typed coins**: on `(r, s₁, s₂)` (`realCoins`), it is
+`⟨⟨⟨1^n, a⟩, ⟨r, [y, []]⟩⟩, [a_b]⟩` with `y = ⟨eval ⟨i, w₁⟩, w₂⟩` (`⟨w₂, eval ⟨i, w₁⟩⟩` if `b`),
+`i = index n r` and `w_j = Sample(i; s_j)`. -/
+theorem realA_realCoins {π : Protocol} (hπ : IsOT T H π)
+    (hout : ∀ x (a : Fin 2 → Bool) (b : Fin 1 → Bool) (r : π.ExecCoins π.P x),
+      π.outV π.P x (List.ofFn a) (List.ofFn b) r = [a (if b 0 then 1 else 0)])
+    (n : ℕ) (a : Fin (otFunctionality.inA.eval n) → Bool)
+    (b : Fin (otFunctionality.inB.eval n) → Bool)
+    (p : T.gen.Coins n × (T.sample.Coins n × T.sample.Coins n)) :
+    otFunctionality.realA π n a b ((realCoins T H hπ n).symm p) =
+      pairEncode (pairEncode (pairEncode (List.replicate n true) (List.ofFn a))
+        (pairEncode (List.ofFn p.1)
+          (pairEncode
+            (if inB1 b 0 then
+              pairEncode (T.sample.runAt n (T.index n p.1) p.2.2)
+                (T.eval (pairEncode (T.index n p.1) (T.sample.runAt n (T.index n p.1) p.2.1)))
+            else
+              pairEncode
+                (T.eval (pairEncode (T.index n p.1) (T.sample.runAt n (T.index n p.1) p.2.1)))
+                (T.sample.runAt n (T.index n p.1) p.2.2))
+            (pairEncode [] []))))
+        [inA2 a (if inB1 b 0 then 1 else 0)] := by
+  have hlen : (List.ofFn p.2.1).length = T.sample.coins.eval n := length_ofFn_coins _ n _
+  rw [Functionality.realA_eq, Protocol.viewP_eq, View.encode_mk, transcriptWith_isOT T H hπ,
+    ← ofFn_inA2 a, ← ofFn_inB1 b, hout, ofFn_inA2, ofFn_inB1, realCoins_symm_fst_ofFn,
+    realCoins_symm_snd_ofFn, receiverNext_single, List.length_replicate, List.take_left' hlen,
+    List.drop_left' hlen, ofFn_eq_inB1, List.headD_cons, ← NUPPT.runAt_eq, ← NUPPT.runAt_eq,
+    ← NUPPT.runAt_eq, ← Collection.index_eq, Strategy.encodeMsgs_cons, Strategy.encodeMsgs_cons,
+    Strategy.encodeMsgs_nil]
+
+/-- **Alice's ideal sampler on typed coins**: on `(r, s₁, s₂)` (`simACoins`), it is
+`⟨⟨⟨1^n, a⟩, ⟨r, [⟨w₁, w₂⟩, []]⟩⟩, [a_b]⟩` with `w_j = Sample(index n r; s_j)`. -/
+theorem idealA_simACoins {S : NUPPT} (hS : IsSimA T S) (n : ℕ)
+    (a : Fin (otFunctionality.inA.eval n) → Bool) (b : Fin (otFunctionality.inB.eval n) → Bool)
+    (p : T.gen.Coins n × (T.sample.Coins n × T.sample.Coins n)) :
+    otFunctionality.idealA S n a b ((simACoins T hS n).symm p) =
+      pairEncode (pairEncode (pairEncode (List.replicate n true) (List.ofFn a))
+        (pairEncode (List.ofFn p.1)
+          (pairEncode (pairEncode (T.sample.runAt n (T.index n p.1) p.2.1)
+              (T.sample.runAt n (T.index n p.1) p.2.2))
+            (pairEncode [] []))))
+        [inA2 a (if inB1 b 0 then 1 else 0)] := by
+  rw [Functionality.idealA_eq, ((isSimA_iff T S).1 hS).2, simACoins_symm_ofFn, simAView_layout,
+    pairFstD_pairEncode, ofFn_f_snd]
+
+/-- **Alice's side of Proposition 161.5** [PS10]: for a protocol of the shape of Protocol 160.4
+(with Bob's output `[a_b]`, `hout`), a machine of `S_A`'s shape and a sampler within `δ` of
+uniform, every distinguisher's advantage between Alice's real and ideal samplers is at most
+`2δ(n)`: `distAdv (realA π n a b) (idealA S n a b) (D.distinguisherL n) ≤ 2 * δ n`.
+
+**Proof sketch.** Relabel both coin spaces as `Coins_Gen × (Coins_Sample × Coins_Sample)`
+(`acceptProb_comp_equiv`). The samplers are then `W r (y_real)` and `W r (y_sim)` for one map
+`W` (`realA_realCoins`, `idealA_simACoins`). For each `r`, `y_real` is `2δ(n)`-close to `y_sim`:
+`StatClose.prod` of `statClose_eval_sample` with the identical raw sample (after swapping the two
+sample blocks when `b`). So the joint samplers are `2δ(n)`-close (`statClose_prod_of_forall`,
+`StatClose.map`), and `distAdv_le_of_statClose` concludes. -/
+theorem distAdv_realA_idealA_le {π : Protocol} (hπ : IsOT T H π)
+    (hout : ∀ x (a : Fin 2 → Bool) (b : Fin 1 → Bool) (r : π.ExecCoins π.P x),
+      π.outV π.P x (List.ofFn a) (List.ofFn b) r = [a (if b 0 then 1 else 0)])
+    {S : NUPPT} (hS : IsSimA T S) {δ : ℕ → ℝ} (hδ : T.SampleClose δ) (D : NUPPT) (n : ℕ)
+    (a : Fin (otFunctionality.inA.eval n) → Bool) (b : Fin (otFunctionality.inB.eval n) → Bool) :
+    distAdv (otFunctionality.realA π n a b) (otFunctionality.idealA S n a b)
+      (D.distinguisherL n) ≤ 2 * δ n := by
+  have h0 : 0 ≤ 2 * δ n := by
+    have := ((Collection.sampleClose_iff _ _).1 hδ n fun _ => false).nonneg
+    linarith
+  rw [distAdv_def, ← acceptProb_comp_equiv (realCoins T H hπ n).symm,
+    ← acceptProb_comp_equiv (simACoins T hS n).symm, ← distAdv_def]
+  simp only [realA_realCoins T H hπ hout, idealA_simACoins T hS]
+  refine distAdv_le_of_statClose _ _ ?_ _
+  -- the per-index closeness of Bob's message
+  have hY : ∀ r : T.gen.Coins n, StatClose
+      (fun s : T.sample.Coins n × T.sample.Coins n =>
+        if inB1 b 0 then
+          pairEncode (T.sample.runAt n (T.index n r) s.2)
+            (T.eval (pairEncode (T.index n r) (T.sample.runAt n (T.index n r) s.1)))
+        else
+          pairEncode (T.eval (pairEncode (T.index n r) (T.sample.runAt n (T.index n r) s.1)))
+            (T.sample.runAt n (T.index n r) s.2))
+      (fun s : T.sample.Coins n × T.sample.Coins n =>
+        pairEncode (T.sample.runAt n (T.index n r) s.1) (T.sample.runAt n (T.index n r) s.2))
+      (2 * δ n) := by
+    intro r
+    have he := statClose_eval_sample T hδ n r
+    have hs := StatClose.refl fun s : T.sample.Coins n => T.sample.runAt n (T.index n r) s
+    cases hb : inB1 b 0
+    · have h := (he.prod hs).map fun q : List Bool × List Bool => pairEncode q.1 q.2
+      simpa only [Bool.false_eq_true, if_false, add_zero] using h
+    · have h := ((hs.prod he).map fun q : List Bool × List Bool =>
+        pairEncode q.1 q.2).comp_equiv_left (Equiv.prodComm (T.sample.Coins n) (T.sample.Coins n))
+      simpa only [if_true, zero_add, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap] using h
+  exact (statClose_prod_of_forall h0 hY).map fun q : T.gen.Coins n × List Bool =>
+    pairEncode (pairEncode (pairEncode (List.replicate n true) (List.ofFn a))
+      (pairEncode (List.ofFn q.1) (pairEncode q.2 (pairEncode [] []))))
+      [inA2 a (if inB1 b 0 then 1 else 0)]
+
+end TCSlib.Cryptography.SecureComputation.OT
diff --git a/TCSlib/Cryptography/SecureComputation/ObliviousTransfer/ViewB.lean b/TCSlib/Cryptography/SecureComputation/ObliviousTransfer/ViewB.lean
new file mode 100644
index 000000000..cc9a78b81
--- /dev/null
+++ b/TCSlib/Cryptography/SecureComputation/ObliviousTransfer/ViewB.lean
@@ -0,0 +1,545 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.SecureComputation.ObliviousTransfer.ViewA
+import TCSlib.Cryptography.SecureComputation.ObliviousTransfer.Predictor
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Oblivious transfer: Bob's side of Proposition 161.5
+
+Bob's real view of Protocol 160.4 differs from `S_B`'s only in the unselected mask:
+`z_{1−b} = h(f_i⁻¹(y_{1−b})) ⊕ a_{1−b}` in the real view, a fresh coin in the simulated one
+[PS10, Proposition 161.5, the proof left as an exercise]. Both are `OT.bobView` with the
+unselected mask `β ⊕ a_{1−b}`, where `β = h(f_i⁻¹(y_{1−b}))` (real) or `β` is uniform
+(simulated). Writing `P(β)` for `D`'s acceptance probability, the real one is `E_r P(B)`, the
+simulated one `E_r (P(B) + P(¬B))/2`, so the advantage is `|E_r P(B) − E_r P(¬B)| / 2`. The
+signed predictor (`uprob_signedPredictor_false`, `_true`) run on the view-building distinguisher
+`D'` (`OT.viewDist`) predicts `B` from `⟨i, s'⟩` with probability `1/2 ± (P(B) − P(¬B))/2`, so the
+enhanced hard-core hypothesis bounds the advantage by `|ε_false(n)| + |ε_true(n)|` for the fixed
+bits `(b, a₀, a₁)`. The eight choices of these bits give sixteen machines; the sum of their
+bounds is negligible and uniform over the inputs.
+
+## Main definitions
+
+* `OT.hcBit`: the enhanced hard-core bit `h_i(f_i⁻¹(Sample(i; s)))` of a sampled element.
+* `OT.accB`: `D`'s acceptance probability of Bob's view with a given unselected bit.
+
+## Main results
+
+* `OT.uprob_signedPredictor_false`, `OT.uprob_signedPredictor_true`: the signed-predictor
+  identity of Algorithm 104.3's proof for a uniform challenge `x` and a bit `B x`.
+* `OT.uprob_xor_shear`, `OT.negligible_finset_sum`: a uniform bit masked by a fixed bit, and
+  finite sums of negligible functions.
+* `OT.mask_eval`, `OT.mask_raw`: Alice's two masks on Bob's real pair.
+* `OT.realB_realCoins`, `OT.idealB_simBCoins`: Bob's real and ideal samplers on typed coins;
+  `OT.acceptProb_realB`, `OT.acceptProb_idealB`: their acceptance probabilities through `accB`.
+* `OT.acceptProb_viewDist`, `OT.uprob_predictor_false`, `OT.uprob_predictor_true`: the
+  prediction experiments of the two predictors.
+* `OT.distAdv_realB_idealB_le`, `OT.exists_negligible_bob`: the bound on Bob's side.
+* `OT.simulators_of_isOT`: Proposition 161.5 with its simulators, for every protocol and pair of
+  machines of the shapes of Protocol 160.4 and of `S_A`, `S_B`.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §6.2.4, Proposition 161.5, and Theorem 104.4 (the predictor), book pp. 104, 161–162.
+* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2*, Cambridge University Press,
+  2004, §7.3.2 (the enhanced predicate in the OT argument).
+-/
+
+namespace TCSlib.Cryptography.SecureComputation.OT
+
+open Complexity Turing TCSlib.Cryptography
+
+variable (T : TrapdoorCollection) (H : List Bool → List Bool)
+
+/-! ### The signed predictor -/
+
+/-- **The signed predictor, unflipped** (the identity behind [PS10, Theorem 104.4, proof], for a
+uniform challenge `x` and a bit `B x`): drawing `c` and coins `ρ`, outputting `c` if `D(x, c; ρ)`
+accepts and `¬c` otherwise, predicts `B x` with probability
+`1/2 + (Pr[D(x, B x) = 1] − Pr[D(x, ¬B x) = 1]) / 2`.
+
+**Proof sketch.** Substitute `c = d ⊕ B x` (a bijection of `Bool × (α × ρ)`) and split on `d`
+(`uprob_bool_prod`): for `d = 0` the prediction is right iff `D(x, B x)` accepts, for `d = 1` iff
+`D(x, ¬B x)` rejects (`uprob_not`). -/
+theorem uprob_signedPredictor_false {α ρ : Type*} [Fintype α] [Fintype ρ] [Nonempty α]
+    [Nonempty ρ] (B : α → Bool) (D : α × Bool → ρ → Bool) :
+    uprob (fun z : α × (Bool × ρ) =>
+        xor (if D (z.1, z.2.1) z.2.2 then z.2.1 else !z.2.1) false = B z.1) =
+      1 / 2 + (acceptProb (fun x => (x, B x)) D - acceptProb (fun x => (x, !B x)) D) / 2 := by
+  let e : Bool × (α × ρ) ≃ α × (Bool × ρ) :=
+    { toFun := fun v => (v.2.1, (xor v.1 (B v.2.1), v.2.2))
+      invFun := fun z => (xor z.2.1 (B z.1), (z.1, z.2.2))
+      left_inv := fun v => by simp
+      right_inv := fun z => by simp }
+  rw [← uprob_comp_equiv e, uprob_bool_prod, acceptProb_def, acceptProb_def,
+    show ∀ a b : ℝ, 1 / 2 + (a - b) / 2 = (a + (1 - b)) / 2 by intro a b; ring, ← uprob_not]
+  congr 2
+  · congr 1
+    funext w
+    apply propext
+    simp only [e, Equiv.coe_fn_mk, Bool.false_xor, Bool.xor_false]
+    cases D (w.1, B w.1) w.2 <;> cases B w.1 <;> simp
+  · congr 1
+    funext w
+    apply propext
+    simp only [e, Equiv.coe_fn_mk, Bool.true_xor, Bool.xor_false]
+    cases D (w.1, !B w.1) w.2 <;> cases B w.1 <;> simp
+
+/-- **The signed predictor, flipped**: the same predictor negated predicts `B x` with probability
+`1/2 − (Pr[D(x, B x) = 1] − Pr[D(x, ¬B x) = 1]) / 2`.
+
+**Proof sketch.** As `uprob_signedPredictor_false`: substitute `c = d ⊕ B x` and split on `d`.
+With the output negated, for `d = 0` the prediction is right iff `D(x, B x)` rejects
+(`uprob_not`), and for `d = 1` iff `D(x, ¬B x)` accepts. -/
+theorem uprob_signedPredictor_true {α ρ : Type*} [Fintype α] [Fintype ρ] [Nonempty α]
+    [Nonempty ρ] (B : α → Bool) (D : α × Bool → ρ → Bool) :
+    uprob (fun z : α × (Bool × ρ) =>
+        xor (if D (z.1, z.2.1) z.2.2 then z.2.1 else !z.2.1) true = B z.1) =
+      1 / 2 - (acceptProb (fun x => (x, B x)) D - acceptProb (fun x => (x, !B x)) D) / 2 := by
+  let e : Bool × (α × ρ) ≃ α × (Bool × ρ) :=
+    { toFun := fun v => (v.2.1, (xor v.1 (B v.2.1), v.2.2))
+      invFun := fun z => (xor z.2.1 (B z.1), (z.1, z.2.2))
+      left_inv := fun v => by simp
+      right_inv := fun z => by simp }
+  rw [← uprob_comp_equiv e, uprob_bool_prod, acceptProb_def, acceptProb_def,
+    show ∀ a b : ℝ, 1 / 2 - (a - b) / 2 = ((1 - a) + b) / 2 by intro a b; ring, ← uprob_not]
+  congr 2
+  · congr 1
+    funext w
+    apply propext
+    simp only [e, Equiv.coe_fn_mk, Bool.false_xor, Bool.xor_true]
+    cases D (w.1, B w.1) w.2 <;> cases B w.1 <;> simp
+  · congr 1
+    funext w
+    apply propext
+    simp only [e, Equiv.coe_fn_mk, Bool.true_xor, Bool.xor_true]
+    cases D (w.1, !B w.1) w.2 <;> cases B w.1 <;> simp
+
+/-- **A uniform bit masked by a fixed bit, re-centred on `g x`**: over uniform `(β, x)`,
+`Pr[Q (β ⊕ a) x] = (Pr[Q (g x) x] + Pr[Q (¬g x) x]) / 2` (the bijection `β ↦ β ⊕ a ⊕ g x`, then
+`uprob_bool_prod`). -/
+theorem uprob_xor_shear {X : Type*} [Fintype X] (g : X → Bool) (a : Bool) (Q : Bool → X → Prop) :
+    uprob (fun w : Bool × X => Q (xor w.1 a) w.2) =
+      (uprob (fun x => Q (g x) x) + uprob (fun x => Q (!g x) x)) / 2 := by
+  let e : Bool × X ≃ Bool × X :=
+    { toFun := fun w => (xor (xor w.1 (g w.2)) a, w.2)
+      invFun := fun w => (xor (xor w.1 a) (g w.2), w.2)
+      left_inv := fun w => by simp
+      right_inv := fun w => by simp }
+  rw [← uprob_comp_equiv e, uprob_bool_prod]
+  congr 2 <;> congr 1 <;> funext x <;> simp only [e, Equiv.coe_fn_mk] <;> cases g x <;>
+    cases a <;> rfl
+
+/-- **A finite sum of negligible functions is negligible** (`Negligible.add` by induction on the
+finite set): `(∀ i ∈ s, Negligible (f i)) → Negligible (fun n => ∑ i ∈ s, f i n)`. -/
+theorem negligible_finset_sum {ι : Type*} (s : Finset ι) {f : ι → ℕ → ℝ}
+    (h : ∀ i ∈ s, Negligible (f i)) : Negligible fun n => ∑ i ∈ s, f i n := by
+  classical
+  induction s using Finset.induction_on with
+  | empty => simpa using negligible_zero
+  | insert i s hi ih =>
+    simp_rw [Finset.sum_insert hi]
+    exact (h i (Finset.mem_insert_self i s)).add
+      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
+
+/-! ### The enhanced bit and the two masks -/
+
+/-- **The enhanced hard-core bit of a sampled element** [Gol04, §7.3.2]: at the index
+`i = index n r`, `hcBit T h n r s = h_i(perm_i⁻¹(dec_i(Sample(i; s))))`. -/
+def hcBit (h : ∀ i, T.D i → Bool) (n : ℕ) (r : T.gen.Coins n) (s : T.sample.Coins n) : Bool :=
+  h (T.index n r) ((T.perm (T.index n r)).symm
+    ((T.decD (T.index n r) (T.sample.runAt n (T.index n r) s)).getD default))
+
+/-- The defining equation of `hcBit`: `hcBit T h n r s =
+h_i (perm_i⁻¹ ((dec_i (Sample(i; s))).getD default))` with `i = index n r`. -/
+theorem hcBit_eq (h : ∀ i, T.D i → Bool) (n : ℕ) (r : T.gen.Coins n) (s : T.sample.Coins n) :
+    hcBit T h n r s = h (T.index n r) ((T.perm (T.index n r)).symm
+      ((T.decD (T.index n r) (T.sample.runAt n (T.index n r) s)).getD default)) := rfl
+
+/-- **The inverter on the all-`true` tape** [PS10, Definition 56.1 (6)]:
+`Inv(1^n, ⟨t, encD y⟩; 1^{inv(n)}) = encD (perm⁻¹ y)` (`TrapdoorCollection.inv_eq_encD`). -/
+theorem inv_runAtL_ones (n : ℕ) (r : T.gen.Coins n) (y : T.D (T.index n r)) :
+    T.inv.runAtL n (pairEncode (T.trap n r) (T.encD _ y))
+        (List.replicate (T.inv.coins.eval n) true) =
+      T.encD _ ((T.perm _).symm y) := by
+  rw [← NUPPT.coinLen_eq, ← List.ofFn_const, ← NUPPT.runAt_eq]
+  exact T.inv_eq_encD n r y fun _ => true
+
+/-- **The selected mask** [PS10, Protocol 160.4]: on `y_b = eval ⟨i, w⟩` with `w = Sample(i; s)`,
+Alice's mask is `H ⟨i, w⟩ ⊕ [c]` (the inverter returns `w`'s element, `H` is correct on it). -/
+theorem mask_eval {h : ∀ i, T.D i → Bool}
+    (henc : ∀ i (x : T.D i), H (pairEncode i (T.encD i x)) = [h i x]) (n : ℕ)
+    (r : T.gen.Coins n) (s : T.sample.Coins n) (c : Bool) :
+    mask T H n (T.index n r) (T.trap n r)
+        (T.eval (pairEncode (T.index n r) (T.sample.runAt n (T.index n r) s))) c =
+      List.zipWith xor (H (pairEncode (T.index n r) (T.sample.runAt n (T.index n r) s))) [c] := by
+  obtain ⟨x, hx, hev⟩ := (Collection.evalSampled_iff _).1 T.toCollection.evalSampled n r s
+  have hw : H (pairEncode (T.index n r) (T.sample.runAt n (T.index n r) s)) = [h _ x] :=
+    T.toCollection.apply_of_decD (v := fun i x => [h i x]) henc hx
+  rw [mask_eq, hev, T.f_perm, inv_runAtL_ones, Equiv.symm_apply_apply, henc, hw]
+
+/-- **The unselected mask** [PS10, Protocol 160.4]: on the raw sample `w' = Sample(i; s)`,
+Alice's mask is `[hcBit T h n r s ⊕ c]` (the inverter returns the encoding of
+`perm⁻¹(dec w')`). -/
+theorem mask_raw {h : ∀ i, T.D i → Bool}
+    (henc : ∀ i (x : T.D i), H (pairEncode i (T.encD i x)) = [h i x]) (n : ℕ)
+    (r : T.gen.Coins n) (s : T.sample.Coins n) (c : Bool) :
+    mask T H n (T.index n r) (T.trap n r) (T.sample.runAt n (T.index n r) s) c =
+      [xor (hcBit T h n r s) c] := by
+  obtain ⟨x, hx, -⟩ := (Collection.evalSampled_iff _).1 T.toCollection.evalSampled n r s
+  have hw : T.sample.runAt n (T.index n r) s = T.encD _ x :=
+    (Collection.decD_eq_some_iff _).1 hx
+  rw [mask_eq, hcBit_eq, hx, Option.getD_some, hw, inv_runAtL_ones, henc]
+  rfl
+
+/-! ### Bob's real and ideal samplers -/
+
+/-- Alice's input string is the two-bit list `[a₀, a₁]`:
+`List.ofFn (inA2 a) = [inA2 a 0, inA2 a 1]`. -/
+theorem ofFn_inA2_eq {n : ℕ} (a : Fin (otFunctionality.inA.eval n) → Bool) :
+    List.ofFn (inA2 a) = [inA2 a 0, inA2 a 1] := by
+  rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
+  rfl
+
+/-- **Bob's real sampler on typed coins**: on `(r, s₁, s₂)` (`realCoins`) it is
+`bobView (1^n) b a₀ a₁ i (s₁ ++ s₂) (Sample(i; s₁)) (hcBit T h n r s₂)` with `i = index n r`.
+
+**Proof sketch.** Unfold the real sampler to the transcript (`transcriptWith_isOT`) on the
+assembled tapes (`realCoins_symm_fst_ofFn`, `realCoins_symm_snd_ofFn`), with Alice's output `[]`
+(`houtP`). Then cases on `b`: the selected mask is `mask_eval`, the unselected one `mask_raw`. -/
+theorem realB_realCoins {h : ∀ i, T.D i → Bool}
+    (henc : ∀ i (x : T.D i), H (pairEncode i (T.encD i x)) = [h i x]) {π : Protocol}
+    (hπ : IsOT T H π)
+    (houtP : ∀ x (a : Fin 2 → Bool) (b : Fin 1 → Bool) (r : π.ExecCoins π.P x),
+      π.outP x (List.ofFn a) (List.ofFn b) r = [])
+    (n : ℕ) (a : Fin (otFunctionality.inA.eval n) → Bool)
+    (b : Fin (otFunctionality.inB.eval n) → Bool)
+    (p : T.gen.Coins n × (T.sample.Coins n × T.sample.Coins n)) :
+    otFunctionality.realB π n a b ((realCoins T H hπ n).symm p) =
+      bobView H (List.replicate n true) (inB1 b 0) (inA2 a 0) (inA2 a 1) (T.index n p.1)
+        (List.ofFn p.2.1 ++ List.ofFn p.2.2) (T.sample.runAt n (T.index n p.1) p.2.1)
+        (hcBit T h n p.1 p.2.2) := by
+  have hlen : (List.ofFn p.2.1).length = T.sample.coins.eval n := length_ofFn_coins _ n _
+  rw [Functionality.realB_eq, Protocol.viewV_eq, View.encode_mk, transcriptWith_isOT T H hπ,
+    ← ofFn_inA2 a, ← ofFn_inB1 b, houtP, ofFn_inB1, ofFn_eq_inB1, ofFn_inA2_eq,
+    realCoins_symm_fst_ofFn, realCoins_symm_snd_ofFn, senderNext_single, receiverNext_single,
+    List.length_replicate, List.take_left' hlen, List.drop_left' hlen, List.headD_cons,
+    ← NUPPT.runAt_eq, ← NUPPT.runAt_eq, ← NUPPT.runAt_eq, ← Collection.index_eq,
+    ← Collection.trap_eq, Strategy.encodeMsgs_cons, Strategy.encodeMsgs_cons,
+    Strategy.encodeMsgs_cons, Strategy.encodeMsgs_nil, bobView_eq]
+  cases inB1 b 0
+  · simp only [Bool.false_eq_true, if_false, pairFstD_pairEncode, pairSndD_pairEncode,
+      mask_eval T H henc, mask_raw T H henc, List.getD_cons_zero, List.getD_cons_succ]
+  · simp only [if_true, pairFstD_pairEncode, pairSndD_pairEncode,
+      mask_eval T H henc, mask_raw T H henc, List.getD_cons_zero, List.getD_cons_succ]
+
+/-- **Bob's ideal sampler on typed coins**: on `(r, s₁, s₂, c)` (`simBCoins`) it is
+`bobView (1^n) b a₀ a₁ i (s₁ ++ s₂) (Sample(i; s₁)) (c ⊕ a_{1−b})` with `i = index n r`. -/
+theorem idealB_simBCoins {S : NUPPT} (hS : IsSimB T H S) (n : ℕ)
+    (a : Fin (otFunctionality.inA.eval n) → Bool) (b : Fin (otFunctionality.inB.eval n) → Bool)
+    (p : T.gen.Coins n × (T.sample.Coins n × (T.sample.Coins n × (Fin 1 → Bool)))) :
+    otFunctionality.idealB S n a b ((simBCoins T H hS n).symm p) =
+      bobView H (List.replicate n true) (inB1 b 0) (inA2 a 0) (inA2 a 1) (T.index n p.1)
+        (List.ofFn p.2.1 ++ List.ofFn p.2.2.1) (T.sample.runAt n (T.index n p.1) p.2.1)
+        (xor (p.2.2.2 0) (if inB1 b 0 then inA2 a 0 else inA2 a 1)) := by
+  have hc : List.ofFn p.2.2.2 = [p.2.2.2 0] := by rw [List.ofFn_succ, List.ofFn_zero]
+  rw [Functionality.idealB_eq, ((isSimB_iff T H S).1 hS).2, simBCoins_symm_ofFn, simBView_layout,
+    pairFstD_pairEncode, pairSndD_pairEncode, ofFn_f_snd, ofFn_f_fst, ofFn_eq_inB1,
+    List.headD_cons, hc, bobView_eq]
+  cases inB1 b 0 <;> simp
+
+/-! ### Acceptance probabilities -/
+
+/-- `D`'s acceptance probability of Bob's view at the index of `r` with the unselected bit
+`g(s₂)`: `accB T H D n b a₀ a₁ r g = Pr_{s₁, s₂, ρ}[D(bobView … (s₁ ++ s₂) (Sample(i; s₁))
+(g s₂); ρ) = 1]`. -/
+noncomputable def accB (D : NUPPT) (n : ℕ) (b a₀ a₁ : Bool) (r : T.gen.Coins n)
+    (g : T.sample.Coins n → Bool) : ℝ :=
+  uprob fun q : (T.sample.Coins n × T.sample.Coins n) × D.Coins n =>
+    D.distinguisherL n (bobView H (List.replicate n true) b a₀ a₁ (T.index n r)
+      (List.ofFn q.1.1 ++ List.ofFn q.1.2) (T.sample.runAt n (T.index n r) q.1.1) (g q.1.2))
+      q.2 = true
+
+/-- The defining equation of `accB`: `accB T H D n b a₀ a₁ r g =
+Pr_{((s₁, s₂), ρ)}[D(bobView … (s₁ ++ s₂) (Sample(i; s₁)) (g s₂); ρ) = 1]`. -/
+theorem accB_eq (D : NUPPT) (n : ℕ) (b a₀ a₁ : Bool) (r : T.gen.Coins n)
+    (g : T.sample.Coins n → Bool) :
+    accB T H D n b a₀ a₁ r g =
+      uprob fun q : (T.sample.Coins n × T.sample.Coins n) × D.Coins n =>
+        D.distinguisherL n (bobView H (List.replicate n true) b a₀ a₁ (T.index n r)
+          (List.ofFn q.1.1 ++ List.ofFn q.1.2) (T.sample.runAt n (T.index n r) q.1.1) (g q.1.2))
+          q.2 = true := rfl
+
+/-- **Bob's real acceptance** is the average over `Gen`'s coins of `accB` with the enhanced bit:
+`acceptProb realB D = E_r accB … r (hcBit T h n r)`. -/
+theorem acceptProb_realB {h : ∀ i, T.D i → Bool}
+    (henc : ∀ i (x : T.D i), H (pairEncode i (T.encD i x)) = [h i x]) {π : Protocol}
+    (hπ : IsOT T H π)
+    (houtP : ∀ x (a : Fin 2 → Bool) (b : Fin 1 → Bool) (r : π.ExecCoins π.P x),
+      π.outP x (List.ofFn a) (List.ofFn b) r = [])
+    (D : NUPPT) (n : ℕ) (a : Fin (otFunctionality.inA.eval n) → Bool)
+    (b : Fin (otFunctionality.inB.eval n) → Bool) :
+    acceptProb (otFunctionality.realB π n a b) (D.distinguisherL n) =
+      uexp fun r => accB T H D n (inB1 b 0) (inA2 a 0) (inA2 a 1) r (hcBit T h n r) := by
+  rw [← acceptProb_comp_equiv (realCoins T H hπ n).symm, acceptProb_def]
+  simp only [realB_realCoins T H henc hπ houtP]
+  rw [← uprob_comp_equiv (Equiv.prodAssoc _ _ _).symm, uprob_prod]
+  congr 1
+
+/-- **Bob's ideal acceptance** is the average of the two `accB` with the enhanced bit and its
+negation: `acceptProb idealB D = E_r (accB … r B + accB … r ¬B) / 2`.
+
+**Proof sketch.** Relabel the coins as `(r, s₁, s₂, c)` (`simBCoins`, `idealB_simBCoins`), reorder
+them as `(r, (c₀, ((s₁, s₂), ρ)))` by an explicit bijection `E` (`c` read as its bit `c₀`), average
+over `r` (`uprob_prod`), and apply `uprob_xor_shear` to the unselected bit `c₀ ⊕ a_{1−b}`,
+re-centred on `B(s₂)`. -/
+theorem acceptProb_idealB {h : ∀ i, T.D i → Bool} {S : NUPPT} (hS : IsSimB T H S) (D : NUPPT)
+    (n : ℕ) (a : Fin (otFunctionality.inA.eval n) → Bool)
+    (b : Fin (otFunctionality.inB.eval n) → Bool) :
+    acceptProb (otFunctionality.idealB S n a b) (D.distinguisherL n) =
+      uexp fun r => (accB T H D n (inB1 b 0) (inA2 a 0) (inA2 a 1) r (hcBit T h n r) +
+        accB T H D n (inB1 b 0) (inA2 a 0) (inA2 a 1) r (fun s => !hcBit T h n r s)) / 2 := by
+  let E : T.gen.Coins n × (Bool × ((T.sample.Coins n × T.sample.Coins n) × D.Coins n)) ≃
+      (T.gen.Coins n × (T.sample.Coins n × (T.sample.Coins n × (Fin 1 → Bool)))) × D.Coins n :=
+    { toFun := fun w => ((w.1, (w.2.2.1.1, (w.2.2.1.2, fun _ => w.2.1))), w.2.2.2)
+      invFun := fun z => (z.1.1, (z.1.2.2.2 0, ((z.1.2.1, z.1.2.2.1), z.2)))
+      left_inv := fun w => rfl
+      right_inv := fun z => by
+        obtain ⟨⟨r, s₁, s₂, c⟩, ρ⟩ := z
+        refine Prod.ext (Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (funext fun j => ?_)))) rfl
+        rw [Subsingleton.elim j 0] }
+  rw [← acceptProb_comp_equiv (simBCoins T H hS n).symm, acceptProb_def]
+  simp only [idealB_simBCoins T H hS]
+  rw [← uprob_comp_equiv E, uprob_prod]
+  congr 1
+  funext r
+  simp only [E, Equiv.coe_fn_mk]
+  rw [accB_eq, accB_eq]
+  have key := uprob_xor_shear
+    (fun q : (T.sample.Coins n × T.sample.Coins n) × D.Coins n => hcBit T h n r q.1.2)
+    (if inB1 b 0 then inA2 a 0 else inA2 a 1) fun β q =>
+      D.distinguisherL n (bobView H (List.replicate n true) (inB1 b 0) (inA2 a 0) (inA2 a 1)
+        (T.index n r) (List.ofFn q.1.1 ++ List.ofFn q.1.2)
+        (T.sample.runAt n (T.index n r) q.1.1) β) q.2 = true
+  exact key
+
+/-! ### The predictor machines -/
+
+/-- **`D'`'s acceptance on `⟨i, ⟨s', [g s']⟩⟩` is `accB`**: over uniform `s'` and `D'`'s coins,
+`D'` accepts `⟨i, ⟨s', [g s']⟩⟩` with probability `accB T H D n b a₀ a₁ r g` (`viewDistCoins`,
+`distinguisherL_viewDist`, and the reordering `(s₂, (s₁, ρ)) ↦ ((s₁, s₂), ρ)`):
+`acceptProb (fun x => (x, g x)) (fun yc ρ => D'.distinguisherL n ⟨i, ⟨ofFn yc.1, [yc.2]⟩⟩ ρ) =
+accB T H D n b a₀ a₁ r g` with `D' = viewDist T hH D b a₀ a₁` and `i = T.index n r`. -/
+theorem acceptProb_viewDist (hH : PolyTimeComputable H) (D : NUPPT) (n : ℕ) (b a₀ a₁ : Bool)
+    (r : T.gen.Coins n) (g : T.sample.Coins n → Bool) :
+    acceptProb (fun x : T.sample.Coins n => (x, g x))
+        (fun (yc : T.sample.Coins n × Bool) (ρ : (viewDist T hH D b a₀ a₁).Coins n) =>
+          (viewDist T hH D b a₀ a₁).distinguisherL n
+            (pairEncode (T.index n r) (pairEncode (List.ofFn yc.1) [yc.2])) ρ) =
+      accB T H D n b a₀ a₁ r g := by
+  let e : (T.sample.Coins n × T.sample.Coins n) × D.Coins n ≃
+      T.sample.Coins n × (viewDist T hH D b a₀ a₁).Coins n :=
+    { toFun := fun q => (q.1.2, (viewDistCoins T hH D b a₀ a₁ n).symm (q.1.1, q.2))
+      invFun := fun z => ((((viewDistCoins T hH D b a₀ a₁ n) z.2).1, z.1),
+        ((viewDistCoins T hH D b a₀ a₁ n) z.2).2)
+      left_inv := fun q => by simp
+      right_inv := fun z => by simp }
+  rw [acceptProb_def, accB_eq, ← uprob_comp_equiv e]
+  congr 1
+  funext q
+  simp only [e, Equiv.coe_fn_mk]
+  rw [distinguisherL_viewDist]
+
+/-- **The unflipped predictor's prediction experiment** at the index of `r`: the machine
+`tdpPredictor D' false` predicts `hcBit T h n r s'` from `⟨i, s'⟩` with probability
+`1/2 + (accB … r B − accB … r ¬B) / 2` (`uprob_tdpPredictor`, `uprob_signedPredictor_false`,
+`acceptProb_viewDist`): `uprob (fun z => P.distinguisherL n ⟨T.index n r, ofFn z.1⟩ z.2 = B z.1) =
+1 / 2 + (accB T H D n b a₀ a₁ r B - accB T H D n b a₀ a₁ r (fun s => !B s)) / 2` with
+`P = tdpPredictor (viewDist T hH D b a₀ a₁) false` and `B = hcBit T h n r`. -/
+theorem uprob_predictor_false (h : ∀ i, T.D i → Bool) (hH : PolyTimeComputable H) (D : NUPPT)
+    (n : ℕ) (b a₀ a₁ : Bool) (r : T.gen.Coins n) :
+    uprob (fun z : T.sample.Coins n × (tdpPredictor (viewDist T hH D b a₀ a₁) false).Coins n =>
+        (tdpPredictor (viewDist T hH D b a₀ a₁) false).distinguisherL n
+          (pairEncode (T.index n r) (List.ofFn z.1)) z.2 = hcBit T h n r z.1) =
+      1 / 2 + (accB T H D n b a₀ a₁ r (hcBit T h n r) -
+        accB T H D n b a₀ a₁ r (fun s => !hcBit T h n r s)) / 2 := by
+  have h₁ := uprob_tdpPredictor (viewDist T hH D b a₀ a₁) false n (T.index n r)
+    (id : T.sample.Coins n → T.sample.Coins n) (hcBit T h n r) List.ofFn
+  have h₂ := uprob_signedPredictor_false (hcBit T h n r)
+    (fun (yc : T.sample.Coins n × Bool) (ρ : (viewDist T hH D b a₀ a₁).Coins n) =>
+      (viewDist T hH D b a₀ a₁).distinguisherL n
+        (pairEncode (T.index n r) (pairEncode (List.ofFn yc.1) [yc.2])) ρ)
+  rw [acceptProb_viewDist T H hH D n b a₀ a₁ r (hcBit T h n r),
+    acceptProb_viewDist T H hH D n b a₀ a₁ r (fun s => !hcBit T h n r s)] at h₂
+  exact h₁.trans h₂
+
+/-- **The flipped predictor's prediction experiment**: `tdpPredictor D' true` predicts
+`hcBit T h n r s'` with probability `1/2 − (accB … r B − accB … r ¬B) / 2`:
+`uprob (fun z => P.distinguisherL n ⟨T.index n r, ofFn z.1⟩ z.2 = B z.1) =
+1 / 2 - (accB T H D n b a₀ a₁ r B - accB T H D n b a₀ a₁ r (fun s => !B s)) / 2` with
+`P = tdpPredictor (viewDist T hH D b a₀ a₁) true` and `B = hcBit T h n r`. -/
+theorem uprob_predictor_true (h : ∀ i, T.D i → Bool) (hH : PolyTimeComputable H) (D : NUPPT)
+    (n : ℕ) (b a₀ a₁ : Bool) (r : T.gen.Coins n) :
+    uprob (fun z : T.sample.Coins n × (tdpPredictor (viewDist T hH D b a₀ a₁) true).Coins n =>
+        (tdpPredictor (viewDist T hH D b a₀ a₁) true).distinguisherL n
+          (pairEncode (T.index n r) (List.ofFn z.1)) z.2 = hcBit T h n r z.1) =
+      1 / 2 - (accB T H D n b a₀ a₁ r (hcBit T h n r) -
+        accB T H D n b a₀ a₁ r (fun s => !hcBit T h n r s)) / 2 := by
+  have h₁ := uprob_tdpPredictor (viewDist T hH D b a₀ a₁) true n (T.index n r)
+    (id : T.sample.Coins n → T.sample.Coins n) (hcBit T h n r) List.ofFn
+  have h₂ := uprob_signedPredictor_true (hcBit T h n r)
+    (fun (yc : T.sample.Coins n × Bool) (ρ : (viewDist T hH D b a₀ a₁).Coins n) =>
+      (viewDist T hH D b a₀ a₁).distinguisherL n
+        (pairEncode (T.index n r) (pairEncode (List.ofFn yc.1) [yc.2])) ρ)
+  rw [acceptProb_viewDist T H hH D n b a₀ a₁ r (hcBit T h n r),
+    acceptProb_viewDist T H hH D n b a₀ a₁ r (fun s => !hcBit T h n r s)] at h₂
+  exact h₁.trans h₂
+
+/-! ### Bob's side -/
+
+/-- **Bob's side for fixed inputs**: if the two predictors `tdpPredictor D' false/true` for the
+bits `(b, a₀, a₁)` of the inputs predict the enhanced bit with probability at most `1/2 + ε_false`
+and `1/2 + ε_true` at `n`, then `D`'s advantage between Bob's real and ideal samplers is at most
+`|ε_false| + |ε_true|`:
+`distAdv (realB π n a b) (idealB S n a b) (D.distinguisherL n) ≤ |εf| + |εt|` under `hf`, `ht`.
+
+**Proof sketch.** With `U± = E_r accB … r (±B)`, the real acceptance is `U+`
+(`acceptProb_realB`) and the ideal one `(U+ + U−)/2` (`acceptProb_idealB`), so the advantage is
+`|U+ − U−| / 2`. The predictors give `U+ − U− ≤ 2ε_false` and `U− − U+ ≤ 2ε_true`
+(`uprob_predictor_false/true`, `uexp_half_add/sub`). -/
+theorem distAdv_realB_idealB_le {h : ∀ i, T.D i → Bool} (hH : PolyTimeComputable H)
+    (henc : ∀ i (x : T.D i), H (pairEncode i (T.encD i x)) = [h i x]) {π : Protocol}
+    (hπ : IsOT T H π)
+    (houtP : ∀ x (a : Fin 2 → Bool) (b : Fin 1 → Bool) (r : π.ExecCoins π.P x),
+      π.outP x (List.ofFn a) (List.ofFn b) r = [])
+    {S : NUPPT} (hS : IsSimB T H S) (D : NUPPT) (n : ℕ)
+    (a : Fin (otFunctionality.inA.eval n) → Bool) (b : Fin (otFunctionality.inB.eval n) → Bool)
+    {εf εt : ℝ}
+    (hf : uexp (fun r : T.gen.Coins n => uprob fun z : T.sample.Coins n ×
+        (tdpPredictor (viewDist T hH D (inB1 b 0) (inA2 a 0) (inA2 a 1)) false).Coins n =>
+      (tdpPredictor (viewDist T hH D (inB1 b 0) (inA2 a 0) (inA2 a 1)) false).distinguisherL n
+        (pairEncode (T.index n r) (List.ofFn z.1)) z.2 = hcBit T h n r z.1) ≤ 1 / 2 + εf)
+    (ht : uexp (fun r : T.gen.Coins n => uprob fun z : T.sample.Coins n ×
+        (tdpPredictor (viewDist T hH D (inB1 b 0) (inA2 a 0) (inA2 a 1)) true).Coins n =>
+      (tdpPredictor (viewDist T hH D (inB1 b 0) (inA2 a 0) (inA2 a 1)) true).distinguisherL n
+        (pairEncode (T.index n r) (List.ofFn z.1)) z.2 = hcBit T h n r z.1) ≤ 1 / 2 + εt) :
+    distAdv (otFunctionality.realB π n a b) (otFunctionality.idealB S n a b)
+      (D.distinguisherL n) ≤ |εf| + |εt| := by
+  simp only [uprob_predictor_false T H h hH D n, uprob_predictor_true T H h hH D n] at hf ht
+  rw [uexp_half_add] at hf
+  rw [uexp_half_sub] at ht
+  rw [distAdv_def, acceptProb_realB T H henc hπ houtP, acceptProb_idealB T H (h := h) hS,
+    show (fun r => (accB T H D n (inB1 b 0) (inA2 a 0) (inA2 a 1) r (hcBit T h n r) +
+        accB T H D n (inB1 b 0) (inA2 a 0) (inA2 a 1) r (fun s => !hcBit T h n r s)) / 2) =
+      fun r => (1 / 2 : ℝ) * (accB T H D n (inB1 b 0) (inA2 a 0) (inA2 a 1) r (hcBit T h n r) +
+        accB T H D n (inB1 b 0) (inA2 a 0) (inA2 a 1) r (fun s => !hcBit T h n r s)) from
+      funext fun r => by ring,
+    HardcoreBit.uexp_const_mul, HardcoreBit.uexp_add]
+  generalize uexp (fun r => accB T H D n (inB1 b 0) (inA2 a 0) (inA2 a 1) r (hcBit T h n r)) = U₁
+    at hf ht ⊢
+  generalize uexp (fun r => accB T H D n (inB1 b 0) (inA2 a 0) (inA2 a 1) r
+    (fun s => !hcBit T h n r s)) = U₂ at hf ht ⊢
+  have h₁ := le_abs_self εf
+  have h₂ := le_abs_self εt
+  have h₃ := abs_nonneg εf
+  have h₄ := abs_nonneg εt
+  rw [abs_le]
+  constructor <;> linarith
+
+/-- **Bob's side of Proposition 161.5** [PS10]: under the enhanced hard-core hypothesis (stated
+explicitly, `hEHC`), for every distinguisher `D` there is a negligible `ε ≥ 0` bounding `D`'s
+advantage between Bob's real and ideal samplers for all `n` and all inputs.
+
+**Proof sketch.** `hEHC` gives a negligible `ε_{t, fl}` for each of the sixteen predictors
+`tdpPredictor (viewDist D t) fl`, `t = (b, a₀, a₁)`, `fl ∈ {0, 1}`. Take
+`ε(n) = Σ_t Σ_fl |ε_{t, fl}(n)|` (negligible by `negligible_finset_sum`): for the inputs' bits
+`t`, `distAdv_realB_idealB_le` bounds the advantage by `|ε_{t, 0}(n)| + |ε_{t, 1}(n)| ≤ ε(n)`. -/
+theorem exists_negligible_bob {h : ∀ i, T.D i → Bool} (hH : PolyTimeComputable H)
+    (henc : ∀ i (x : T.D i), H (pairEncode i (T.encD i x)) = [h i x]) {π : Protocol}
+    (hπ : IsOT T H π)
+    (houtP : ∀ x (a : Fin 2 → Bool) (b : Fin 1 → Bool) (r : π.ExecCoins π.P x),
+      π.outP x (List.ofFn a) (List.ofFn b) r = [])
+    {S : NUPPT} (hS : IsSimB T H S)
+    (hEHC : ∀ A : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n,
+      uexp (fun r : T.gen.Coins n =>
+        uprob fun z : T.sample.Coins n × A.Coins n =>
+          A.distinguisherL n (pairEncode (T.index n r) (List.ofFn z.1)) z.2 =
+            h (T.index n r) ((T.perm (T.index n r)).symm
+              ((T.decD (T.index n r) (T.sample.runAt n (T.index n r) z.1)).getD default)))
+        ≤ 1 / 2 + ε n)
+    (D : NUPPT) :
+    ∃ ε : ℕ → ℝ, Negligible ε ∧ (∀ n, 0 ≤ ε n) ∧
+      ∀ n (a : Fin (otFunctionality.inA.eval n) → Bool)
+        (b : Fin (otFunctionality.inB.eval n) → Bool),
+        distAdv (otFunctionality.realB π n a b) (otFunctionality.idealB S n a b)
+          (D.distinguisherL n) ≤ ε n := by
+  choose ε hε hb using fun (t : Bool × Bool × Bool) (fl : Bool) =>
+    hEHC (tdpPredictor (viewDist T hH D t.1 t.2.1 t.2.2) fl)
+  refine ⟨fun n => ∑ t : Bool × Bool × Bool, ∑ fl : Bool, |ε t fl n|,
+    negligible_finset_sum _ fun t _ => negligible_finset_sum _ fun fl _ =>
+      (hε t fl).mono ⟨0, fun n _ => (abs_abs _).le⟩,
+    fun n => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _,
+    fun n a b => ?_⟩
+  refine (distAdv_realB_idealB_le T H hH henc hπ houtP hS D n a b
+    (hb (inB1 b 0, inA2 a 0, inA2 a 1) false n) (hb (inB1 b 0, inA2 a 0, inA2 a 1) true n)).trans ?_
+  have hsum : ∑ fl : Bool, |ε (inB1 b 0, inA2 a 0, inA2 a 1) fl n| =
+      |ε (inB1 b 0, inA2 a 0, inA2 a 1) false n| + |ε (inB1 b 0, inA2 a 0, inA2 a 1) true n| := by
+    rw [Fintype.sum_bool, add_comm]
+  rw [← hsum]
+  exact Finset.single_le_sum (f := fun t => ∑ fl : Bool, |ε t fl n|)
+    (fun t _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ _)
+
+/-- **Proposition 161.5 with its simulators** [PS10], for every protocol of the shape of
+Protocol 160.4 (with Bob's output `[a_b]` and Alice's `[]`) and every pair of machines of the
+shapes of `S_A` and `S_B`: for a collection of one-way trapdoor permutations with an enhanced
+hard-core predicate (`hEHC`, explicit) evaluated on encodings by `H`, each distinguisher has
+a negligible `ε` bounding both advantages for all `n` and all inputs:
+`∀ D, ∃ ε, Negligible ε ∧ ∀ n x y, distAdv (realA π n x y) (idealA SA n x y) (D.distinguisherL n)
+≤ ε n ∧ distAdv (realB π n x y) (idealB SB n x y) (D.distinguisherL n) ≤ ε n`.
+
+**Proof sketch.** `T.OneWay` gives a negligible `δ` with `SampleClose δ`. Alice's side is at
+most `2δ(n)` (`distAdv_realA_idealA_le`), Bob's at most a negligible `ε_B(n) ≥ 0`
+(`exists_negligible_bob`). Take `ε(n) = 2|δ(n)| + ε_B(n)`. -/
+theorem simulators_of_isOT {h : ∀ i, T.D i → Bool} (hH : PolyTimeComputable H)
+    (henc : ∀ i (x : T.D i), H (pairEncode i (T.encD i x)) = [h i x]) {π : Protocol}
+    (hπ : IsOT T H π)
+    (houtV : ∀ x (a : Fin 2 → Bool) (b : Fin 1 → Bool) (r : π.ExecCoins π.P x),
+      π.outV π.P x (List.ofFn a) (List.ofFn b) r = [a (if b 0 then 1 else 0)])
+    (houtP : ∀ x (a : Fin 2 → Bool) (b : Fin 1 → Bool) (r : π.ExecCoins π.P x),
+      π.outP x (List.ofFn a) (List.ofFn b) r = [])
+    {SA SB : NUPPT} (hSA : IsSimA T SA) (hSB : IsSimB T H SB) (hT : T.OneWay)
+    (hEHC : ∀ A : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n,
+      uexp (fun r : T.gen.Coins n =>
+        uprob fun z : T.sample.Coins n × A.Coins n =>
+          A.distinguisherL n (pairEncode (T.index n r) (List.ofFn z.1)) z.2 =
+            h (T.index n r) ((T.perm (T.index n r)).symm
+              ((T.decD (T.index n r) (T.sample.runAt n (T.index n r) z.1)).getD default)))
+        ≤ 1 / 2 + ε n) :
+    ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
+      ∀ n (x : Fin (otFunctionality.inA.eval n) → Bool)
+        (y : Fin (otFunctionality.inB.eval n) → Bool),
+        distAdv (otFunctionality.realA π n x y) (otFunctionality.idealA SA n x y)
+            (D.distinguisherL n) ≤ ε n ∧
+          distAdv (otFunctionality.realB π n x y) (otFunctionality.idealB SB n x y)
+            (D.distinguisherL n) ≤ ε n := by
+  obtain ⟨δ, hδ, hδS⟩ := ((TrapdoorCollection.oneWay_iff T).1 hT).sampleClose
+  intro D
+  obtain ⟨εB, hεB, h0, hB⟩ := exists_negligible_bob T H hH henc hπ houtP hSB hEHC D
+  refine ⟨fun n => 2 * |δ n| + εB n,
+    ((hδ.mono ⟨0, fun n _ => (abs_abs _).le⟩).const_mul 2).add hεB, fun n x y => ⟨?_, ?_⟩⟩
+  · have hA := distAdv_realA_idealA_le T H hπ houtV hSA hδS D n x y
+    have := le_abs_self (δ n)
+    have := h0 n
+    linarith
+  · have := hB n x y
+    have := abs_nonneg (δ n)
+    linarith
+
+end TCSlib.Cryptography.SecureComputation.OT

## ===== TCSlib/Cryptography/SecureComputation/ObliviousTransfer.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Defs
import TCSlib.Cryptography.Asymptotic.Collections
import TCSlib.Cryptography.SecureComputation.ObliviousTransfer.Shape
import TCSlib.Cryptography.SecureComputation.ObliviousTransfer.Efficiency
import TCSlib.Cryptography.SecureComputation.ObliviousTransfer.Simulators
import TCSlib.Cryptography.SecureComputation.ObliviousTransfer.ViewA
import TCSlib.Cryptography.SecureComputation.ObliviousTransfer.Predictor
import TCSlib.Cryptography.SecureComputation.ObliviousTransfer.ViewB

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Oblivious transfer from trapdoor permutations

[PS10, Protocol 160.4]: for a collection of trapdoor permutations `{f_i}` with a hard-core
predicate `h`,
- Alice (sender, input `a₁, a₂`) runs `(i, t) ← Gen(1^n)` and sends `i`;
- Bob (receiver, input `b`) samples `x`, sets `y_b = f_i(x)` and `y_{1−b}` a random element, and
  sends `(y₁, y₂)`;
- Alice sends `z_j = h(f_i^{-1}(y_j)) ⊕ a_j` for `j = 1, 2`;
- Bob outputs `h(x) ⊕ z_b`.

[PS10, Proposition 161.5]: the protocol is an honest-but-curious one-out-of-two oblivious transfer
(Definition 155.1 for `otFunctionality`).

**On the ch. 2–4 layer.** The collection is a `TrapdoorCollection`, used as Algorithm 104.3 uses it.
`Gen` uses Alice's fresh generator coins, and the two domain samples use separate fresh blocks
of Bob's tape. The evaluator `eval` is deterministic. Only the trapdoor inverter uses a fixed
all-`true` tape, justified by its correctness on every inverter tape. The hard-core predicate
is evaluated by a polynomial-time `H`, specified by
`H ⟨i, encD i x⟩ = [h i x]` on canonical encodings. Canonical decoding extends this specification
to every string decoding to `x` (`Collection.apply_of_decD`). The evaluator and its polynomial
cost are passed explicitly, so this module needs only `Asymptotic/Collections`.

**Deviations and source notes.**
- **Five messages.** The ch. 2–4 model (D8) reads a party's output as its next-message function
  on its complete history, so the last mover's last message is its output. With the source's
  three messages Alice would move last and output `(z₁, z₂)`, not `⊥`. Two empty messages are
  added (Bob, then Alice), so Alice's output is `[]` (the empty `⊥` of `otFunctionality`) and
  Bob's is computed on his complete history `[i, (z₁, z₂), []]`.
- **The source's typo:** Alice sends `(z₁, z₂)`, not `(z₁, …, z₄)` (inventory Prot-160.4).
- **Random elements, not random strings.** The source's `y_j ← {0,1}^n` becomes the collection's
  domain sampler, as in Algorithm 104.3. `y_b = f_i(x) = encD (perm x)` is a canonical encoding.
  `y_{1−b}` must be one too, or Alice tells the two apart and learns `b`. Canonical decoding and
  the sampler contract guarantee this (`Collection.sample_eq_encD`, stated here as the theorem
  `SamplerCanonical`).
- **An enhanced hard-core predicate** (gate 03b review; ruling of 2026-11-05). `y_{1−b}` is a
  raw sample, and Bob's view holds the coins that produced it. If the sampler computes its
  output as `f_i(u)` from a uniform `u`, those coins reveal `u = f_i⁻¹(y_{1−b})` and so
  `a_{1−b}`; the hard-core property of [PS10] (from `⟨i, f_i(u)⟩` alone) does not exclude this,
  and the proposition is not provable under it. Proposition 161.5 therefore assumes that `h` is
  **enhanced** hard-core (`EnhancedHardCore`): unpredictable on the preimage of a sampled element
  even given the sampler's coins. Enhanced inversion is motivated in [Gol04, Appendix C.1];
  the predicate and OT argument are in [Gol04, §7.3.2]. The Boolean prediction experiment here
  is an explicit hypothesis, not a literal transcription of the inversion condition C.1.1.

## Main definitions

* `SecureComputation.otSender`, `otReceiver`, `otProtocol`: Protocol 160.4.
* `SecureComputation.otSimA`, `otSimB`: the simulators of Proposition 161.5.
* `SecureComputation.EnhancedHardCore`: an enhanced hard-core predicate.

## Main results

* The `otMask_eq`, `otKnown_eq`, `otRaw_eq`, simulator-function equations and explicit
  `otSender`, `otReceiver`, `otProtocol` field equations expose the protocol's computations.
* `SecureComputation.enhancedHardCore_iff`: the enhanced prediction bound.
* `SecureComputation.otSimA_coins`, `otSimA_uniform`, `runAt_otSimA`: Alice's simulator contract.
* `SecureComputation.otSimB_coins`, `otSimB_uniform`, `runAt_otSimB`: Bob's simulator contract.
* `SecureComputation.SamplerCanonical`: the sampler outputs canonical encodings.
* `SecureComputation.otProtocol_outV`, `otProtocol_outP`: correctness: Bob outputs `a_b` and
  Alice outputs `⊥ = []`, on every coin string.
* `SecureComputation.otProtocol_isOT`: the protocol has the shape `OT.IsOT` of the helper
  modules.
* `SecureComputation.otProtocol_polyTime`: the parties run in polynomial time (proved,
  `OT.polyTime_of_isOT`).
* `SecureComputation.otSimA_isSimA`, `otSimB_isSimB`: the simulators have the shapes
  `OT.IsSimA`, `OT.IsSimB` of the helper modules.
* `SecureComputation.otProtocol_simulators`: Prop 161.5 with the explicit simulators (proved,
  `OT.simulators_of_isOT`), and `otProtocol_hbcSecure` (Prop 161.5, proved from the two).

## Contents

The proofs are in the helper modules under `SecureComputation/ObliviousTransfer/`, which state
them for every protocol of the shape of Protocol 160.4:
* `ObliviousTransfer/Shape.lean`: the shape `OT.IsOT` (the next-message functions restated) and
  the five moves of its executions.
* `ObliviousTransfer/Efficiency.lean`: the parties' machines and the message bound
  (`OT.polyTime_of_isOT`).
* `ObliviousTransfer/Simulators.lean`: the simulators' shapes `OT.IsSimA`, `OT.IsSimB` (their raw
  functions restated), the coin spaces, and the simulated views on assembled tapes.
* `ObliviousTransfer/ViewA.lean`: Alice's side, the bound `2δ(n)`
  (`OT.distAdv_realA_idealA_le`).
* `ObliviousTransfer/Predictor.lean`: the view-building distinguisher `OT.viewDist` behind Bob's
  side.
* `ObliviousTransfer/ViewB.lean`: Bob's side through the signed predictor
  (`OT.exists_negligible_bob`) and the two sides together (`OT.simulators_of_isOT`).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2.4, Protocol 160.4 and Proposition 161.5 (book pp. 160–162).
* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2*, Cambridge University Press,
  2004, Appendix C.1 (enhanced inversion) and §7.3.2 (enhanced predicates and OT). The audit
  consulted the author drafts: Appendix revised third version, 15 June 2003; Chapter 7
  version 3.2, 2 July 2003, draft pp. 639–641 for the predicate/OT argument. No text/page
  identity with the published edition is asserted.
-/

namespace TCSlib.Cryptography.SecureComputation

open Complexity Turing TCSlib.Cryptography

variable (T : TrapdoorCollection)

/-! ### The protocol -/

/-- Alice's mask `z_j = h(f_i^{-1}(y_j)) ⊕ a_j`: the trapdoor inverter on `⟨t, y_j⟩` (all-`true`
coins, as in Algorithm 104.3), the predicate evaluator `H` on `⟨i, ·⟩`, then XOR with `[a_j]`. -/
def otMask (H : List Bool → List Bool) (n : ℕ) (i t yj : List Bool) (a : Bool) : List Bool :=
  List.zipWith xor (H (pairEncode i (T.inv.runAtL n (pairEncode t yj)
    (List.replicate (T.inv.coins.eval n) true)))) [a]

/-- Alice's mask XORs her bit with the predicate evaluated on the trapdoor inversion,
using the all-`true` inverter tape. -/
theorem otMask_eq (H : List Bool → List Bool) (n : ℕ) (i t yj : List Bool) (a : Bool) :
    otMask T H n i t yj a =
      List.zipWith xor (H (pairEncode i (T.inv.runAtL n (pairEncode t yj)
        (List.replicate (T.inv.coins.eval n) true)))) [a] := rfl

/-- **Alice, the sender** [PS10, Protocol 160.4], on common input `1^n`, input `⟨a₁, a₂⟩` and the
coins of `Gen`: first `i`, then `⟨z₁, z₂⟩` on Bob's `⟨y₁, y₂⟩`, then `[]`. -/
def otSender (H : List Bool → List Bool) : Strategy where
  next x y r hist :=
    if hist.length = 0 then pairFstD (T.gen.runAtL x.length [] r)
    else if hist.length = 1 then
      pairEncode
        (otMask T H x.length (pairFstD (T.gen.runAtL x.length [] r))
          (pairSndD (T.gen.runAtL x.length [] r)) (pairFstD (hist.headD [])) (y.getD 0 false))
        (otMask T H x.length (pairFstD (T.gen.runAtL x.length [] r))
          (pairSndD (T.gen.runAtL x.length [] r)) (pairSndD (hist.headD [])) (y.getD 1 false))
    else []
  coins := T.gen.coins

/-- Alice uses the index generator's coin polynomial. -/
theorem otSender_coins (H : List Bool → List Bool) : (otSender T H).coins = T.gen.coins := rfl

/-- Alice sends the generated index initially, both masks after one received message,
and the empty word on every later history. -/
theorem otSender_next (H : List Bool → List Bool) (x y r : List Bool)
    (hist : List (List Bool)) :
    (otSender T H).next x y r hist =
      if hist.length = 0 then pairFstD (T.gen.runAtL x.length [] r)
      else if hist.length = 1 then
        pairEncode
          (otMask T H x.length (pairFstD (T.gen.runAtL x.length [] r))
            (pairSndD (T.gen.runAtL x.length [] r)) (pairFstD (hist.headD [])) (y.getD 0 false))
          (otMask T H x.length (pairFstD (T.gen.runAtL x.length [] r))
            (pairSndD (T.gen.runAtL x.length [] r)) (pairSndD (hist.headD [])) (y.getD 1 false))
      else [] := rfl

/-- Bob's sampled element `w` (decoding to `x`), from the first half of his coins. -/
def otKnown (n : ℕ) (i r : List Bool) : List Bool :=
  T.sample.runAtL n i (r.take (T.sample.coins.eval n))

/-- Bob's known element is the sample obtained from the first sampler-sized coin block. -/
theorem otKnown_eq (n : ℕ) (i r : List Bool) :
    otKnown T n i r = T.sample.runAtL n i (r.take (T.sample.coins.eval n)) := rfl

/-- Bob's raw element `y_{1−b}`, from the second half of his coins. -/
def otRaw (n : ℕ) (i r : List Bool) : List Bool :=
  T.sample.runAtL n i (r.drop (T.sample.coins.eval n))

/-- Bob's raw element is the sample obtained after dropping the first sampler-sized block. -/
theorem otRaw_eq (n : ℕ) (i r : List Bool) :
    otRaw T n i r = T.sample.runAtL n i (r.drop (T.sample.coins.eval n)) := rfl

/-- **Bob, the receiver** [PS10, Protocol 160.4], on common input `1^n`, input `[b]` and two
blocks of sampler coins: on `[i]`, the pair with `y_b = f_i(x)` (by `eval`) and `y_{1−b}` the raw
element; on `[i, z]`, `[]`; and on his complete history, `h(x) ⊕ z_b`. -/
def otReceiver (H : List Bool → List Bool) : Strategy where
  next x z r hist :=
    if hist.length = 1 then
      if z.headD false then
        pairEncode (otRaw T x.length (hist.headD []) r)
          (T.eval (pairEncode (hist.headD []) (otKnown T x.length (hist.headD []) r)))
      else
        pairEncode (T.eval (pairEncode (hist.headD []) (otKnown T x.length (hist.headD []) r)))
          (otRaw T x.length (hist.headD []) r)
    else if hist.length = 2 then []
    else List.zipWith xor (H (pairEncode (hist.headD []) (otKnown T x.length (hist.headD []) r)))
      (if z.headD false then pairSndD (hist.getD 1 []) else pairFstD (hist.getD 1 []))
  coins := .add T.sample.coins T.sample.coins

/-- Bob uses two consecutive blocks of sampler coins. -/
theorem otReceiver_coins (H : List Bool → List Bool) :
    (otReceiver T H).coins = .add T.sample.coins T.sample.coins := rfl

/-- Bob sends the choice-ordered element pair after one message, an empty filler after two,
and the XOR of the predicate word and selected mask on every other history. -/
theorem otReceiver_next (H : List Bool → List Bool) (x z r : List Bool)
    (hist : List (List Bool)) :
    (otReceiver T H).next x z r hist =
      if hist.length = 1 then
        if z.headD false then
          pairEncode (otRaw T x.length (hist.headD []) r)
            (T.eval (pairEncode (hist.headD []) (otKnown T x.length (hist.headD []) r)))
        else
          pairEncode (T.eval (pairEncode (hist.headD []) (otKnown T x.length (hist.headD []) r)))
            (otRaw T x.length (hist.headD []) r)
      else if hist.length = 2 then []
      else List.zipWith xor (H (pairEncode (hist.headD []) (otKnown T x.length (hist.headD []) r)))
        (if z.headD false then pairSndD (hist.getD 1 []) else pairFstD (hist.getD 1 [])) := rfl

/-- **Protocol 160.4** [PS10], with five messages, Alice first. -/
def otProtocol (H : List Bool → List Bool) : Protocol where
  P := otSender T H
  V := otReceiver T H
  rounds := .const 5
  verifierFirst := false

/-- Alice, the OT sender, is the protocol's prover-side strategy. -/
theorem otProtocol_P (H : List Bool → List Bool) : (otProtocol T H).P = otSender T H := rfl

/-- Bob, the OT receiver, is the protocol's verifier-side strategy. -/
theorem otProtocol_V (H : List Bool → List Bool) : (otProtocol T H).V = otReceiver T H := rfl

/-- The OT protocol makes five moves. -/
theorem otProtocol_rounds (H : List Bool → List Bool) : (otProtocol T H).rounds = .const 5 := rfl

/-- The OT protocol starts with Alice, rather than the verifier-side party. -/
theorem otProtocol_verifierFirst (H : List Bool → List Bool) :
    (otProtocol T H).verifierFirst = false := rfl

/-- **Protocol 160.4 has the shape `OT.IsOT`**: its next-message functions are `OT.senderNext`
and `OT.receiverNext` (the field equations, with `otMask_eq`, `otKnown_eq` and `otRaw_eq`), Alice
uses `Gen`'s coins and Bob two sampler blocks, and it has five messages, Alice first:
`OT.IsOT T H (otProtocol T H)`. -/
theorem otProtocol_isOT (H : List Bool → List Bool) : OT.IsOT T H (otProtocol T H) := by
  refine (OT.isOT_iff T H _).2 ⟨?_, ?_, by rw [otProtocol_P, otSender_coins],
    by rw [otProtocol_V, otReceiver_coins], otProtocol_rounds T H, otProtocol_verifierFirst T H⟩
  · funext x y r hist
    rw [otProtocol_P, otSender_next, OT.senderNext_eq, otMask_eq, otMask_eq, OT.mask_eq,
      OT.mask_eq]
  · funext x z r hist
    rw [otProtocol_V, otReceiver_next, OT.receiverNext_eq, otKnown_eq, otRaw_eq]

/-- **The sampler outputs canonical encodings** [PS10, Definition 41.1 (2)]: at every generated
index, every output of the domain sampler is `encD i x` for some `x ∈ D_i`
(`Collection.sample_eq_encD`, from the sampler contract and canonical decoding). -/
theorem SamplerCanonical :
    ∀ n (r : T.gen.Coins n) (s : T.sample.Coins n), ∃ x,
      T.sample.runAt n (T.index n r) s = T.encD (T.index n r) x :=
  T.toCollection.sample_eq_encD

/-- **An enhanced hard-core predicate**, the explicit Boolean prediction hypothesis used for
the OT argument of [Gol04, §7.3.2] (a declared strengthening of [PS10, Proposition 161.5]'s
hypothesis; see the module docstring). Appendix C.1 motivates enhanced inversion; its
Definition C.1.1 is an inversion condition, not this prediction definition. For every
non-uniform PPT `A`,
predicting `h(f_i⁻¹(y))` for a sampled element `y`, given the index `i` and **the sampler's
coins** that produced `y`, succeeds with probability at most `½` plus a negligible amount, on
average over the generated indices. The element `y` is read through the decoder (a sampled
string decodes, `Collection.sample_spec`), and its preimage is `perm⁻¹` of it (`f_perm`). -/
def EnhancedHardCore (h : ∀ i, T.D i → Bool) : Prop :=
  ∀ A : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n,
    uexp (fun r : T.gen.Coins n =>
      uprob fun z : T.sample.Coins n × A.Coins n =>
        A.distinguisherL n (pairEncode (T.index n r) (List.ofFn z.1)) z.2 =
          h (T.index n r) ((T.perm (T.index n r)).symm
            ((T.decD (T.index n r) (T.sample.runAt n (T.index n r) z.1)).getD default)))
      ≤ 1 / 2 + ε n

/-- Enhanced hard-core security bounds prediction of a sampled element's preimage bit by
one half plus a negligible function, even when the predictor receives the sampler's coins. -/
theorem enhancedHardCore_iff (h : ∀ i, T.D i → Bool) :
    EnhancedHardCore T h ↔
      ∀ A : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n,
        uexp (fun r : T.gen.Coins n =>
          uprob fun z : T.sample.Coins n × A.Coins n =>
            A.distinguisherL n (pairEncode (T.index n r) (List.ofFn z.1)) z.2 =
              h (T.index n r) ((T.perm (T.index n r)).symm
                ((T.decD (T.index n r) (T.sample.runAt n (T.index n r) z.1)).getD default)))
          ≤ 1 / 2 + ε n := Iff.rfl

/-! ### Correctness -/

section Correctness

variable {h : ∀ i, T.D i → Bool} (H : List Bool → List Bool)
  (henc : ∀ i (x : T.D i), H (pairEncode i (T.encD i x)) = [h i x])

include henc in
/-- **Bob outputs `a_b`** on every coin string (the output clause of Proposition 161.5).

**Proof sketch.**
1. Unfold the five moves. Bob's known element `w` is the sampler on his first coin block, and it
   decodes to some `x` with `eval ⟨i, w⟩ = encD(perm x)` (`sample_spec`, `f_perm`).
2. So `y_b = encD(perm x)`, and Alice's trapdoor inverter maps it back to an encoding of `x`
   (`inv_spec`). Canonical decoding extends the supplied specification of `H` to all decodable
   strings (`Collection.apply_of_decD`), so `H` gives `[h(x)]` on both sides.
3. Bob outputs `h(x) ⊕ z_b = h(x) ⊕ h(x) ⊕ a_b = a_b`, by cases on `b` and on `h(x)`. -/
theorem otProtocol_outV (x : List Bool) (a : Fin 2 → Bool) (b : Fin 1 → Bool)
    (r : (otProtocol T H).ExecCoins (otProtocol T H).P x) :
    (otProtocol T H).outV (otProtocol T H).P x (List.ofFn a) (List.ofFn b) r =
      [a (if b 0 then 1 else 0)] := by
  have hspec : ∀ i w (xx : T.D i),
      T.decD i w = some xx → H (pairEncode i w) = [h i xx] :=
    fun _ _ _ hw =>
      T.toCollection.apply_of_decD (v := fun i xx => [h i xx]) henc hw
  obtain ⟨rA₀, rB₀⟩ := r
  have hA : (otSender T H).coinLen x.length = T.gen.coinLen x.length :=
    (Strategy.coinLen_eq (otSender T H) x.length).trans (T.gen.coinLen_eq x.length).symm
  have hB : (otReceiver T H).coinLen x.length =
      T.sample.coinLen x.length + T.sample.coinLen x.length :=
    (Strategy.coinLen_eq (otReceiver T H) x.length).trans
      ((PolyExpr.eval_add T.sample.coins T.sample.coins x.length).trans
        (congrArg₂ Nat.add (T.sample.coinLen_eq x.length).symm
          (T.sample.coinLen_eq x.length).symm))
  let rA : T.gen.Coins x.length := fun j => rA₀ (Fin.cast hA.symm j)
  let rB : Fin (T.sample.coinLen x.length + T.sample.coinLen x.length) → Bool :=
    fun j => rB₀ (Fin.cast hB.symm j)
  have hAr : List.ofFn rA₀ = List.ofFn rA := List.ofFn_congr hA rA₀
  have hBr : List.ofFn rB₀ = List.ofFn rB := List.ofFn_congr hB rB₀
  rw [Protocol.outV_eq, Protocol.transcriptWith_eq, hAr, hBr]
  simp [otProtocol, exec_succ, exec_zero, otSender, otReceiver]
  have hg : T.gen.runAtL x.length [] (List.ofFn fun i => rA i) =
      T.gen.runAt x.length [] rA :=
    (T.gen.runAt_eq x.length [] rA).symm
  erw [hg]
  -- Bob's first coin block, typed
  let s1 : T.sample.Coins x.length := fun j => rB ⟨j.1,
    show (j : ℕ) < T.sample.coinLen x.length + T.sample.coinLen x.length from
      Nat.lt_of_lt_of_le j.2 (Nat.le_add_right _ _)⟩
  have hs1 : (List.ofFn fun i => rB i).take (T.sample.coins.eval x.length) = List.ofFn s1 := by
    apply List.ext_getElem
    · simp only [List.length_take, List.length_ofFn]
      rw [← T.sample.coinLen_eq x.length]
      omega
    · intro j h₁ h₂
      simp only [List.getElem_take, List.getElem_ofFn]
      rfl
  have hknown : otKnown T x.length (pairFstD (T.gen.runAt x.length [] rA))
      (List.ofFn fun i => rB i) =
      T.sample.runAt x.length (pairFstD (T.gen.runAt x.length [] rA)) s1 := by
    rw [otKnown, hs1]
    exact (T.sample.runAt_eq x.length _ s1).symm
  obtain ⟨xx, hdec, heval⟩ := T.sample_spec x.length rA s1
  have hyb : T.eval (pairEncode (pairFstD (T.gen.runAt x.length [] rA))
      (otKnown T x.length (pairFstD (T.gen.runAt x.length [] rA)) (List.ofFn fun i => rB i))) =
      T.encD _ (T.perm _ xx) := by
    rw [hknown, heval, T.f_perm]
  have hinv := T.inv_spec x.length rA (T.perm _ xx) (fun _ => true)
  rw [Equiv.symm_apply_apply] at hinv
  have hHinv : H (pairEncode (pairFstD (T.gen.runAt x.length [] rA))
      (T.inv.runAtL x.length
        (pairEncode (pairSndD (T.gen.runAt x.length [] rA)) (T.encD _ (T.perm _ xx)))
        (List.replicate (T.inv.coins.eval x.length) true))) = [h _ xx] := by
    rw [← T.inv.coinLen_eq x.length, ← List.ofFn_const, ← NUPPT.runAt_eq]
    exact hspec _ _ _ hinv
  have hHw : H (pairEncode (pairFstD (T.gen.runAt x.length [] rA))
      (otKnown T x.length (pairFstD (T.gen.runAt x.length [] rA)) (List.ofFn fun i => rB i))) =
      [h _ xx] := by
    rw [hknown]
    exact hspec _ _ _ hdec
  cases hb : b 0
  · simp only [Bool.false_eq_true, if_false, pairFstD_pairEncode, pairSndD_pairEncode]
    erw [hyb]
    simp only [otMask]
    erw [hHinv, hHw]
    cases h _ xx <;> simp
  · simp only [if_true, pairFstD_pairEncode, pairSndD_pairEncode]
    erw [hyb]
    simp only [otMask]
    erw [hHinv, hHw]
    cases h _ xx <;> simp

/-- **Alice outputs `⊥ = []`** on every coin string. -/
theorem otProtocol_outP (x : List Bool) (a : Fin 2 → Bool) (b : Fin 1 → Bool)
    (r : (otProtocol T H).ExecCoins (otProtocol T H).P x) :
    (otProtocol T H).outP x (List.ofFn a) (List.ofFn b) r = [] := by
  obtain ⟨rA, rB⟩ := r
  simp [Protocol.outP_eq, Protocol.transcriptWith_eq, otProtocol, exec_succ, exec_zero,
    otSender, otReceiver]

end Correctness

/-! ### The simulators -/

/-- The coin segment of length `q(n)` after the first `p(n)` coins of a raw layout. -/
def coinSeg (p q : PolyExpr) (z : List Bool) : List Bool :=
  ((NUPPT.inCoins z).drop (p.eval (NUPPT.inParam z).length)).take (q.eval (NUPPT.inParam z).length)

/-- The coin segment drops the first `p(|parameter|)` bits and takes the next
`q(|parameter|)` bits of the raw tape. -/
theorem coinSeg_eq (p q : PolyExpr) (z : List Bool) :
    coinSeg p q z =
      ((NUPPT.inCoins z).drop (p.eval (NUPPT.inParam z).length)).take
        (q.eval (NUPPT.inParam z).length) := rfl

/-- A coin segment is polynomial-time (`polyTimeComputable_pairDropPoly`,
`polyTimeComputable_pairTakePoly`). -/
theorem polyTimeComputable_coinSeg (p q : PolyExpr) : PolyTimeComputable (coinSeg p q) := by
  have h₁ := (polyTimeComputable_pairDropPoly p).comp
    (NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inCoins)
  have h₂ := (polyTimeComputable_pairTakePoly q).comp
    (NUPPT.polyTimeComputable_inParam.pairEncode h₁)
  refine (congrArg PolyTimeComputable (?_ : coinSeg p q = _)).mpr h₂
  funext z
  simp only [coinSeg, Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]

/-- The index `i` a simulator generates from its first `coins_Gen(n)` coins. -/
def simIdx (z : List Bool) : List Bool :=
  pairFstD (T.gen.output (NUPPT.layout (NUPPT.inParam z) [] []
    (coinSeg (.const 0) T.gen.coins z)))

/-- The simulated index is the first component of the generator's output on its designated
coin segment, with empty argument and advice. -/
theorem simIdx_eq (z : List Bool) :
    simIdx T z = pairFstD (T.gen.output (NUPPT.layout (NUPPT.inParam z) [] []
      (coinSeg (.const 0) T.gen.coins z))) := rfl

/-- The simulated index is polynomial-time. -/
theorem polyTimeComputable_simIdx : PolyTimeComputable (simIdx T) := by
  have h := polyTimeComputable_pairFstD.comp (T.gen.polyTimeComputable_output.comp
    (NUPPT.polyTimeComputable_layout NUPPT.polyTimeComputable_inParam
      (polyTimeComputable_const []) (polyTimeComputable_const [])
      (polyTimeComputable_coinSeg (.const 0) T.gen.coins)))
  refine (congrArg PolyTimeComputable (?_ : simIdx T = _)).mpr h
  funext z
  simp only [simIdx, Function.comp_apply]

/-- A sampled element at the simulated index, from the sampler-coin segment after `p(n)` coins. -/
def simSample (p : PolyExpr) (z : List Bool) : List Bool :=
  T.sample.output (NUPPT.layout (NUPPT.inParam z) (simIdx T z) [] (coinSeg p T.sample.coins z))

/-- A simulated sample runs the sampler at the simulated index on its designated coin
segment, with empty advice. -/
theorem simSample_eq (p : PolyExpr) (z : List Bool) :
    simSample T p z =
      T.sample.output (NUPPT.layout (NUPPT.inParam z) (simIdx T z) []
        (coinSeg p T.sample.coins z)) := rfl

/-- A simulated sample is polynomial-time. -/
theorem polyTimeComputable_simSample (p : PolyExpr) : PolyTimeComputable (simSample T p) := by
  have h := T.sample.polyTimeComputable_output.comp
    (NUPPT.polyTimeComputable_layout NUPPT.polyTimeComputable_inParam
      (polyTimeComputable_simIdx T) (polyTimeComputable_const [])
      (polyTimeComputable_coinSeg p T.sample.coins))
  refine (congrArg PolyTimeComputable (?_ : simSample T p = _)).mpr h
  funext z
  simp only [simSample, Function.comp_apply]

/-- **`S_A`** on `⟨1^n, ⟨⟨a₁, a₂⟩, ⊥⟩⟩`: Alice's view, with `Gen`'s coins as her tape and two
fresh sampled elements as Bob's message: `⟨⟨1^n, ⟨a₁, a₂⟩⟩, ⟨r_Gen, [⟨y₁, y₂⟩, []]⟩⟩`. -/
def otSimAFun (z : List Bool) : List Bool :=
  pairEncode (pairEncode (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)))
    (pairEncode (coinSeg (.const 0) T.gen.coins z)
      (pairEncode (pairEncode (simSample T T.gen.coins z)
          (simSample T (.add T.gen.coins T.sample.coins) z))
        (pairEncode [] [])))

/-- Alice's simulator word encodes her parameter, input and generator coins, followed by
the two simulated samples and an empty received message. -/
theorem otSimAFun_eq (z : List Bool) :
    otSimAFun T z =
      pairEncode (pairEncode (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)))
        (pairEncode (coinSeg (.const 0) T.gen.coins z)
          (pairEncode (pairEncode (simSample T T.gen.coins z)
              (simSample T (.add T.gen.coins T.sample.coins) z))
            (pairEncode [] []))) := rfl

/-- `S_A` is polynomial-time. -/
theorem polyTimeComputable_otSimAFun : PolyTimeComputable (otSimAFun T) := by
  have h := (NUPPT.polyTimeComputable_inParam.pairEncode
    (polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg)).pairEncode
    ((polyTimeComputable_coinSeg (.const 0) T.gen.coins).pairEncode
      (((polyTimeComputable_simSample T T.gen.coins).pairEncode
          (polyTimeComputable_simSample T (.add T.gen.coins T.sample.coins))).pairEncode
        (polyTimeComputable_const (pairEncode [] []))))
  refine (congrArg PolyTimeComputable (?_ : otSimAFun T = _)).mpr h
  funext z
  simp only [otSimAFun, Function.comp_apply]

/-- **The simulator `S_A`** of Proposition 161.5: `Gen`'s coins and two blocks of sampler coins. -/
noncomputable def otSimA : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_otSimAFun T)
    (.add T.gen.coins (.add T.sample.coins T.sample.coins))

/-- Alice's simulator uses generator coins followed by two sampler blocks. -/
theorem otSimA_coins :
    (otSimA T).coins = .add T.gen.coins (.add T.sample.coins T.sample.coins) :=
  NUPPT.coins_ofPolyTimeUniform (polyTimeComputable_otSimAFun T) _

/-- Alice's simulator is uniform. -/
theorem otSimA_uniform : (otSimA T).Uniform :=
  NUPPT.ofPolyTimeUniform_uniform (polyTimeComputable_otSimAFun T) _

/-- Alice's simulator at parameter `n` computes its view word on the unary-parameter layout,
with the supplied argument and tape and empty advice. -/
theorem runAt_otSimA (n : ℕ) (y : List Bool) (r : (otSimA T).Coins n) :
    (otSimA T).runAt n y r =
      otSimAFun T (NUPPT.layout (List.replicate n true) y [] (List.ofFn r)) := by
  rw [NUPPT.runAt_eq]
  unfold otSimA
  rw [NUPPT.runAtL_ofPolyTimeUniform, NUPPT.advInput_eq, NUPPT.layout_eq]

/-- `S_B`'s mask `z_b = h(x) ⊕ a_b`, with `x` its first sampled element and `[a_b]` the second
part of its argument. -/
def otSimZb (H : List Bool → List Bool) (z : List Bool) : List Bool :=
  List.zipWith xor (H (pairEncode (simIdx T z) (simSample T T.gen.coins z)))
    (pairSndD (NUPPT.inArg z))

/-- Bob's selected mask XORs the predicate word of the first simulated sample with the
second component of the supplied argument. -/
theorem otSimZb_eq (H : List Bool → List Bool) (z : List Bool) :
    otSimZb T H z =
      List.zipWith xor (H (pairEncode (simIdx T z) (simSample T T.gen.coins z)))
        (pairSndD (NUPPT.inArg z)) := rfl

/-- `S_B`'s pair `(z₁, z₂)`: `z_b` from `otSimZb`, `z_{1−b}` one fresh coin. -/
def otSimZ (H : List Bool → List Bool) (z : List Bool) : List Bool :=
  if (pairFstD (NUPPT.inArg z)).headD false then
    pairEncode (coinSeg (.add T.gen.coins (.add T.sample.coins T.sample.coins)) (.const 1) z)
      (otSimZb T H z)
  else
    pairEncode (otSimZb T H z)
      (coinSeg (.add T.gen.coins (.add T.sample.coins T.sample.coins)) (.const 1) z)

/-- Bob's simulated mask pair places the final coin segment in the unselected position and
the computed mask in the position selected by the first input bit. -/
theorem otSimZ_eq (H : List Bool → List Bool) (z : List Bool) :
    otSimZ T H z =
      if (pairFstD (NUPPT.inArg z)).headD false then
        pairEncode (coinSeg (.add T.gen.coins (.add T.sample.coins T.sample.coins)) (.const 1) z)
          (otSimZb T H z)
      else
        pairEncode (otSimZb T H z)
          (coinSeg (.add T.gen.coins (.add T.sample.coins T.sample.coins)) (.const 1) z) := rfl

/-- **`S_B`** on `⟨1^n, ⟨[b], [a_b]⟩⟩`: Bob's view, with two blocks of sampler coins as his tape,
the simulated index as Alice's first message, `(z₁, z₂)` from `otSimZ` as her second, and `[]`:
`⟨⟨1^n, [b]⟩, ⟨r_B, [i, ⟨z₁, z₂⟩, []]⟩⟩`. -/
def otSimBFun (H : List Bool → List Bool) (z : List Bool) : List Bool :=
  pairEncode (pairEncode (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)))
    (pairEncode (coinSeg T.gen.coins (.add T.sample.coins T.sample.coins) z)
      (pairEncode (simIdx T z) (pairEncode (otSimZ T H z) (pairEncode [] []))))

/-- Bob's simulator word encodes his parameter, choice bit and sampler coins, followed by
the simulated index, mask pair and empty received message. -/
theorem otSimBFun_eq (H : List Bool → List Bool) (z : List Bool) :
    otSimBFun T H z =
      pairEncode (pairEncode (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)))
        (pairEncode (coinSeg T.gen.coins (.add T.sample.coins T.sample.coins) z)
          (pairEncode (simIdx T z) (pairEncode (otSimZ T H z) (pairEncode [] [])))) := rfl

/-- `S_B` is polynomial-time when `H` is.

**Proof sketch.** `S_B` is built from polynomial-time pieces by pairing: the parameter and input
readers, the coin segments (`polyTimeComputable_coinSeg`), the simulated index and sample, `H`,
one XOR, and a branch on `b` (`polyTimeComputable_ite`). Each piece is matched to its definition
by `funext`. -/
theorem polyTimeComputable_otSimBFun {H : List Bool → List Bool} (hH : PolyTimeComputable H) :
    PolyTimeComputable (otSimBFun T H) := by
  have hzb : PolyTimeComputable (otSimZb T H) := by
    have h := polyTimeComputable_pairXor.comp ((hH.comp ((polyTimeComputable_simIdx T).pairEncode
      (polyTimeComputable_simSample T T.gen.coins))).pairEncode
      (polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg))
    refine (congrArg PolyTimeComputable (?_ : otSimZb T H = _)).mpr h
    funext z
    simp only [otSimZb, Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hu := polyTimeComputable_coinSeg (.add T.gen.coins (.add T.sample.coins T.sample.coins))
    (.const 1)
  have hb₀ := polyTimeComputable_headD.comp
    (polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg)
  have hb : PolyTimeComputable fun z => [(pairFstD (NUPPT.inArg z)).headD false] := by
    refine (congrArg PolyTimeComputable
      (?_ : (fun z => [(pairFstD (NUPPT.inArg z)).headD false]) = _)).mpr hb₀
    funext z
    simp only [Function.comp_apply]
  have hz : PolyTimeComputable (otSimZ T H) := by
    have h := polyTimeComputable_ite (p := fun z => (pairFstD (NUPPT.inArg z)).headD false)
      hb (hu.pairEncode hzb) (hzb.pairEncode hu)
    refine (congrArg PolyTimeComputable (?_ : otSimZ T H = _)).mpr h
    funext z
    simp only [otSimZ]
  have h := (NUPPT.polyTimeComputable_inParam.pairEncode
    (polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg)).pairEncode
    ((polyTimeComputable_coinSeg T.gen.coins (.add T.sample.coins T.sample.coins)).pairEncode
      ((polyTimeComputable_simIdx T).pairEncode
        (hz.pairEncode (polyTimeComputable_const (pairEncode [] [])))))
  refine (congrArg PolyTimeComputable (?_ : otSimBFun T H = _)).mpr h
  funext z
  simp only [otSimBFun, Function.comp_apply]

/-- **The simulator `S_B`** of Proposition 161.5: `Gen`'s coins, two blocks of sampler coins and
one coin for `z_{1−b}`. -/
noncomputable def otSimB {H : List Bool → List Bool} (hH : PolyTimeComputable H) : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_otSimBFun T hH)
    (.add T.gen.coins (.add T.sample.coins (.add T.sample.coins (.const 1))))

/-- Bob's simulator uses generator coins, two sampler blocks and one fresh mask coin. -/
theorem otSimB_coins {H : List Bool → List Bool} (hH : PolyTimeComputable H) :
    (otSimB T hH).coins =
      .add T.gen.coins (.add T.sample.coins (.add T.sample.coins (.const 1))) :=
  NUPPT.coins_ofPolyTimeUniform (polyTimeComputable_otSimBFun T hH) _

/-- Bob's simulator is uniform. -/
theorem otSimB_uniform {H : List Bool → List Bool} (hH : PolyTimeComputable H) :
    (otSimB T hH).Uniform :=
  NUPPT.ofPolyTimeUniform_uniform (polyTimeComputable_otSimBFun T hH) _

/-- Bob's simulator at parameter `n` computes its view word on the unary-parameter layout,
with the supplied argument and tape and empty advice. -/
theorem runAt_otSimB {H : List Bool → List Bool} (hH : PolyTimeComputable H)
    (n : ℕ) (y : List Bool) (r : (otSimB T hH).Coins n) :
    (otSimB T hH).runAt n y r =
      otSimBFun T H (NUPPT.layout (List.replicate n true) y [] (List.ofFn r)) := by
  rw [NUPPT.runAt_eq]
  unfold otSimB
  rw [NUPPT.runAtL_ofPolyTimeUniform, NUPPT.advInput_eq, NUPPT.layout_eq]

/-- **`S_A` has the shape `OT.IsSimA`**: its coins are `coins_Gen + (coins_Sample + coins_Sample)`
and it computes `OT.simAView` (`otSimA_coins`, `runAt_otSimA`, and the readers of `otSimAFun`,
`coinSeg`, `simIdx`, `simSample`): `OT.IsSimA T (otSimA T)`. -/
theorem otSimA_isSimA : OT.IsSimA T (otSimA T) := by
  refine (OT.isSimA_iff T _).2 ⟨otSimA_coins T, fun n y r => ?_⟩
  rw [runAt_otSimA]
  simp only [otSimAFun_eq, simSample_eq, simIdx_eq, coinSeg_eq, OT.simAView_eq, OT.simSampled_eq,
    OT.simIndex_eq, OT.simSeg_eq]

/-- **`S_B` has the shape `OT.IsSimB`**: its coins are
`coins_Gen + (coins_Sample + (coins_Sample + 1))` and it computes `OT.simBView` (`otSimB_coins`,
`runAt_otSimB`, and the readers of `otSimBFun`, `otSimZ`, `otSimZb`, `coinSeg`, `simIdx`,
`simSample`): `OT.IsSimB T H (otSimB T hH)`. -/
theorem otSimB_isSimB {H : List Bool → List Bool} (hH : PolyTimeComputable H) :
    OT.IsSimB T H (otSimB T hH) := by
  refine (OT.isSimB_iff T H _).2 ⟨otSimB_coins T hH, fun n y r => ?_⟩
  rw [runAt_otSimB]
  simp only [otSimBFun_eq, otSimZ_eq, otSimZb_eq, simSample_eq, simIdx_eq, coinSeg_eq,
    OT.simBView_eq, OT.simZpair_eq, OT.simZbit_eq, OT.simSampled_eq, OT.simIndex_eq, OT.simSeg_eq]

/-! ### Proposition 161.5 -/

section Security

variable {h : ∀ i, T.D i → Bool} (H : List Bool → List Bool) (hH : PolyTimeComputable H)
  (henc : ∀ i (x : T.D i), H (pairEncode i (T.encD i x)) = [h i x])

include henc in
/-- **Proposition 161.5 with its simulators** [PS10]: for a collection of trapdoor permutations
`T` with an enhanced hard-core predicate `h` evaluated on encodings by polynomial-time `H`,
`S_A = otSimA` and `S_B = otSimB` simulate the two sides of Protocol 160.4 within a negligible
advantage, uniformly over the inputs.

**Proof sketch.** The protocol and the simulators have the shapes `OT.IsOT`, `OT.IsSimA`,
`OT.IsSimB` (`otProtocol_isOT`, `otSimA_isSimA`, `otSimB_isSimB`), and `OT.simulators_of_isOT`
proves the statement for every protocol and simulators of these shapes.
1. *Correctness* (`otProtocol_outV`, `otProtocol_outP`): the real outputs are `a_b` for Bob and
   `[]` for Alice on every coin string, which are the ideal outputs. So each side reduces to its
   view.
2. *Alice's side* (`OT.distAdv_realA_idealA_le`). On the coins `(r, s₁, s₂)` (`OT.realCoins`,
   `OT.simACoins`) Alice's real and simulated views differ only in Bob's message.
   - Real: `⟨f_i(w₁), w₂⟩` (or `⟨w₂, f_i(w₁)⟩` when `b`), with `w_j = Sample(i; s_j)`.
   - Simulated: `⟨w₁, w₂⟩`, two sampled elements, canonical by `SamplerCanonical`.

   The sampler is within `δ(n)` of uniform on `D_i` (`T.OneWay.sampleClose`), and `perm` is a
   bijection, so at every generated index `f_i(w) = eval ⟨i, w⟩` is `2δ(n)`-close to a sampled
   element (`OT.statClose_eval_sample`). The views are `2δ(n)`-close statistically, so any
   distinguisher's advantage is at most `2δ(n)` (`distAdv_le_of_statClose`).
3. *Bob's side* (`OT.exists_negligible_bob`).
   - Bob's real view is his tape, `i`, and `(z₁, z₂)` with `z_b = h(x) ⊕ a_b` and
     `z_{1−b} = h(u) ⊕ a_{1−b}`, where `u = perm⁻¹(x')` for Bob's raw element `x'`
     (`OT.mask_eval`, `OT.mask_raw`).
   - `S_B` produces the same, but with `z_{1−b}` a fresh coin. Writing `P(β)` for `D`'s
     acceptance with `z_{1−b} = β ⊕ a_{1−b}`, the advantage is `|E_r P(B) − E_r P(¬B)| / 2`
     for `B = h(u)` (`OT.acceptProb_realB`, `OT.acceptProb_idealB`).
   - A distinguisher of the two gives a predictor of `h(u)` from `⟨i, s'⟩`, where `s'` are the
     sampler coins of `x'`: the machine `OT.viewDist` builds the view around the challenge (Bob's
     tape contains `s'`) and runs the distinguisher, inside `tdpPredictor` of Algorithm 104.3. It
     predicts with probability `1/2 ± (P(B) − P(¬B))/2` (the signed-predictor identity
     `OT.uprob_signedPredictor_false`/`_true`, for uniform coin challenges).
   - Its advantage is at most `|ε_false(n)| + |ε_true(n)|` by `hEHC` (enhanced hard-core: the
     predictor sees the sampler's coins, which the plain hard-core property would not allow).
   - Building the selected mask also uses `a_b`, so the bits `(b, a₀, a₁)` are fixed in the
     machine: eight triples and two signs. The sum of the sixteen negligible bounds is negligible
     and uniform over the inputs; fixing only the choice and unselected sender bit would not
     specify the complete view.
4. *Efficiency.* The predictor runs Bob's sampler, `H`, one XOR and the distinguisher (with its
   advice): `NUPPT.ofPolyTime` of a polynomial-time raw function (`OT.viewDist`).

The bound is `ε(n) = 2|δ(n)| + ε_B(n)`. The source writes out `S_A` only and leaves `S_B` "as an
exercise"; step 3 is that exercise. -/
theorem otProtocol_simulators (hT : T.OneWay) (hEHC : EnhancedHardCore T h) :
    ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n (x : Fin (otFunctionality.inA.eval n) → Bool)
        (y : Fin (otFunctionality.inB.eval n) → Bool),
        distAdv (otFunctionality.realA (otProtocol T H) n x y)
            (otFunctionality.idealA (otSimA T) n x y) (D.distinguisherL n) ≤ ε n ∧
          distAdv (otFunctionality.realB (otProtocol T H) n x y)
            (otFunctionality.idealB (otSimB T hH) n x y) (D.distinguisherL n) ≤ ε n :=
  OT.simulators_of_isOT T H hH henc (otProtocol_isOT T H) (otProtocol_outV T H henc)
    (otProtocol_outP T H) (otSimA_isSimA T) (otSimB_isSimB T hH) hT
    ((enhancedHardCore_iff T h).1 hEHC)

include hH in
/-- **Protocol 160.4 runs in polynomial time** (Definition 155.1's efficiency requirement,
`Functionality.PolyTime`).

**Proof sketch.** The protocol has the shape `OT.IsOT` (`otProtocol_isOT`), and
`OT.polyTime_of_isOT` proves the requirement for every protocol of that shape.
1. *Alice.* On the empty history she outputs `Gen`'s index; on one message, the two masks (the
   trapdoor inverter, `H` and one XOR each, paired); otherwise `[]`. The raw machine
   `OT.senderRaw` reads the case off the encoded history `w`: `w = []`, or `snd w = []`
   (`polyTimeComputable_isNil`). `Gen` and the inverter are uniform machines and `H` is
   polynomial-time, so `NUPPT.ofPolyTimeUniform` of it computes her next-message function
   (`OT.senderRaw_advInput`), with `Gen`'s coins.
2. *Bob.* His sampler on the two coin blocks, `eval` and a pairing on one message; `[]` on two;
   `H` and one XOR otherwise (`OT.receiverRaw`, with a third emptiness test). The same
   construction gives a uniform machine with two sampler blocks of coins.
3. *Messages.* The transcript is `([y, []], [i, z, []])` (`OT.transcriptWith_isOT`). The index has
   `|i| ≤ Q₁(n)`, `Gen`'s `NUPPT.runLenPoly`. Bob's pair `y` has two sampler outputs (`≤ Q₂(n)`,
   the sampler's `runLenPoly` at `Q₁`) or evaluations (`≤ Q₃(n)`, `eval`'s polynomial bound), so
   `|y| ≤ 3(Q₂ + Q₃) + 2`. The masks have one bit each, so `|z| ≤ 5`, and the fillers are empty.
   So `B = Q₁ + (3(Q₂ + Q₃) + 2) + 5` (`OT.exists_messages_le`). -/
theorem otProtocol_polyTime : otFunctionality.PolyTime (otProtocol T H) :=
  OT.polyTime_of_isOT T hH (otProtocol_isOT T H)

include henc hH in
/-- **Proposition 161.5** [PS10]: Protocol 160.4 is an honest-but-curious one-out-of-two
oblivious transfer (Definition 155.1 for `otFunctionality`), for a collection of trapdoor
permutations with an enhanced hard-core predicate evaluated on canonical encodings by a
polynomial-time `H`. Sampler canonicity follows from the collection contract. -/
theorem otProtocol_hbcSecure (hT : T.OneWay) (hEHC : EnhancedHardCore T h) :
    HBCSecure (otProtocol T H) otFunctionality :=
  (hbcSecure_iff (otProtocol T H) otFunctionality).mpr
    ⟨otProtocol_polyTime T H hH, otSimA T, otSimB T hH,
      otProtocol_simulators T H hH henc hT hEHC⟩

end Security

end TCSlib.Cryptography.SecureComputation

## ===== TCSlib/Cryptography/SecureComputation/ObliviousTransfer/Shape.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Defs
import TCSlib.Cryptography.Asymptotic.Collections

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Oblivious transfer: the shape of Protocol 160.4 and its five moves

The proofs of [PS10, Proposition 161.5] are carried out for every protocol of the shape of
Protocol 160.4, stated here by its next-message functions. This module cannot import
`SecureComputation/ObliviousTransfer.lean`, which imports it, so the shape restates the bodies of
`otSender` and `otReceiver` (with `otMask`, `otKnown` and `otRaw` expanded); the owned file proves
that `otProtocol` has this shape from its published field equations.

## Main definitions

* `OT.mask`, `OT.senderNext`, `OT.receiverNext`: Alice's mask and the two next-message
  functions of [PS10, Protocol 160.4].
* `OT.IsOT`: a protocol of the shape of Protocol 160.4.

## Main results

* `OT.senderNext_nil`, `OT.senderNext_single`, `OT.senderNext_pair`, `OT.receiverNext_single`,
  `OT.receiverNext_pair`: the messages on histories of length `0`, `1` and `2`.
* `OT.exec_five`: the five moves of a prover-first execution.
* `OT.transcriptWith_isOT`: the transcript of a protocol of the shape of Protocol 160.4.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2.4, Protocol 160.4 (book p. 160).
-/

namespace TCSlib.Cryptography.SecureComputation.OT

open Complexity Turing TCSlib.Cryptography

variable (T : TrapdoorCollection) (H : List Bool → List Bool)

/-- **Alice's mask** [PS10, Protocol 160.4]: `z_j = h(f_i⁻¹(y_j)) ⊕ a_j`, computed as
`zipWith xor (H ⟨i, Inv(1^n, ⟨t, y_j⟩; 1^{inv(n)})⟩) [a]` (the body of `otMask`). -/
def mask (n : ℕ) (i t yj : List Bool) (a : Bool) : List Bool :=
  List.zipWith xor (H (pairEncode i (T.inv.runAtL n (pairEncode t yj)
    (List.replicate (T.inv.coins.eval n) true)))) [a]

/-- The defining equation of `mask`: `mask T H n i t yj a =
zipWith xor (H ⟨i, Inv(1^n, ⟨t, yj⟩; 1^{inv(n)})⟩) [a]`. -/
theorem mask_eq (n : ℕ) (i t yj : List Bool) (a : Bool) :
    mask T H n i t yj a =
      List.zipWith xor (H (pairEncode i (T.inv.runAtL n (pairEncode t yj)
        (List.replicate (T.inv.coins.eval n) true)))) [a] := rfl

/-- **Alice's next message** [PS10, Protocol 160.4] (the body of `otSender`): on the empty
history `i = fst Gen(1^{|x|}; r)`; on one message `m`, `⟨mask (fst m) y₀, mask (snd m) y₁⟩` with
`⟨i, t⟩ = Gen(1^{|x|}; r)`; otherwise `[]`. -/
def senderNext (x y r : List Bool) (hist : List (List Bool)) : List Bool :=
  if hist.length = 0 then pairFstD (T.gen.runAtL x.length [] r)
  else if hist.length = 1 then
    pairEncode
      (mask T H x.length (pairFstD (T.gen.runAtL x.length [] r))
        (pairSndD (T.gen.runAtL x.length [] r)) (pairFstD (hist.headD [])) (y.getD 0 false))
      (mask T H x.length (pairFstD (T.gen.runAtL x.length [] r))
        (pairSndD (T.gen.runAtL x.length [] r)) (pairSndD (hist.headD [])) (y.getD 1 false))
  else []

/-- The defining equation of `senderNext`: `[]` ↦ `i`, `[m]` ↦ the two masks, else `[]`, i.e.
`senderNext T H x y r hist = if |hist| = 0 then i else if |hist| = 1 then
⟨mask (fst m) y₀, mask (snd m) y₁⟩ else []` with `i = fst Gen(1^{|x|}; r)` and
`m = hist.headD []`. -/
theorem senderNext_eq (x y r : List Bool) (hist : List (List Bool)) :
    senderNext T H x y r hist =
      if hist.length = 0 then pairFstD (T.gen.runAtL x.length [] r)
      else if hist.length = 1 then
        pairEncode
          (mask T H x.length (pairFstD (T.gen.runAtL x.length [] r))
            (pairSndD (T.gen.runAtL x.length [] r)) (pairFstD (hist.headD [])) (y.getD 0 false))
          (mask T H x.length (pairFstD (T.gen.runAtL x.length [] r))
            (pairSndD (T.gen.runAtL x.length [] r)) (pairSndD (hist.headD [])) (y.getD 1 false))
      else [] := rfl

/-- **Bob's next message** [PS10, Protocol 160.4] (the body of `otReceiver`): on one message
`i`, the pair of `f_i(w) = eval ⟨i, w⟩` (with `w` sampled from the first coin block) and the raw
sample `w'` (from the rest), ordered by the choice bit `b = z.headD false`; on two messages `[]`;
otherwise `H ⟨i, w⟩ ⊕ z_b`. -/
def receiverNext (x z r : List Bool) (hist : List (List Bool)) : List Bool :=
  if hist.length = 1 then
    if z.headD false then
      pairEncode (T.sample.runAtL x.length (hist.headD []) (r.drop (T.sample.coins.eval x.length)))
        (T.eval (pairEncode (hist.headD [])
          (T.sample.runAtL x.length (hist.headD []) (r.take (T.sample.coins.eval x.length)))))
    else
      pairEncode (T.eval (pairEncode (hist.headD [])
          (T.sample.runAtL x.length (hist.headD []) (r.take (T.sample.coins.eval x.length)))))
        (T.sample.runAtL x.length (hist.headD []) (r.drop (T.sample.coins.eval x.length)))
  else if hist.length = 2 then []
  else List.zipWith xor (H (pairEncode (hist.headD [])
      (T.sample.runAtL x.length (hist.headD []) (r.take (T.sample.coins.eval x.length)))))
    (if z.headD false then pairSndD (hist.getD 1 []) else pairFstD (hist.getD 1 []))

/-- The defining equation of `receiverNext`: `[i]` ↦ the ordered pair, two messages ↦ `[]`,
else `H ⟨i, w⟩ ⊕ z_b`, i.e. `receiverNext T H x z r hist = if |hist| = 1 then P else
if |hist| = 2 then [] else H ⟨i, w⟩ ⊕ z_b` with `P` the pair `⟨f_i(w), w'⟩` (or `⟨w', f_i(w)⟩`
when `b`), `i = hist.headD []` and `z_b` read off `hist.getD 1 []`. -/
theorem receiverNext_eq (x z r : List Bool) (hist : List (List Bool)) :
    receiverNext T H x z r hist =
      if hist.length = 1 then
        if z.headD false then
          pairEncode
            (T.sample.runAtL x.length (hist.headD []) (r.drop (T.sample.coins.eval x.length)))
            (T.eval (pairEncode (hist.headD [])
              (T.sample.runAtL x.length (hist.headD []) (r.take (T.sample.coins.eval x.length)))))
        else
          pairEncode (T.eval (pairEncode (hist.headD [])
              (T.sample.runAtL x.length (hist.headD []) (r.take (T.sample.coins.eval x.length)))))
            (T.sample.runAtL x.length (hist.headD []) (r.drop (T.sample.coins.eval x.length)))
      else if hist.length = 2 then []
      else List.zipWith xor (H (pairEncode (hist.headD [])
          (T.sample.runAtL x.length (hist.headD []) (r.take (T.sample.coins.eval x.length)))))
        (if z.headD false then pairSndD (hist.getD 1 []) else pairFstD (hist.getD 1 [])) := rfl

/-- **A protocol of the shape of Protocol 160.4** [PS10]: `P.next = senderNext T H`,
`V.next = receiverNext T H`, `P.coins = coins_Gen`, `V.coins = coins_Sample + coins_Sample`,
five messages, Alice first. -/
def IsOT (π : Protocol) : Prop :=
  π.P.next = senderNext T H ∧ π.V.next = receiverNext T H ∧ π.P.coins = T.gen.coins ∧
    π.V.coins = .add T.sample.coins T.sample.coins ∧ π.rounds = .const 5 ∧
      π.verifierFirst = false

/-- The defining property of `IsOT`: `IsOT T H π` iff the six field equations hold,
`IsOT T H π ↔ P.next = senderNext T H ∧ V.next = receiverNext T H ∧ P.coins = coins_Gen ∧
V.coins = coins_Sample + coins_Sample ∧ rounds = 5 ∧ verifierFirst = false`. -/
theorem isOT_iff (π : Protocol) :
    IsOT T H π ↔
      π.P.next = senderNext T H ∧ π.V.next = receiverNext T H ∧ π.P.coins = T.gen.coins ∧
        π.V.coins = .add T.sample.coins T.sample.coins ∧ π.rounds = .const 5 ∧
          π.verifierFirst = false := Iff.rfl

/-! ### Messages on short histories -/

/-- Alice's first message is the index: `senderNext T H x y r [] = fst Gen(1^{|x|}; r)`. -/
theorem senderNext_nil (x y r : List Bool) :
    senderNext T H x y r [] = pairFstD (T.gen.runAtL x.length [] r) := by
  rw [senderNext_eq, if_pos List.length_nil]

/-- Alice's second message is the pair of masks:
`senderNext T H x y r [m] = ⟨mask (fst m) y₀, mask (snd m) y₁⟩`. -/
theorem senderNext_single (x y r m : List Bool) :
    senderNext T H x y r [m] =
      pairEncode
        (mask T H x.length (pairFstD (T.gen.runAtL x.length [] r))
          (pairSndD (T.gen.runAtL x.length [] r)) (pairFstD m) (y.getD 0 false))
        (mask T H x.length (pairFstD (T.gen.runAtL x.length [] r))
          (pairSndD (T.gen.runAtL x.length [] r)) (pairSndD m) (y.getD 1 false)) := by
  rw [senderNext_eq, if_neg (by simp), if_pos List.length_singleton, List.headD_cons]

/-- Alice's third message is empty: `senderNext T H x y r [m, m'] = []`. -/
theorem senderNext_pair (x y r m m' : List Bool) : senderNext T H x y r [m, m'] = [] := by
  rw [senderNext_eq, if_neg (by simp), if_neg (by simp)]

/-- Bob's first message is the ordered pair `⟨f_i(w), w'⟩` (or `⟨w', f_i(w)⟩` when `b`):
`receiverNext T H x z r [i] = if b then ⟨w', eval ⟨i, w⟩⟩ else ⟨eval ⟨i, w⟩, w'⟩` with
`w = Sample(1^{|x|}, i; r.take coins_Sample)`, `w' = Sample(1^{|x|}, i; r.drop coins_Sample)`
and `b = z.headD false`. -/
theorem receiverNext_single (x z r i : List Bool) :
    receiverNext T H x z r [i] =
      if z.headD false then
        pairEncode (T.sample.runAtL x.length i (r.drop (T.sample.coins.eval x.length)))
          (T.eval (pairEncode i
            (T.sample.runAtL x.length i (r.take (T.sample.coins.eval x.length)))))
      else
        pairEncode
          (T.eval (pairEncode i
            (T.sample.runAtL x.length i (r.take (T.sample.coins.eval x.length)))))
          (T.sample.runAtL x.length i (r.drop (T.sample.coins.eval x.length))) := by
  rw [receiverNext_eq, if_pos List.length_singleton, List.headD_cons]

/-- Bob's second message is empty: `receiverNext T H x z r [m, m'] = []`. -/
theorem receiverNext_pair (x z r m m' : List Bool) : receiverNext T H x z r [m, m'] = [] := by
  rw [receiverNext_eq, if_neg (by simp), if_pos (by simp)]

/-! ### The five moves -/

/-- **The five moves of a prover-first execution** [PS10, §4.4]: with
`m₁ = P([])`, `m₂ = V([m₁])`, `m₃ = P([m₂])`, `m₄ = V([m₁, m₃])`, `m₅ = P([m₂, m₄])`,
`exec P V false x zP zV rP rV 5 = ([m₂, m₄], [m₁, m₃, m₅])`. -/
theorem exec_five (P V : Strategy) (x zP zV rP rV : List Bool) {m₁ m₂ m₃ m₄ m₅ : List Bool}
    (h₁ : P.next x zP rP [] = m₁) (h₂ : V.next x zV rV [m₁] = m₂)
    (h₃ : P.next x zP rP [m₂] = m₃) (h₄ : V.next x zV rV [m₁, m₃] = m₄)
    (h₅ : P.next x zP rP [m₂, m₄] = m₅) :
    exec P V false x zP zV rP rV 5 = ([m₂, m₄], [m₁, m₃, m₅]) := by
  simp only [exec_succ, exec_zero, moverIsV_false]
  simp [h₁, h₂, h₃, h₄, h₅]

/-- **The transcript of a protocol of the shape of Protocol 160.4**: with
`i = fst Gen(1^{|x|}; r₁)`, `y = receiverNext [i]` and `z = senderNext [y]`, the messages received
are `([y, []], [i, z, []])`. -/
theorem transcriptWith_isOT {π : Protocol} (hπ : IsOT T H π) (x y z : List Bool)
    (r : π.ExecCoins π.P x) :
    π.transcriptWith π.P x y z r =
      ([receiverNext T H x z (List.ofFn r.2)
          [pairFstD (T.gen.runAtL x.length [] (List.ofFn r.1))], []],
        [pairFstD (T.gen.runAtL x.length [] (List.ofFn r.1)),
          senderNext T H x y (List.ofFn r.1) [receiverNext T H x z (List.ofFn r.2)
            [pairFstD (T.gen.runAtL x.length [] (List.ofFn r.1))]], []]) := by
  obtain ⟨hP, hV, -, -, hr, hf⟩ := (isOT_iff T H π).1 hπ
  rw [Protocol.transcriptWith_eq, hr, hf, PolyExpr.eval_const]
  exact exec_five _ _ _ _ _ _ _ (by rw [hP, senderNext_nil]) (by rw [hV]) (by rw [hP])
    (by rw [hV, receiverNext_pair]) (by rw [hP, senderNext_pair])

end TCSlib.Cryptography.SecureComputation.OT

## ===== TCSlib/Cryptography/SecureComputation/ObliviousTransfer/Efficiency.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.ObliviousTransfer.Shape

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Oblivious transfer: Protocol 160.4 runs in polynomial time

Both parties of a protocol of the shape of [PS10, Protocol 160.4] (`OT.IsOT`) are efficient
strategies, and the messages of its honest executions are polynomially bounded: the
efficiency requirement `Functionality.PolyTime` of Definition 155.1 for `otFunctionality`.

Each next-message function branches on the number of messages received, which the raw machine
reads off the encoded history `⟨m₁, ⟨m₂, …⟩⟩` by emptiness tests of its iterated second
components (`polyTimeComputable_isNil`); the branches are compositions of `Gen`, the sampler and
the inverter (uniform machines, `NUPPT.polyTimeComputable_output`), the evaluator (`eval_poly`),
`H`, pairing and one XOR. The machines are `NUPPT.ofPolyTimeUniform` of these raw functions.

## Main definitions

* `OT.senderRaw`, `OT.receiverRaw`: the raw functions of the two parties' machines.

## Main results

* `OT.polyTimeComputable_senderRaw`, `OT.polyTimeComputable_receiverRaw`: they are
  polynomial-time.
* `OT.senderRaw_advInput`, `OT.receiverRaw_advInput`: they compute the next messages.
* `OT.length_runAtL_le`: the output-length bound of a machine on an untyped tape.
* `OT.polyTime_of_isOT`: [PS10, Protocol 160.4] runs in polynomial time.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2, Definition 155.1 and Protocol 160.4 (book pp. 155, 160).
-/

namespace TCSlib.Cryptography.SecureComputation.OT

open Complexity Turing TCSlib.Cryptography

variable (T : TrapdoorCollection) (H : List Bool → List Bool)

/-! ### Reading the encoded history -/

/-- The first message of a history is the first projection of its encoding:
`hist.headD [] = fst (encodeMsgs hist)` (`Strategy.pairFstD_encodeMsgs`). -/
theorem headD_eq_pairFstD (hist : List (List Bool)) :
    hist.headD [] = pairFstD (Strategy.encodeMsgs hist) :=
  (Strategy.pairFstD_encodeMsgs hist).symm

/-- The second projection of the empty word is empty, `pairSndD [] = []`
(`BinArith.iterate_pairSndD_nil` at `1`). -/
theorem pairSndD_nil' : pairSndD ([] : List Bool) = [] :=
  BinArith.iterate_pairSndD_nil 1

/-- The second message of a history is read off its encoding:
`hist.getD 1 [] = fst (snd (encodeMsgs hist))`. -/
theorem getD_one_eq (hist : List (List Bool)) :
    hist.getD 1 [] = pairFstD (pairSndD (Strategy.encodeMsgs hist)) := by
  rcases hist with _ | ⟨m, _ | ⟨m', rest⟩⟩
  · rw [Strategy.encodeMsgs_nil, pairSndD_nil', pairFstD_nil]
    rfl
  · rw [Strategy.encodeMsgs_cons, Strategy.encodeMsgs_nil, pairSndD_pairEncode, pairFstD_nil]
    rfl
  · rw [Strategy.encodeMsgs_cons, Strategy.encodeMsgs_cons, pairSndD_pairEncode,
      pairFstD_pairEncode]
    rfl

/-- A uniform machine's activation is its output on the layout with empty advice:
`A.runAtL n y r = A.output (layout 1^n y [] r)` (`NUPPT.runAtL_eq_output_layout`). -/
theorem runAtL_eq_layout {A : NUPPT} (hA : A.Uniform) (n : ℕ) (y r : List Bool) :
    A.runAtL n y r = A.output (NUPPT.layout (List.replicate n true) y [] r) := by
  rw [NUPPT.runAtL_eq_output_layout, NUPPT.Uniform.advice_eq hA]

/-- The raw layout of a strategy activation: `⟨⟨advInput n a, []⟩, r⟩ = layout 1^n a [] r`. -/
theorem advInput_layout (n : ℕ) (a r : List Bool) :
    pairEncode (pairEncode (NUPPT.advInput n a) []) r =
      NUPPT.layout (List.replicate n true) a [] r := by
  rw [NUPPT.advInput_eq, NUPPT.layout_eq]

/-! ### Alice's machine -/

/-- `Gen`'s output on the raw layout `z`: `Gen(inParam z; inCoins z)` with empty argument,
`genRaw T z = Gen.output (layout (inParam z) [] [] (inCoins z))`. -/
def genRaw (z : List Bool) : List Bool :=
  T.gen.output (NUPPT.layout (NUPPT.inParam z) [] [] (NUPPT.inCoins z))

/-- The defining equation of `genRaw`: `genRaw T z = Gen.output (layout (inParam z) [] []
(inCoins z))`. -/
theorem genRaw_eq (z : List Bool) :
    genRaw T z = T.gen.output (NUPPT.layout (NUPPT.inParam z) [] [] (NUPPT.inCoins z)) := rfl

/-- `genRaw` is polynomial-time: `PolyTimeComputable (genRaw T)`. -/
theorem polyTimeComputable_genRaw : PolyTimeComputable (genRaw T) :=
  (T.gen.polyTimeComputable_output.comp' (NUPPT.polyTimeComputable_layout
    NUPPT.polyTimeComputable_inParam (polyTimeComputable_const [])
    (polyTimeComputable_const []) NUPPT.polyTimeComputable_inCoins)).congr
    fun z => (genRaw_eq T z).symm

/-- Alice's mask on the raw layout `z`, for the element `yj` and the bit word `bt`:
`zipWith xor (H ⟨i, Inv(⟨t, yj⟩; 1^{inv})⟩) bt` with `⟨i, t⟩ = genRaw T z`. -/
def maskRaw (z yj bt : List Bool) : List Bool :=
  List.zipWith xor (H (pairEncode (pairFstD (genRaw T z))
    (T.inv.output (NUPPT.layout (NUPPT.inParam z) (pairEncode (pairSndD (genRaw T z)) yj) []
      (List.replicate (T.inv.coins.eval (NUPPT.inParam z).length) true))))) bt

/-- The defining equation of `maskRaw`: `maskRaw T H z yj bt =
zipWith xor (H ⟨i, Inv(inParam z, ⟨t, yj⟩; 1^{inv})⟩) bt` with `⟨i, t⟩ = genRaw T z`. -/
theorem maskRaw_eq (z yj bt : List Bool) :
    maskRaw T H z yj bt =
      List.zipWith xor (H (pairEncode (pairFstD (genRaw T z))
        (T.inv.output (NUPPT.layout (NUPPT.inParam z) (pairEncode (pairSndD (genRaw T z)) yj) []
          (List.replicate (T.inv.coins.eval (NUPPT.inParam z).length) true))))) bt := rfl

/-- The raw mask is polynomial-time in `z` for polynomial-time `yj` and `bt`:
`PolyTimeComputable (fun z => maskRaw T H z (Y z) (B z))` for polynomial-time `H`, `Y`, `B`.

**Proof sketch.** Pair the index (first projection of `genRaw`) with the inverter's output on
the layout of `1^n`, `⟨t, yj⟩` and the all-`true` tape (`polyTimeComputable_unaryPoly`), apply
`H`, pair with `bt` and XOR (`polyTimeComputable_pairXor`). -/
theorem polyTimeComputable_maskRaw {H : List Bool → List Bool} (hH : PolyTimeComputable H)
    {Y B : List Bool → List Bool} (hY : PolyTimeComputable Y) (hB : PolyTimeComputable B) :
    PolyTimeComputable fun z => maskRaw T H z (Y z) (B z) := by
  have hG := polyTimeComputable_genRaw T
  have hinv := T.inv.polyTimeComputable_output.comp' (NUPPT.polyTimeComputable_layout
    NUPPT.polyTimeComputable_inParam ((polyTimeComputable_pairSndD.comp' hG).pairEncode hY)
    (polyTimeComputable_const [])
    ((polyTimeComputable_unaryPoly T.inv.coins).comp' NUPPT.polyTimeComputable_inParam))
  have h := polyTimeComputable_pairXor.comp'
    ((hH.comp' ((polyTimeComputable_pairFstD.comp' hG).pairEncode hinv)).pairEncode hB)
  refine h.congr fun z => ?_
  rw [maskRaw_eq, pairFstD_pairEncode, pairSndD_pairEncode]

/-- **Alice's raw function** on `z = layout 1^{|x|} ⟨⟨x, y⟩, w⟩ [] r` with `w` the encoded
history: `fst (genRaw z)` if `w = []`; the two masks if `snd w = []`; else `[]`. -/
def senderRaw (z : List Bool) : List Bool :=
  if decide (pairSndD (NUPPT.inArg z) = []) then pairFstD (genRaw T z)
  else if decide (pairSndD (pairSndD (NUPPT.inArg z)) = []) then
    pairEncode
      (maskRaw T H z (pairFstD (pairFstD (pairSndD (NUPPT.inArg z))))
        [(pairSndD (pairFstD (NUPPT.inArg z))).headD false])
      (maskRaw T H z (pairSndD (pairFstD (pairSndD (NUPPT.inArg z))))
        [((pairSndD (pairFstD (NUPPT.inArg z))).drop 1).headD false])
  else []

/-- The defining equation of `senderRaw`: with `w = snd (inArg z)`, `fst (genRaw T z)` if
`w = []`, the two raw masks if `snd w = []`, else `[]`. -/
theorem senderRaw_eq (z : List Bool) :
    senderRaw T H z =
      if decide (pairSndD (NUPPT.inArg z) = []) then pairFstD (genRaw T z)
      else if decide (pairSndD (pairSndD (NUPPT.inArg z)) = []) then
        pairEncode
          (maskRaw T H z (pairFstD (pairFstD (pairSndD (NUPPT.inArg z))))
            [(pairSndD (pairFstD (NUPPT.inArg z))).headD false])
          (maskRaw T H z (pairSndD (pairFstD (pairSndD (NUPPT.inArg z))))
            [((pairSndD (pairFstD (NUPPT.inArg z))).drop 1).headD false])
      else [] := rfl

/-- **Alice's raw function is polynomial-time** (`polyTimeComputable_ite` on the two emptiness
tests `polyTimeComputable_isNil`, `polyTimeComputable_maskRaw`, `polyTimeComputable_headD`,
`polyTimeComputable_tail`): `PolyTimeComputable (senderRaw T H)` for polynomial-time `H`. -/
theorem polyTimeComputable_senderRaw {H : List Bool → List Bool} (hH : PolyTimeComputable H) :
    PolyTimeComputable (senderRaw T H) := by
  have hw := polyTimeComputable_pairSndD.comp' NUPPT.polyTimeComputable_inArg
  have hy := polyTimeComputable_pairSndD.comp'
    (polyTimeComputable_pairFstD.comp' NUPPT.polyTimeComputable_inArg)
  have hm := polyTimeComputable_pairFstD.comp' hw
  have h₁ := polyTimeComputable_maskRaw T hH (polyTimeComputable_pairFstD.comp' hm)
    (polyTimeComputable_headD.comp' hy)
  have h₂ := polyTimeComputable_maskRaw T hH (polyTimeComputable_pairSndD.comp' hm)
    (polyTimeComputable_headD.comp' (polyTimeComputable_tail.comp' hy))
  have h := polyTimeComputable_ite (polyTimeComputable_isNil.comp' hw)
    (polyTimeComputable_pairFstD.comp' (polyTimeComputable_genRaw T))
    (polyTimeComputable_ite (polyTimeComputable_isNil.comp' (polyTimeComputable_pairSndD.comp' hw))
      (h₁.pairEncode h₂) (polyTimeComputable_const []))
  exact h.congr fun z => (senderRaw_eq T H z).symm

/-- `Gen`'s output on the layout of an activation at `1^{|x|}` is `Gen(1^{|x|}; r)`:
`genRaw T (layout 1^n a [] r) = Gen.runAtL n [] r`. -/
theorem genRaw_layout (n : ℕ) (a r : List Bool) :
    genRaw T (NUPPT.layout (List.replicate n true) a [] r) = T.gen.runAtL n [] r := by
  rw [genRaw_eq, NUPPT.inParam_layout, NUPPT.inCoins_layout, runAtL_eq_layout T.gen_uniform]

/-- The raw mask on the layout of an activation is Alice's mask:
`maskRaw T H (layout 1^n a [] r) yj [c] = mask T H n i t yj c` with `⟨i, t⟩ = Gen(1^n; r)`. -/
theorem maskRaw_layout (n : ℕ) (a r yj : List Bool) (c : Bool) :
    maskRaw T H (NUPPT.layout (List.replicate n true) a [] r) yj [c] =
      mask T H n (pairFstD (T.gen.runAtL n [] r)) (pairSndD (T.gen.runAtL n [] r)) yj c := by
  rw [maskRaw_eq, genRaw_layout, NUPPT.inParam_layout, List.length_replicate, mask_eq,
    runAtL_eq_layout T.inv_uniform]

/-- `y.getD 0 false` is the head bit: `y.getD 0 false = y.headD false`. -/
theorem getD_zero_eq (y : List Bool) : y.getD 0 false = y.headD false := by
  cases y <;> rfl

/-- `y.getD 1 false` is the head bit of `y.drop 1`:
`y.getD 1 false = (y.drop 1).headD false`. -/
theorem getD_one_eq' (y : List Bool) : y.getD 1 false = (y.drop 1).headD false := by
  rcases y with _ | ⟨a, _ | ⟨b, t⟩⟩ <;> rfl

/-- **Alice's raw function computes her next message**: on the raw input of the activation
`⟨⟨advInput |x| ⟨⟨x, y⟩, encodeMsgs hist⟩, []⟩, r⟩` it returns `senderNext T H x y r hist`:
`senderRaw T H ⟨⟨advInput |x| ⟨⟨x, y⟩, encodeMsgs hist⟩, []⟩, r⟩ =
senderNext T H x y r hist`.

**Proof sketch.** Cases on the history: `[]` (the encoding is empty), `[m]` (its second
projection is empty), and two or more messages (neither is empty); `genRaw_layout`,
`maskRaw_layout` and `getD_zero_eq`, `getD_one_eq'` identify the branches with
`senderNext_nil`, `senderNext_single`, `senderNext_eq`. -/
theorem senderRaw_advInput (x y r : List Bool) (hist : List (List Bool)) :
    senderRaw T H (pairEncode (pairEncode (NUPPT.advInput x.length
      (pairEncode (pairEncode x y) (Strategy.encodeMsgs hist))) []) r) =
      senderNext T H x y r hist := by
  rw [advInput_layout, senderRaw_eq, NUPPT.inArg_layout, genRaw_layout, pairSndD_pairEncode,
    pairFstD_pairEncode, pairSndD_pairEncode]
  rcases hist with _ | ⟨m, _ | ⟨m', rest⟩⟩
  · rw [Strategy.encodeMsgs_nil, if_pos (by simp), senderNext_nil]
  · rw [Strategy.encodeMsgs_cons, Strategy.encodeMsgs_nil, if_neg (by simp [pairEncode_ne_nil]),
      pairSndD_pairEncode, if_pos (by simp), pairFstD_pairEncode, senderNext_single,
      maskRaw_layout, maskRaw_layout, getD_zero_eq, getD_one_eq']
  · rw [Strategy.encodeMsgs_cons, Strategy.encodeMsgs_cons, if_neg (by simp [pairEncode_ne_nil]),
      pairSndD_pairEncode, if_neg (by simp [pairEncode_ne_nil]), senderNext_eq,
      if_neg (by simp), if_neg (by simp)]

/-! ### Bob's machine -/

/-- Bob's sampled element on the raw layout `z`, at the index `i = fst w` of the encoded
history `w = snd (inArg z)`: the sampler on the first `coins_Sample(n)` coins. -/
def knownRaw (z : List Bool) : List Bool :=
  T.sample.output (NUPPT.layout (NUPPT.inParam z) (pairFstD (pairSndD (NUPPT.inArg z))) []
    ((NUPPT.inCoins z).take (T.sample.coins.eval (NUPPT.inParam z).length)))

/-- The defining equation of `knownRaw`: `knownRaw T z = Sample(inParam z, fst w;
(inCoins z).take coins_Sample(n))` with `w = snd (inArg z)`. -/
theorem knownRaw_eq (z : List Bool) :
    knownRaw T z =
      T.sample.output (NUPPT.layout (NUPPT.inParam z) (pairFstD (pairSndD (NUPPT.inArg z))) []
        ((NUPPT.inCoins z).take (T.sample.coins.eval (NUPPT.inParam z).length))) := rfl

/-- Bob's raw element on the raw layout `z`: the sampler on the coins after the first block,
`rawRaw T z = Sample(inParam z, fst w; (inCoins z).drop coins_Sample(n))` with
`w = snd (inArg z)`. -/
def rawRaw (z : List Bool) : List Bool :=
  T.sample.output (NUPPT.layout (NUPPT.inParam z) (pairFstD (pairSndD (NUPPT.inArg z))) []
    ((NUPPT.inCoins z).drop (T.sample.coins.eval (NUPPT.inParam z).length)))

/-- The defining equation of `rawRaw`: `rawRaw T z = Sample(inParam z, fst w;
(inCoins z).drop coins_Sample(n))` with `w = snd (inArg z)`. -/
theorem rawRaw_eq (z : List Bool) :
    rawRaw T z =
      T.sample.output (NUPPT.layout (NUPPT.inParam z) (pairFstD (pairSndD (NUPPT.inArg z))) []
        ((NUPPT.inCoins z).drop (T.sample.coins.eval (NUPPT.inParam z).length))) := rfl

/-- Bob's output on the raw layout `z`: `H ⟨i, w⟩ ⊕ z_b` with `z_b` the second or first
projection of the second message, by the choice bit `b`:
`outRaw T H z = zipWith xor (H ⟨fst w, knownRaw T z⟩) z_b` with `w = snd (inArg z)`. -/
def outRaw (z : List Bool) : List Bool :=
  List.zipWith xor (H (pairEncode (pairFstD (pairSndD (NUPPT.inArg z))) (knownRaw T z)))
    (if (pairSndD (pairFstD (NUPPT.inArg z))).headD false then
      pairSndD (pairFstD (pairSndD (pairSndD (NUPPT.inArg z))))
    else pairFstD (pairFstD (pairSndD (pairSndD (NUPPT.inArg z)))))

/-- The defining equation of `outRaw`: `outRaw T H z = zipWith xor (H ⟨fst w, knownRaw T z⟩) z_b`
with `z_b` the second or first projection of `fst (snd w)` by the choice bit. -/
theorem outRaw_eq (z : List Bool) :
    outRaw T H z =
      List.zipWith xor (H (pairEncode (pairFstD (pairSndD (NUPPT.inArg z))) (knownRaw T z)))
        (if (pairSndD (pairFstD (NUPPT.inArg z))).headD false then
          pairSndD (pairFstD (pairSndD (pairSndD (NUPPT.inArg z))))
        else pairFstD (pairFstD (pairSndD (pairSndD (NUPPT.inArg z))))) := rfl

/-- Bob's ordered pair on the raw layout `z`: `⟨w', eval ⟨i, w⟩⟩` if `b`, else
`⟨eval ⟨i, w⟩, w'⟩`, with `w = knownRaw T z`, `w' = rawRaw T z`, `i = fst (snd (inArg z))` and
`b = (snd (fst (inArg z))).headD false`. -/
def pairRaw (z : List Bool) : List Bool :=
  if (pairSndD (pairFstD (NUPPT.inArg z))).headD false then
    pairEncode (rawRaw T z)
      (T.eval (pairEncode (pairFstD (pairSndD (NUPPT.inArg z))) (knownRaw T z)))
  else
    pairEncode (T.eval (pairEncode (pairFstD (pairSndD (NUPPT.inArg z))) (knownRaw T z)))
      (rawRaw T z)

/-- The defining equation of `pairRaw`: `⟨rawRaw, eval ⟨fst w, knownRaw⟩⟩` if `b`, else
`⟨eval ⟨fst w, knownRaw⟩, rawRaw⟩`, i.e. `pairRaw T z = if b then ⟨rawRaw T z, eval ⟨fst w,
knownRaw T z⟩⟩ else ⟨eval ⟨fst w, knownRaw T z⟩, rawRaw T z⟩` with `w = snd (inArg z)`. -/
theorem pairRaw_eq (z : List Bool) :
    pairRaw T z =
      if (pairSndD (pairFstD (NUPPT.inArg z))).headD false then
        pairEncode (rawRaw T z)
          (T.eval (pairEncode (pairFstD (pairSndD (NUPPT.inArg z))) (knownRaw T z)))
      else
        pairEncode (T.eval (pairEncode (pairFstD (pairSndD (NUPPT.inArg z))) (knownRaw T z)))
          (rawRaw T z) := rfl

/-- **Bob's raw function** on `z = layout 1^{|x|} ⟨⟨x, z_B⟩, w⟩ [] r`: `outRaw` if `w = []`, the
pair if `snd w = []`, `[]` if `snd (snd w) = []`, else `outRaw`. -/
def receiverRaw (z : List Bool) : List Bool :=
  if decide (pairSndD (NUPPT.inArg z) = []) then outRaw T H z
  else if decide (pairSndD (pairSndD (NUPPT.inArg z)) = []) then pairRaw T z
  else if decide (pairSndD (pairSndD (pairSndD (NUPPT.inArg z))) = []) then []
  else outRaw T H z

/-- The defining equation of `receiverRaw`: with `w = snd (inArg z)`, `outRaw` if `w = []`,
`pairRaw` if `snd w = []`, `[]` if `snd (snd w) = []`, else `outRaw`. -/
theorem receiverRaw_eq (z : List Bool) :
    receiverRaw T H z =
      if decide (pairSndD (NUPPT.inArg z) = []) then outRaw T H z
      else if decide (pairSndD (pairSndD (NUPPT.inArg z)) = []) then pairRaw T z
      else if decide (pairSndD (pairSndD (pairSndD (NUPPT.inArg z))) = []) then []
      else outRaw T H z := rfl

/-- **Bob's raw function is polynomial-time**: the sampler on the two coin blocks
(`polyTimeComputable_pairTakePoly`, `polyTimeComputable_pairDropPoly`), `eval_poly`, `H`, XOR,
pairing, and branches on the choice bit and three emptiness tests (`polyTimeComputable_ite`):
`PolyTimeComputable (receiverRaw T H)` for polynomial-time `H`.

**Proof sketch.** Build `knownRaw`, `rawRaw`, `outRaw`, `pairRaw` from the projections and the
machines' output functions, then nest three `polyTimeComputable_ite`. -/
theorem polyTimeComputable_receiverRaw {H : List Bool → List Bool} (hH : PolyTimeComputable H) :
    PolyTimeComputable (receiverRaw T H) := by
  have hU := NUPPT.polyTimeComputable_inParam
  have hw := polyTimeComputable_pairSndD.comp' NUPPT.polyTimeComputable_inArg
  have hi := polyTimeComputable_pairFstD.comp' hw
  have hb := polyTimeComputable_headD.comp' (polyTimeComputable_pairSndD.comp'
    (polyTimeComputable_pairFstD.comp' NUPPT.polyTimeComputable_inArg))
  have htake := (polyTimeComputable_pairTakePoly T.sample.coins).comp'
    (hU.pairEncode NUPPT.polyTimeComputable_inCoins)
  have hdrop := (polyTimeComputable_pairDropPoly T.sample.coins).comp'
    (hU.pairEncode NUPPT.polyTimeComputable_inCoins)
  have hk : PolyTimeComputable (knownRaw T) :=
    (T.sample.polyTimeComputable_output.comp' (NUPPT.polyTimeComputable_layout hU hi
      (polyTimeComputable_const []) htake)).congr fun z => by
        rw [knownRaw_eq, pairFstD_pairEncode, pairSndD_pairEncode]
  have hr : PolyTimeComputable (rawRaw T) :=
    (T.sample.polyTimeComputable_output.comp' (NUPPT.polyTimeComputable_layout hU hi
      (polyTimeComputable_const []) hdrop)).congr fun z => by
        rw [rawRaw_eq, pairFstD_pairEncode, pairSndD_pairEncode]
  have he := T.eval_poly.comp' (hi.pairEncode hk)
  have hm := polyTimeComputable_pairFstD.comp' (polyTimeComputable_pairSndD.comp' hw)
  have ho : PolyTimeComputable (outRaw T H) :=
    (polyTimeComputable_pairXor.comp' ((hH.comp' (hi.pairEncode hk)).pairEncode
      (polyTimeComputable_ite hb (polyTimeComputable_pairSndD.comp' hm)
        (polyTimeComputable_pairFstD.comp' hm)))).congr fun z => by
      rw [outRaw_eq, pairFstD_pairEncode, pairSndD_pairEncode]
  have hp : PolyTimeComputable (pairRaw T) :=
    (polyTimeComputable_ite hb (hr.pairEncode he) (he.pairEncode hr)).congr
      fun z => (pairRaw_eq T z).symm
  have h := polyTimeComputable_ite (polyTimeComputable_isNil.comp' hw) ho
    (polyTimeComputable_ite (polyTimeComputable_isNil.comp' (polyTimeComputable_pairSndD.comp' hw))
      hp (polyTimeComputable_ite (polyTimeComputable_isNil.comp'
        (polyTimeComputable_pairSndD.comp' (polyTimeComputable_pairSndD.comp' hw)))
        (polyTimeComputable_const []) ho))
  exact h.congr fun z => (receiverRaw_eq T H z).symm

/-- On the layout of an activation, `knownRaw` is the sampler on the first coin block:
`knownRaw T (layout 1^n ⟨u, encodeMsgs hist⟩ [] r) =
Sample.runAtL n (hist.headD []) (r.take coins_Sample(n))`. -/
theorem knownRaw_layout (n : ℕ) (u r : List Bool) (hist : List (List Bool)) :
    knownRaw T
        (NUPPT.layout (List.replicate n true) (pairEncode u (Strategy.encodeMsgs hist)) [] r) =
      T.sample.runAtL n (hist.headD []) (r.take (T.sample.coins.eval n)) := by
  rw [knownRaw_eq, NUPPT.inParam_layout, NUPPT.inArg_layout, NUPPT.inCoins_layout,
    pairSndD_pairEncode, ← headD_eq_pairFstD, List.length_replicate,
    runAtL_eq_layout T.sample_uniform]

/-- On the layout of an activation, `rawRaw` is the sampler on the second coin block:
`rawRaw T (layout 1^n ⟨u, encodeMsgs hist⟩ [] r) =
Sample.runAtL n (hist.headD []) (r.drop coins_Sample(n))`. -/
theorem rawRaw_layout (n : ℕ) (u r : List Bool) (hist : List (List Bool)) :
    rawRaw T
        (NUPPT.layout (List.replicate n true) (pairEncode u (Strategy.encodeMsgs hist)) [] r) =
      T.sample.runAtL n (hist.headD []) (r.drop (T.sample.coins.eval n)) := by
  rw [rawRaw_eq, NUPPT.inParam_layout, NUPPT.inArg_layout, NUPPT.inCoins_layout,
    pairSndD_pairEncode, ← headD_eq_pairFstD, List.length_replicate,
    runAtL_eq_layout T.sample_uniform]

/-- **Bob's raw function computes his next message**: on the raw input of the activation
`⟨⟨advInput |x| ⟨⟨x, z⟩, encodeMsgs hist⟩, []⟩, r⟩` it returns `receiverNext T H x z r hist`:
`receiverRaw T H ⟨⟨advInput |x| ⟨⟨x, z⟩, encodeMsgs hist⟩, []⟩, r⟩ =
receiverNext T H x z r hist`.

**Proof sketch.** `knownRaw_layout`, `rawRaw_layout`, `headD_eq_pairFstD` and `getD_one_eq`
identify `outRaw` with the last branch of `receiverNext` on every history and `pairRaw` with the
first. Then cases on the history: `[]`, `[i]`, two messages, and three or more, by the emptiness
of the iterated second projections of the encoding. -/
theorem receiverRaw_advInput (x z r : List Bool) (hist : List (List Bool)) :
    receiverRaw T H (pairEncode (pairEncode (NUPPT.advInput x.length
      (pairEncode (pairEncode x z) (Strategy.encodeMsgs hist))) []) r) =
      receiverNext T H x z r hist := by
  rw [advInput_layout, receiverRaw_eq]
  have hout : outRaw T H (NUPPT.layout (List.replicate x.length true)
      (pairEncode (pairEncode x z) (Strategy.encodeMsgs hist)) [] r) =
      List.zipWith xor (H (pairEncode (hist.headD [])
        (T.sample.runAtL x.length (hist.headD []) (r.take (T.sample.coins.eval x.length)))))
        (if z.headD false then pairSndD (hist.getD 1 []) else pairFstD (hist.getD 1 [])) := by
    rw [outRaw_eq, knownRaw_layout, NUPPT.inArg_layout, pairSndD_pairEncode, pairFstD_pairEncode,
      pairSndD_pairEncode, ← headD_eq_pairFstD, getD_one_eq]
  have hpair : pairRaw T (NUPPT.layout (List.replicate x.length true)
      (pairEncode (pairEncode x z) (Strategy.encodeMsgs hist)) [] r) =
      receiverNext T H x z r [hist.headD []] := by
    rw [pairRaw_eq, knownRaw_layout, rawRaw_layout, NUPPT.inArg_layout, pairSndD_pairEncode,
      pairFstD_pairEncode, pairSndD_pairEncode, ← headD_eq_pairFstD, receiverNext_single]
  rw [hout, hpair, NUPPT.inArg_layout, pairSndD_pairEncode]
  rcases hist with _ | ⟨m, _ | ⟨m', _ | ⟨m'', rest⟩⟩⟩
  · rw [Strategy.encodeMsgs_nil, if_pos (by simp), receiverNext_eq,
      if_neg (show ¬([] : List (List Bool)).length = 1 by simp),
      if_neg (show ¬([] : List (List Bool)).length = 2 by simp)]
  · rw [Strategy.encodeMsgs_cons, Strategy.encodeMsgs_nil, if_neg (by simp [pairEncode_ne_nil]),
      pairSndD_pairEncode, if_pos (by simp), List.headD_cons]
  · rw [Strategy.encodeMsgs_cons, Strategy.encodeMsgs_cons, Strategy.encodeMsgs_nil,
      if_neg (by simp [pairEncode_ne_nil]), pairSndD_pairEncode,
      if_neg (by simp [pairEncode_ne_nil]), pairSndD_pairEncode, if_pos (by simp),
      receiverNext_pair]
  · rw [Strategy.encodeMsgs_cons, Strategy.encodeMsgs_cons, Strategy.encodeMsgs_cons,
      if_neg (by simp [pairEncode_ne_nil]), pairSndD_pairEncode,
      if_neg (by simp [pairEncode_ne_nil]), pairSndD_pairEncode,
      if_neg (by simp [pairEncode_ne_nil]), receiverNext_eq,
      if_neg (show ¬(m :: m' :: m'' :: rest).length = 1 by simp),
      if_neg (show ¬(m :: m' :: m'' :: rest).length = 2 by simp)]

/-! ### Message lengths -/

/-- **The output-length bound on an untyped tape of the right length**: `|A(1^n, y; r)| ≤
runLenPoly A Y (n)` whenever `|y| ≤ Y(n)` and `|r| = coins_A(n)` (the list form of
`NUPPT.length_runAt_le_runLenPoly`, through `List.ofFn_get`). -/
theorem length_runAtL_le (A : NUPPT) {Y : PolyExpr} (n : ℕ) {y r : List Bool}
    (hy : y.length ≤ Y.eval n) (hr : r.length = A.coins.eval n) :
    (A.runAtL n y r).length ≤ (A.runLenPoly Y).eval n := by
  have hr' : r.length = A.coinLen n := hr.trans (A.coinLen_eq n).symm
  have h := A.length_runAt_le_runLenPoly n hy (fun j => r.get (Fin.cast hr'.symm j))
  rwa [NUPPT.runAt_eq, ← List.ofFn_congr hr' r.get, List.ofFn_get] at h

/-- A mask has at most one bit: `|zipWith xor w [a]| ≤ 1`. -/
theorem length_zipWith_singleton_le (w : List Bool) (a : Bool) :
    (List.zipWith xor w [a]).length ≤ 1 := by
  rw [List.length_zipWith, List.length_singleton]
  exact Nat.min_le_right _ _

/-- Alice's mask has at most one bit: `|mask T H n i t yj a| ≤ 1`. -/
theorem length_mask_le (n : ℕ) (i t yj : List Bool) (a : Bool) :
    (mask T H n i t yj a).length ≤ 1 := by
  rw [mask_eq]
  exact length_zipWith_singleton_le _ a

/-- **The messages of Protocol 160.4 are polynomially bounded**: for a protocol of its shape there
is a polynomial `B` with `|msg| ≤ B(n)` for every message of every honest execution on `1^n`.

**Proof sketch.** The transcript is `([y, []], [i, z, []])` (`transcriptWith_isOT`). The index
has `|i| ≤ Q₁(n)` (`Gen`'s `runLenPoly`); the two samples have `≤ Q₂(n)` (the sampler's
`runLenPoly` at `Q₁`, the coin blocks having `coins_Sample(n)` bits); the evaluation has
`≤ Q₃(n)` (the evaluator's polynomial bound at `2Q₁ + 2 + Q₂`); so `|y| ≤ 3(Q₂ + Q₃) + 2`.
The masks have one bit each, so `|z| ≤ 5`. Take `B = Q₁ + (3(Q₂ + Q₃) + 2) + 5`. -/
theorem exists_messages_le {π : Protocol} (hπ : IsOT T H π) :
    ∃ B : PolyExpr, ∀ n (x : Fin (otFunctionality.inA.eval n) → Bool)
      (y : Fin (otFunctionality.inB.eval n) → Bool) (r : π.ExecCoins π.P (List.replicate n true)),
      ∀ msg ∈ (π.transcript (List.replicate n true) (List.ofFn x) (List.ofFn y) r).1 ++
          (π.transcript (List.replicate n true) (List.ofFn x) (List.ofFn y) r).2,
        msg.length ≤ B.eval n := by
  obtain ⟨-, -, hPc, hVc, -, -⟩ := (isOT_iff T H π).1 hπ
  obtain ⟨C, c, hC⟩ := T.eval_poly.output_length_le
  set Q₁ : PolyExpr := T.gen.runLenPoly (.const 0) with hQ₁
  set Q₂ : PolyExpr := T.sample.runLenPoly Q₁ with hQ₂
  set Q₃ : PolyExpr := (PolyExpr.normal C c).subst
    (.add (.add (.mul (.const 2) Q₁) (.const 2)) Q₂) with hQ₃
  refine ⟨.add Q₁ (.add (.add (.mul (.const 3) (.add Q₂ Q₃)) (.const 2)) (.const 5)),
    fun n x y r msg hmsg => ?_⟩
  suffices key : ∀ (w a b : List Bool) (r : π.ExecCoins π.P w),
      ∀ msg ∈ (π.transcript w a b r).1 ++ (π.transcript w a b r).2,
        msg.length ≤ (PolyExpr.add Q₁ (.add (.add (.mul (.const 3) (.add Q₂ Q₃)) (.const 2))
          (.const 5))).eval w.length by
    have h := key _ _ _ r msg hmsg
    rwa [List.length_replicate] at h
  intro w a b r msg hmsg
  rw [Protocol.transcript_eq_transcriptWith, transcriptWith_isOT T H hπ] at hmsg
  -- the coin lengths
  have hrA : (List.ofFn r.1).length = T.gen.coins.eval w.length := by
    rw [List.length_ofFn, Strategy.coinLen_eq, hPc]
  have hrB : (List.ofFn r.2).length =
      T.sample.coins.eval w.length + T.sample.coins.eval w.length := by
    rw [List.length_ofFn, Strategy.coinLen_eq, hVc, PolyExpr.eval_add]
  -- the index
  set i := pairFstD (T.gen.runAtL w.length [] (List.ofFn r.1)) with hi_def
  have hi : i.length ≤ Q₁.eval w.length :=
    (length_pairFstD_le _).trans (length_runAtL_le T.gen w.length (by simp) hrA)
  -- the two samples
  have hk : (T.sample.runAtL w.length i
      ((List.ofFn r.2).take (T.sample.coins.eval w.length))).length ≤ Q₂.eval w.length :=
    length_runAtL_le T.sample w.length hi (by rw [List.length_take, hrB]; omega)
  have hd : (T.sample.runAtL w.length i
      ((List.ofFn r.2).drop (T.sample.coins.eval w.length))).length ≤ Q₂.eval w.length :=
    length_runAtL_le T.sample w.length hi (by rw [List.length_drop, hrB]; omega)
  -- the evaluation
  have he : (T.eval (pairEncode i (T.sample.runAtL w.length i
      ((List.ofFn r.2).take (T.sample.coins.eval w.length))))).length ≤ Q₃.eval w.length := by
    refine (hC _).trans ?_
    rw [hQ₃, PolyExpr.eval_subst, PolyExpr.eval_normal]
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    simp only [length_pairEncode, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    omega
  have hB : ∀ k, k ≤ Q₁.eval w.length + (3 * (Q₂.eval w.length + Q₃.eval w.length) + 2) + 5 →
      k ≤ (PolyExpr.add Q₁ (.add (.add (.mul (.const 3) (.add Q₂ Q₃)) (.const 2))
        (.const 5))).eval w.length := by
    intro k hk'
    simpa only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const] using hk'
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hmsg
  refine hB _ ?_
  rcases hmsg with h | h | h | h | h <;> subst h
  · -- Bob's pair
    rw [receiverNext_single]
    split_ifs <;> simp only [length_pairEncode] <;> omega
  · simp
  · omega
  · -- Alice's masks
    rw [senderNext_single, length_pairEncode]
    refine le_trans (Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul_left 2
      (length_mask_le T H _ _ _ _ _)) 2) (length_mask_le T H _ _ _ _ _)) ?_
    omega
  · simp

/-- **Protocol 160.4 runs in polynomial time** [PS10, Definition 155.1, efficiency]: for a
protocol of its shape with a polynomial-time `H`, both parties are efficient strategies (the
machines `ofPolyTimeUniform` of `senderRaw` and `receiverRaw`) and the honest messages are
polynomially bounded (`exists_messages_le`): `IsOT T H π → otFunctionality.PolyTime π`. -/
theorem polyTime_of_isOT {H : List Bool → List Bool} (hH : PolyTimeComputable H) {π : Protocol}
    (hπ : IsOT T H π) : otFunctionality.PolyTime π := by
  obtain ⟨hP, hV, hPc, hVc, -, -⟩ := (isOT_iff T H π).1 hπ
  refine (Functionality.polyTime_iff _ _).2 ⟨?_, ?_, exists_messages_le T H hπ⟩
  · refine (Strategy.efficient_iff _).2 ⟨NUPPT.ofPolyTimeUniform (polyTimeComputable_senderRaw T hH)
      T.gen.coins, NUPPT.ofPolyTimeUniform_uniform _ _,
      hPc.trans (NUPPT.coins_ofPolyTimeUniform _ _).symm, fun x z r hist => ?_⟩
    rw [Strategy.ofNUPPT_next, NUPPT.runAtL_ofPolyTimeUniform, senderRaw_advInput, hP]
  · refine (Strategy.efficient_iff _).2 ⟨NUPPT.ofPolyTimeUniform
      (polyTimeComputable_receiverRaw T hH) (.add T.sample.coins T.sample.coins),
      NUPPT.ofPolyTimeUniform_uniform _ _,
      hVc.trans (NUPPT.coins_ofPolyTimeUniform _ _).symm, fun x z r hist => ?_⟩
    rw [Strategy.ofNUPPT_next, NUPPT.runAtL_ofPolyTimeUniform, receiverRaw_advInput, hV]

end TCSlib.Cryptography.SecureComputation.OT

## ===== TCSlib/Cryptography/SecureComputation/ObliviousTransfer/Simulators.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.ObliviousTransfer.Shape

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Oblivious transfer: the shape of the simulators of Proposition 161.5

The simulators `S_A` and `S_B` of [PS10, Proposition 161.5] restated for the helper modules
(which cannot import `SecureComputation/ObliviousTransfer.lean`, the owned file that imports them):
the coin segments, the simulated index and samples, and the two simulated views, with the
predicates `OT.IsSimA` and `OT.IsSimB` that the owned file proves for `otSimA` and `otSimB`.
On a tape assembled from typed coin blocks (`OT.splitLen`), the simulated views are computed
explicitly (`OT.simAView_layout`, `OT.simBView_layout`).

## Main definitions

* `OT.splitLen`: a coin string of length `c = a + b` as an `a`-bit and a `b`-bit string.
* `OT.simSeg`, `OT.simIndex`, `OT.simSampled`: a coin segment, the simulated index and a
  simulated sample (the bodies of `coinSeg`, `simIdx`, `simSample`).
* `OT.simAView`, `OT.simZbit`, `OT.simZpair`, `OT.simBView`: the simulators' raw functions (the
  bodies of `otSimAFun`, `otSimZb`, `otSimZ`, `otSimBFun`).
* `OT.IsSimA`, `OT.IsSimB`: machines of the simulators' shape.

## Main results

* `OT.splitLen_symm_ofFn`: the assembled tape is the concatenation of the blocks.
* `OT.simSeg_layout`, `OT.simIndex_layout`, `OT.simSampled_layout`: the pieces on such a tape.
* `OT.simAView_layout`, `OT.simBView_layout`: the simulated views on such a tape.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2.4, Proposition 161.5 (book pp. 160–162).
-/

namespace TCSlib.Cryptography.SecureComputation.OT

open Complexity Turing TCSlib.Cryptography

variable (T : TrapdoorCollection) (H : List Bool → List Bool)

/-! ### Splitting coin strings -/

/-- **A coin string of length `c = a + b` split** into its first `a` and last `b` bits:
`splitCoins a b` after the length cast `Fin c ≃ Fin (a + b)`. -/
def splitLen {a b c : ℕ} (h : c = a + b) : (Fin c → Bool) ≃ (Fin a → Bool) × (Fin b → Bool) :=
  (Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)).trans (splitCoins a b)

/-- The tape assembled from two blocks is their concatenation:
`ofFn ((splitLen h).symm (r₁, r₂)) = ofFn r₁ ++ ofFn r₂` (`ofFn_splitCoins_symm`). -/
theorem splitLen_symm_ofFn {a b c : ℕ} (h : c = a + b) (p : (Fin a → Bool) × (Fin b → Bool)) :
    List.ofFn ((splitLen h).symm p) = List.ofFn p.1 ++ List.ofFn p.2 := by
  rw [← ofFn_splitCoins_symm]
  exact (List.ofFn_congr h _).trans rfl

/-! ### The simulators restated -/

/-- The coin segment of length `q(n)` after the first `p(n)` coins of a raw layout `z` (the body
of `coinSeg`): `(inCoins z).drop p(|inParam z|) |>.take q(|inParam z|)`. -/
def simSeg (p q : PolyExpr) (z : List Bool) : List Bool :=
  ((NUPPT.inCoins z).drop (p.eval (NUPPT.inParam z).length)).take (q.eval (NUPPT.inParam z).length)

/-- The defining equation of `simSeg`: `simSeg p q z =
((inCoins z).drop p(|inParam z|)).take q(|inParam z|)`. -/
theorem simSeg_eq (p q : PolyExpr) (z : List Bool) :
    simSeg p q z =
      ((NUPPT.inCoins z).drop (p.eval (NUPPT.inParam z).length)).take
        (q.eval (NUPPT.inParam z).length) := rfl

/-- The simulated index (the body of `simIdx`):
`simIndex T z = fst Gen(inParam z; simSeg 0 coins_Gen z)`. -/
def simIndex (z : List Bool) : List Bool :=
  pairFstD (T.gen.output (NUPPT.layout (NUPPT.inParam z) [] []
    (simSeg (.const 0) T.gen.coins z)))

/-- The defining equation of `simIndex`: `simIndex T z =
fst Gen.output (layout (inParam z) [] [] (simSeg 0 coins_Gen z))`. -/
theorem simIndex_eq (z : List Bool) :
    simIndex T z = pairFstD (T.gen.output (NUPPT.layout (NUPPT.inParam z) [] []
      (simSeg (.const 0) T.gen.coins z))) := rfl

/-- A simulated sample after `p(n)` coins (the body of `simSample`):
`simSampled T p z = Sample(inParam z, simIndex z; simSeg p coins_Sample z)`. -/
def simSampled (p : PolyExpr) (z : List Bool) : List Bool :=
  T.sample.output (NUPPT.layout (NUPPT.inParam z) (simIndex T z) [] (simSeg p T.sample.coins z))

/-- The defining equation of `simSampled`: `simSampled T p z =
Sample.output (layout (inParam z) (simIndex T z) [] (simSeg p coins_Sample z))`. -/
theorem simSampled_eq (p : PolyExpr) (z : List Bool) :
    simSampled T p z =
      T.sample.output (NUPPT.layout (NUPPT.inParam z) (simIndex T z) []
        (simSeg p T.sample.coins z)) := rfl

/-- **`S_A`'s raw function** [PS10, Proposition 161.5] (the body of `otSimAFun`):
`simAView T z = ⟨⟨1^n, ⟨a₁, a₂⟩⟩, ⟨r_Gen, [⟨y₁, y₂⟩, []]⟩⟩` with two simulated samples
`y₁, y₂`. -/
def simAView (z : List Bool) : List Bool :=
  pairEncode (pairEncode (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)))
    (pairEncode (simSeg (.const 0) T.gen.coins z)
      (pairEncode (pairEncode (simSampled T T.gen.coins z)
          (simSampled T (.add T.gen.coins T.sample.coins) z))
        (pairEncode [] [])))

/-- The defining equation of `simAView`: `simAView T z = ⟨⟨inParam z, fst (inArg z)⟩,
⟨simSeg 0 coins_Gen z, [⟨y₁, y₂⟩, []]⟩⟩` with the two simulated samples `y₁, y₂`. -/
theorem simAView_eq (z : List Bool) :
    simAView T z =
      pairEncode (pairEncode (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)))
        (pairEncode (simSeg (.const 0) T.gen.coins z)
          (pairEncode (pairEncode (simSampled T T.gen.coins z)
              (simSampled T (.add T.gen.coins T.sample.coins) z))
            (pairEncode [] []))) := rfl

/-- `S_B`'s mask `z_b = h(x) ⊕ a_b` (the body of `otSimZb`). -/
def simZbit (z : List Bool) : List Bool :=
  List.zipWith xor (H (pairEncode (simIndex T z) (simSampled T T.gen.coins z)))
    (pairSndD (NUPPT.inArg z))

/-- The defining equation of `simZbit`: `simZbit T H z =
zipWith xor (H ⟨simIndex T z, simSampled T coins_Gen z⟩) (snd (inArg z))`. -/
theorem simZbit_eq (z : List Bool) :
    simZbit T H z =
      List.zipWith xor (H (pairEncode (simIndex T z) (simSampled T T.gen.coins z)))
        (pairSndD (NUPPT.inArg z)) := rfl

/-- `S_B`'s pair `(z₁, z₂)` (the body of `otSimZ`): `z_b` from `simZbit`, `z_{1−b}` one coin,
`simZpair T H z = ⟨c, z_b⟩` if the choice bit is set, else `⟨z_b, c⟩`. -/
def simZpair (z : List Bool) : List Bool :=
  if (pairFstD (NUPPT.inArg z)).headD false then
    pairEncode (simSeg (.add T.gen.coins (.add T.sample.coins T.sample.coins)) (.const 1) z)
      (simZbit T H z)
  else
    pairEncode (simZbit T H z)
      (simSeg (.add T.gen.coins (.add T.sample.coins T.sample.coins)) (.const 1) z)

/-- The defining equation of `simZpair`: `⟨c, z_b⟩` if the choice bit is set, else `⟨z_b, c⟩`,
with `c` the last coin segment and `z_b = simZbit T H z`. -/
theorem simZpair_eq (z : List Bool) :
    simZpair T H z =
      if (pairFstD (NUPPT.inArg z)).headD false then
        pairEncode (simSeg (.add T.gen.coins (.add T.sample.coins T.sample.coins)) (.const 1) z)
          (simZbit T H z)
      else
        pairEncode (simZbit T H z)
          (simSeg (.add T.gen.coins (.add T.sample.coins T.sample.coins)) (.const 1) z) := rfl

/-- **`S_B`'s raw function** [PS10, Proposition 161.5] (the body of `otSimBFun`):
`simBView T H z = ⟨⟨1^n, [b]⟩, ⟨r_B, [i, ⟨z₁, z₂⟩, []]⟩⟩`. -/
def simBView (z : List Bool) : List Bool :=
  pairEncode (pairEncode (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)))
    (pairEncode (simSeg T.gen.coins (.add T.sample.coins T.sample.coins) z)
      (pairEncode (simIndex T z) (pairEncode (simZpair T H z) (pairEncode [] []))))

/-- The defining equation of `simBView`: `simBView T H z = ⟨⟨inParam z, fst (inArg z)⟩,
⟨simSeg coins_Gen (2 coins_Sample) z, [simIndex T z, simZpair T H z, []]⟩⟩`. -/
theorem simBView_eq (z : List Bool) :
    simBView T H z =
      pairEncode (pairEncode (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)))
        (pairEncode (simSeg T.gen.coins (.add T.sample.coins T.sample.coins) z)
          (pairEncode (simIndex T z) (pairEncode (simZpair T H z) (pairEncode [] [])))) := rfl

/-- **A machine of `S_A`'s shape**: coins `coins_Gen + (coins_Sample + coins_Sample)`, and
`S(1^n, y; r) = simAView T (layout 1^n y [] r)`. -/
def IsSimA (S : NUPPT) : Prop :=
  S.coins = .add T.gen.coins (.add T.sample.coins T.sample.coins) ∧
    ∀ n y (r : S.Coins n),
      S.runAt n y r = simAView T (NUPPT.layout (List.replicate n true) y [] (List.ofFn r))

/-- The defining property of `IsSimA`: `IsSimA T S` iff `S.coins = coins_Gen + (coins_Sample +
coins_Sample)` and `S(1^n, y; r) = simAView T (layout 1^n y [] r)`. -/
theorem isSimA_iff (S : NUPPT) :
    IsSimA T S ↔
      S.coins = .add T.gen.coins (.add T.sample.coins T.sample.coins) ∧
        ∀ n y (r : S.Coins n),
          S.runAt n y r = simAView T (NUPPT.layout (List.replicate n true) y [] (List.ofFn r)) :=
  Iff.rfl

/-- **A machine of `S_B`'s shape**: coins `coins_Gen + (coins_Sample + (coins_Sample + 1))`, and
`S(1^n, y; r) = simBView T H (layout 1^n y [] r)`. -/
def IsSimB (S : NUPPT) : Prop :=
  S.coins = .add T.gen.coins (.add T.sample.coins (.add T.sample.coins (.const 1))) ∧
    ∀ n y (r : S.Coins n),
      S.runAt n y r = simBView T H (NUPPT.layout (List.replicate n true) y [] (List.ofFn r))

/-- The defining property of `IsSimB`: `IsSimB T H S` iff its coins are `coins_Gen +
(coins_Sample + (coins_Sample + 1))` and `S(1^n, y; r) = simBView T H (layout 1^n y [] r)`. -/
theorem isSimB_iff (S : NUPPT) :
    IsSimB T H S ↔
      S.coins = .add T.gen.coins (.add T.sample.coins (.add T.sample.coins (.const 1))) ∧
        ∀ n y (r : S.Coins n),
          S.runAt n y r = simBView T H (NUPPT.layout (List.replicate n true) y [] (List.ofFn r)) :=
  Iff.rfl

/-! ### The simulators on assembled tapes -/

/-- A coin segment of a tape `A ++ (B ++ C)` with `|A| = p(|u|)` and `|B| = q(|u|)` is `B`. -/
theorem simSeg_layout {p q : PolyExpr} (u y α : List Bool) {A B : List Bool} (C : List Bool)
    (hA : A.length = p.eval u.length) (hB : B.length = q.eval u.length) :
    simSeg p q (NUPPT.layout u y α (A ++ (B ++ C))) = B := by
  rw [simSeg_eq, NUPPT.inCoins_layout, NUPPT.inParam_layout, List.drop_left' hA,
    List.take_left' hB]

/-- The typed tape of a machine as a list has the coin length: `|ofFn r| = coins_A(n)`. -/
theorem length_ofFn_coins (A : NUPPT) (n : ℕ) (r : A.Coins n) :
    (List.ofFn r).length = A.coins.eval n := by
  rw [List.length_ofFn, NUPPT.coinLen_eq]

/-- On a tape starting with `Gen`'s coins `r`, the simulated index is `index n r`:
`simIndex T (layout 1^n y [] (ofFn r ++ B)) = T.index n r`. -/
theorem simIndex_layout (n : ℕ) (y : List Bool) (r : T.gen.Coins n) (B : List Bool) :
    simIndex T (NUPPT.layout (List.replicate n true) y [] (List.ofFn r ++ B)) = T.index n r := by
  have h := simSeg_layout (p := .const 0) (q := T.gen.coins) (List.replicate n true) y [] B
    (A := []) (B := List.ofFn r) (by rw [PolyExpr.eval_const, List.length_nil])
    (by rw [length_ofFn_coins, List.length_replicate])
  rw [List.nil_append] at h
  rw [simIndex_eq, h, NUPPT.inParam_layout, Collection.index_eq, NUPPT.runAt_eq,
    NUPPT.runAtL_eq_output_layout, NUPPT.Uniform.advice_eq T.gen_uniform]

/-- On a tape `r ++ (A ++ (s ++ C))` with `|A| = p(n) - coins_Gen(n)`, the simulated sample
after `p(n)` coins is `Sample(1^n, index n r; s)`. -/
theorem simSampled_layout {p : PolyExpr} (n : ℕ) (y : List Bool) (r : T.gen.Coins n)
    (A : List Bool) (s : T.sample.Coins n) (C : List Bool)
    (hA : (List.ofFn r ++ A).length = p.eval n) :
    simSampled T p
        (NUPPT.layout (List.replicate n true) y [] (List.ofFn r ++ (A ++ (List.ofFn s ++ C)))) =
      T.sample.runAt n (T.index n r) s := by
  have h := simSeg_layout (p := p) (q := T.sample.coins) (List.replicate n true) y []
    (A := List.ofFn r ++ A) (B := List.ofFn s) C (by rw [hA, List.length_replicate])
    (by rw [length_ofFn_coins, List.length_replicate])
  rw [List.append_assoc] at h
  rw [simSampled_eq, h, NUPPT.inParam_layout, simIndex_layout,
    NUPPT.runAt_eq, NUPPT.runAtL_eq_output_layout, NUPPT.Uniform.advice_eq T.sample_uniform]

/-- **`S_A`'s view on the tape `r ++ (s₁ ++ s₂)`**:
`⟨⟨1^n, fst y⟩, ⟨r, [⟨Sample(i; s₁), Sample(i; s₂)⟩, []]⟩⟩` with `i = index n r`. -/
theorem simAView_layout (n : ℕ) (y : List Bool) (r : T.gen.Coins n)
    (s₁ s₂ : T.sample.Coins n) :
    simAView T (NUPPT.layout (List.replicate n true) y []
        (List.ofFn r ++ (List.ofFn s₁ ++ List.ofFn s₂))) =
      pairEncode (pairEncode (List.replicate n true) (pairFstD y))
        (pairEncode (List.ofFn r)
          (pairEncode (pairEncode (T.sample.runAt n (T.index n r) s₁)
              (T.sample.runAt n (T.index n r) s₂))
            (pairEncode [] []))) := by
  have h₀ := simSeg_layout (p := .const 0) (q := T.gen.coins) (List.replicate n true) y []
    (A := []) (B := List.ofFn r) (List.ofFn s₁ ++ List.ofFn s₂)
    (by rw [PolyExpr.eval_const, List.length_nil])
    (by rw [length_ofFn_coins, List.length_replicate])
  rw [List.nil_append] at h₀
  have h₁ := simSampled_layout T (p := T.gen.coins) n y r [] s₁ (List.ofFn s₂)
    (by rw [List.append_nil, length_ofFn_coins])
  have h₂ := simSampled_layout T (p := .add T.gen.coins T.sample.coins) n y r
    (List.ofFn s₁) s₂ [] (by rw [List.length_append, length_ofFn_coins, length_ofFn_coins,
      PolyExpr.eval_add])
  rw [List.nil_append] at h₁
  rw [List.append_nil] at h₂
  rw [simAView_eq, NUPPT.inParam_layout, NUPPT.inArg_layout, h₀, h₁, h₂]

/-- **`S_B`'s view on the tape `r ++ (s₁ ++ (s₂ ++ c))`**:
`⟨⟨1^n, fst y⟩, ⟨s₁ ++ s₂, [i, Z, []]⟩⟩` with `i = index n r`, `z_b = H ⟨i, Sample(i; s₁)⟩ ⊕ snd y`
and `Z = ⟨c, z_b⟩` if `(fst y).headD false`, else `⟨z_b, c⟩`.

**Proof sketch.** The coin segments of the tape are `s₁ ++ s₂` and `c` (`simSeg_layout`), the
simulated index is `index n r` (`simIndex_layout`) and the first simulated sample is
`Sample(i; s₁)` (`simSampled_layout`); rewrite `simBView`, `simZpair` and `simZbit` with them. -/
theorem simBView_layout (n : ℕ) (y : List Bool) (r : T.gen.Coins n)
    (s₁ s₂ : T.sample.Coins n) (c : Fin 1 → Bool) :
    simBView T H (NUPPT.layout (List.replicate n true) y []
        (List.ofFn r ++ (List.ofFn s₁ ++ (List.ofFn s₂ ++ List.ofFn c)))) =
      pairEncode (pairEncode (List.replicate n true) (pairFstD y))
        (pairEncode (List.ofFn s₁ ++ List.ofFn s₂)
          (pairEncode (T.index n r)
            (pairEncode
              (if (pairFstD y).headD false then
                pairEncode (List.ofFn c)
                  (List.zipWith xor (H (pairEncode (T.index n r)
                    (T.sample.runAt n (T.index n r) s₁))) (pairSndD y))
              else
                pairEncode (List.zipWith xor (H (pairEncode (T.index n r)
                    (T.sample.runAt n (T.index n r) s₁))) (pairSndD y))
                  (List.ofFn c))
              (pairEncode [] [])))) := by
  have hs := simSeg_layout (p := T.gen.coins) (q := .add T.sample.coins T.sample.coins)
    (List.replicate n true) y [] (A := List.ofFn r) (B := List.ofFn s₁ ++ List.ofFn s₂)
    (List.ofFn c) (by rw [length_ofFn_coins, List.length_replicate])
    (by rw [List.length_append, length_ofFn_coins, length_ofFn_coins, PolyExpr.eval_add,
      List.length_replicate])
  rw [List.append_assoc] at hs
  have hc := simSeg_layout (p := .add T.gen.coins (.add T.sample.coins T.sample.coins))
    (q := .const 1) (List.replicate n true) y []
    (A := List.ofFn r ++ (List.ofFn s₁ ++ List.ofFn s₂)) (B := List.ofFn c) []
    (by rw [List.length_append, List.length_append, length_ofFn_coins, length_ofFn_coins,
      length_ofFn_coins, PolyExpr.eval_add, PolyExpr.eval_add, List.length_replicate])
    (by rw [List.length_ofFn, PolyExpr.eval_const])
  rw [List.append_nil, List.append_assoc, List.append_assoc] at hc
  have hi := simIndex_layout T n y r (List.ofFn s₁ ++ (List.ofFn s₂ ++ List.ofFn c))
  have h₁ := simSampled_layout T (p := T.gen.coins) n y r [] s₁ (List.ofFn s₂ ++ List.ofFn c)
    (by rw [List.append_nil, length_ofFn_coins])
  rw [List.nil_append] at h₁
  rw [simBView_eq, simZpair_eq, simZbit_eq, NUPPT.inParam_layout, NUPPT.inArg_layout, hs, hc,
    hi, h₁]

/-! ### The coin spaces -/

/-- **The real coins of a protocol of the shape of Protocol 160.4**: Alice's tape is `Gen`'s
coins and Bob's two sampler blocks, `ExecCoins ≃ Coins_Gen × (Coins_Sample × Coins_Sample)`. -/
def realCoins {π : Protocol} (hπ : IsOT T H π) (n : ℕ) :
    π.ExecCoins π.P (List.replicate n true) ≃
      T.gen.Coins n × (T.sample.Coins n × T.sample.Coins n) :=
  Equiv.prodCongr
    (Equiv.arrowCongr (finCongr (by
      rw [Strategy.coinLen_eq, ((isOT_iff T H π).1 hπ).2.2.1, List.length_replicate,
        NUPPT.coinLen_eq])) (Equiv.refl Bool))
    (splitLen (by
      rw [Strategy.coinLen_eq, ((isOT_iff T H π).1 hπ).2.2.2.1, List.length_replicate,
        PolyExpr.eval_add, NUPPT.coinLen_eq]))

/-- Alice's real tape is `Gen`'s coins: `ofFn ((realCoins hπ n).symm p).1 = ofFn p.1`. -/
theorem realCoins_symm_fst_ofFn {π : Protocol} (hπ : IsOT T H π) (n : ℕ)
    (p : T.gen.Coins n × (T.sample.Coins n × T.sample.Coins n)) :
    List.ofFn ((realCoins T H hπ n).symm p).1 = List.ofFn p.1 :=
  (List.ofFn_congr (by rw [Strategy.coinLen_eq, ((isOT_iff T H π).1 hπ).2.2.1,
    List.length_replicate, NUPPT.coinLen_eq]) _).trans rfl

/-- Bob's real tape is the two sampler blocks:
`ofFn ((realCoins hπ n).symm p).2 = ofFn p.2.1 ++ ofFn p.2.2`. -/
theorem realCoins_symm_snd_ofFn {π : Protocol} (hπ : IsOT T H π) (n : ℕ)
    (p : T.gen.Coins n × (T.sample.Coins n × T.sample.Coins n)) :
    List.ofFn ((realCoins T H hπ n).symm p).2 = List.ofFn p.2.1 ++ List.ofFn p.2.2 :=
  splitLen_symm_ofFn _ p.2

/-- **`S_A`'s coins**: `Coins_S ≃ Coins_Gen × (Coins_Sample × Coins_Sample)` for a machine of
`S_A`'s shape. -/
def simACoins {S : NUPPT} (hS : IsSimA T S) (n : ℕ) :
    S.Coins n ≃ T.gen.Coins n × (T.sample.Coins n × T.sample.Coins n) :=
  (splitLen (by rw [NUPPT.coinLen_eq, ((isSimA_iff T S).1 hS).1, PolyExpr.eval_add,
    NUPPT.coinLen_eq])).trans
    (Equiv.prodCongr (Equiv.refl _) (splitLen (by rw [PolyExpr.eval_add, NUPPT.coinLen_eq])))

/-- `S_A`'s tape from blocks: `ofFn ((simACoins hS n).symm p) = ofFn p.1 ++ (ofFn p.2.1 ++
ofFn p.2.2)`. -/
theorem simACoins_symm_ofFn {S : NUPPT} (hS : IsSimA T S) (n : ℕ)
    (p : T.gen.Coins n × (T.sample.Coins n × T.sample.Coins n)) :
    List.ofFn ((simACoins T hS n).symm p) =
      List.ofFn p.1 ++ (List.ofFn p.2.1 ++ List.ofFn p.2.2) := by
  rw [simACoins, Equiv.symm_trans_apply, splitLen_symm_ofFn, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.refl_symm, Equiv.refl_apply,
    splitLen_symm_ofFn]

/-- **`S_B`'s coins**: `Coins_S ≃ Coins_Gen × (Coins_Sample × (Coins_Sample × {0,1}))` for a
machine of `S_B`'s shape. -/
def simBCoins {S : NUPPT} (hS : IsSimB T H S) (n : ℕ) :
    S.Coins n ≃ T.gen.Coins n × (T.sample.Coins n × (T.sample.Coins n × (Fin 1 → Bool))) :=
  (splitLen (by rw [NUPPT.coinLen_eq, ((isSimB_iff T H S).1 hS).1, PolyExpr.eval_add,
    NUPPT.coinLen_eq])).trans
    (Equiv.prodCongr (Equiv.refl _) ((splitLen (by rw [PolyExpr.eval_add, NUPPT.coinLen_eq])).trans
      (Equiv.prodCongr (Equiv.refl _)
        (splitLen (by rw [PolyExpr.eval_add, NUPPT.coinLen_eq, PolyExpr.eval_const])))))

/-- `S_B`'s tape from blocks: `ofFn ((simBCoins hS n).symm p) =
ofFn p.1 ++ (ofFn p.2.1 ++ (ofFn p.2.2.1 ++ ofFn p.2.2.2))`. -/
theorem simBCoins_symm_ofFn {S : NUPPT} (hS : IsSimB T H S) (n : ℕ)
    (p : T.gen.Coins n × (T.sample.Coins n × (T.sample.Coins n × (Fin 1 → Bool)))) :
    List.ofFn ((simBCoins T H hS n).symm p) =
      List.ofFn p.1 ++ (List.ofFn p.2.1 ++ (List.ofFn p.2.2.1 ++ List.ofFn p.2.2.2)) := by
  rw [simBCoins, Equiv.symm_trans_apply, splitLen_symm_ofFn, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.refl_symm, Equiv.refl_apply,
    Equiv.symm_trans_apply, splitLen_symm_ofFn, Equiv.prodCongr_symm, Equiv.prodCongr_apply,
    Prod.map_fst, Prod.map_snd, Equiv.refl_symm, Equiv.refl_apply, splitLen_symm_ofFn]

/-! ### The OT inputs and outputs -/

/-- Alice's OT input length is `2`, `otFunctionality.inA.eval n = 2` (`otFunctionality_inA`). -/
theorem inA_eval (n : ℕ) : otFunctionality.inA.eval n = 2 := by
  rw [otFunctionality_inA, PolyExpr.eval_const]

/-- Bob's OT input length is `1`, `otFunctionality.inB.eval n = 1` (`otFunctionality_inB`). -/
theorem inB_eval (n : ℕ) : otFunctionality.inB.eval n = 1 := by
  rw [otFunctionality_inB, PolyExpr.eval_const]

/-- Alice's OT input read as two bits: `inA2 a j = a (cast j)`. -/
def inA2 {n : ℕ} (a : Fin (otFunctionality.inA.eval n) → Bool) : Fin 2 → Bool :=
  fun j => a (Fin.cast (inA_eval n).symm j)

/-- The defining equation of `inA2`: `inA2 a j = a (Fin.cast (inA_eval n).symm j)`. -/
theorem inA2_apply {n : ℕ} (a : Fin (otFunctionality.inA.eval n) → Bool) (j : Fin 2) :
    inA2 a j = a (Fin.cast (inA_eval n).symm j) := rfl

/-- Reading the input as two bits keeps its string: `ofFn (inA2 a) = ofFn a`. -/
theorem ofFn_inA2 {n : ℕ} (a : Fin (otFunctionality.inA.eval n) → Bool) :
    List.ofFn (inA2 a) = List.ofFn a :=
  ((List.ofFn_congr (inA_eval n) a).trans rfl).symm

/-- Bob's OT input read as one bit: `inB1 b j = b (cast j)`. -/
def inB1 {n : ℕ} (b : Fin (otFunctionality.inB.eval n) → Bool) : Fin 1 → Bool :=
  fun j => b (Fin.cast (inB_eval n).symm j)

/-- The defining equation of `inB1`: `inB1 b j = b (Fin.cast (inB_eval n).symm j)`. -/
theorem inB1_apply {n : ℕ} (b : Fin (otFunctionality.inB.eval n) → Bool) (j : Fin 1) :
    inB1 b j = b (Fin.cast (inB_eval n).symm j) := rfl

/-- Reading the input as one bit keeps its string: `ofFn (inB1 b) = ofFn b`. -/
theorem ofFn_inB1 {n : ℕ} (b : Fin (otFunctionality.inB.eval n) → Bool) :
    List.ofFn (inB1 b) = List.ofFn b :=
  ((List.ofFn_congr (inB_eval n) b).trans rfl).symm

/-- Bob's choice string is the one-bit list `[inB1 b 0]`: `List.ofFn b = [inB1 b 0]`. -/
theorem ofFn_eq_inB1 {n : ℕ} (b : Fin (otFunctionality.inB.eval n) → Bool) :
    List.ofFn b = [inB1 b 0] := by
  rw [← ofFn_inB1, List.ofFn_succ, List.ofFn_zero]

/-- Alice's OT output is empty: `ofFn (f n a b).1 = []`. -/
theorem ofFn_f_fst (n : ℕ) (a : Fin (otFunctionality.inA.eval n) → Bool)
    (b : Fin (otFunctionality.inB.eval n) → Bool) :
    List.ofFn (otFunctionality.f n a b).1 = [] :=
  List.eq_nil_of_length_eq_zero
    (by rw [List.length_ofFn, otFunctionality_outA, PolyExpr.eval_const])

/-- Bob's OT output is the chosen bit: `ofFn (f n a b).2 = [a_b]` with
`a_b = inA2 a (if inB1 b 0 then 1 else 0)` (`otFunctionality_f_snd_apply`). -/
theorem ofFn_f_snd (n : ℕ) (a : Fin (otFunctionality.inA.eval n) → Bool)
    (b : Fin (otFunctionality.inB.eval n) → Bool) :
    List.ofFn (otFunctionality.f n a b).2 = [inA2 a (if inB1 b 0 then 1 else 0)] := by
  have h : otFunctionality.outB.eval n = 1 := by
    rw [otFunctionality_outB, PolyExpr.eval_const]
  rw [List.ofFn_congr h, List.ofFn_succ, List.ofFn_zero, otFunctionality_f_snd_apply]
  rfl

end TCSlib.Cryptography.SecureComputation.OT

## ===== TCSlib/Cryptography/SecureComputation/ObliviousTransfer/ViewA.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.ObliviousTransfer.Simulators

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Oblivious transfer: Alice's side of Proposition 161.5

Alice's real view of Protocol 160.4 differs from `S_A`'s only in Bob's message: the real pair holds
`y_b = f_i(x) = eval ⟨i, w⟩` for a sampled `w` and a raw sample `y_{1−b}`, the simulated pair two
raw samples. For every generated index `i`, `eval ⟨i, w⟩` is within `2δ(n)` of a raw sample when
the sampler is within `δ(n)` of uniform (`perm_i` is a bijection), so any distinguisher's
advantage is at most `2δ(n)` [PS10, Proposition 161.5, proof].

## Main results

* `OT.statClose_prod_of_forall`: closeness for every value of a shared first coordinate gives
  closeness of the joint samplers.
* `OT.statClose_eval_sample`: `eval ⟨i, Sample(i; s)⟩` is `2δ(n)`-close to `Sample(i; s)`.
* `OT.realA_realCoins`, `OT.idealA_simACoins`: Alice's real and ideal samplers on typed coins.
* `OT.distAdv_realA_idealA_le`: the bound `2δ(n)` on Alice's side.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2.4, Proposition 161.5 (book pp. 161–162).
-/

namespace TCSlib.Cryptography.SecureComputation.OT

open Complexity Turing TCSlib.Cryptography

variable (T : TrapdoorCollection) (H : List Bool → List Bool)

/-- **Closeness with a shared first coordinate**: if `X r` is `c`-close to `Y r` for every `r`
(and `0 ≤ c`), then `(r, X r s)` is `c`-close to `(r, Y r t)` over uniform `(r, s)` and `(r, t)`
(`uprob_prod`, `abs_uexp_sub_le`). -/
theorem statClose_prod_of_forall {ρ σ τ γ : Type*} [Fintype ρ] [Fintype σ] [Fintype τ]
    {X : ρ → σ → γ} {Y : ρ → τ → γ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ r, StatClose (X r) (Y r) c) :
    StatClose (fun z : ρ × σ => (z.1, X z.1 z.2)) (fun z : ρ × τ => (z.1, Y z.1 z.2)) c := by
  refine (statClose_iff _ _ _).2 fun P => ?_
  rw [uprob_prod, uprob_prod]
  exact abs_uexp_sub_le hc fun r => (statClose_iff _ _ _).1 (h r) fun g => P (r, g)

/-- **The evaluated sample is close to a raw sample** [PS10, Proposition 161.5, proof]: at every
generated index `i = index n r`, `eval ⟨i, Sample(i; s)⟩` is `2δ(n)`-close to `Sample(i; s)` when
the sampler is within `δ` of uniform.

**Proof sketch.** Decoding the sample is `δ`-close to the uniform element (`SampleClose`). Mapping
by `x ↦ encD (perm x)` gives `eval ⟨i, Sample⟩` (`evalSampled`, `f_perm`) against
`encD (perm x)`, which is `0`-close to `encD x` (`perm` is a bijection, `comp_equiv_left`).
Mapping by `encD` gives `Sample` (canonical decoding) against `encD x`. Chain the three. -/
theorem statClose_eval_sample {δ : ℕ → ℝ} (hδ : T.SampleClose δ) (n : ℕ) (r : T.gen.Coins n) :
    StatClose (fun s : T.sample.Coins n =>
        T.eval (pairEncode (T.index n r) (T.sample.runAt n (T.index n r) s)))
      (fun s => T.sample.runAt n (T.index n r) s) (2 * δ n) := by
  have h₁ := (Collection.sampleClose_iff _ _).1 hδ n r
  have hA : StatClose (fun s : T.sample.Coins n => T.encD (T.index n r) (T.perm (T.index n r)
      ((T.decD (T.index n r) (T.sample.runAt n (T.index n r) s)).getD default)))
      (fun x => T.encD (T.index n r) (T.perm (T.index n r) x)) (δ n) :=
    h₁.map fun o => T.encD (T.index n r) (T.perm (T.index n r) (o.getD default))
  have hC : StatClose (fun s : T.sample.Coins n => T.encD (T.index n r)
      ((T.decD (T.index n r) (T.sample.runAt n (T.index n r) s)).getD default))
      (fun x => T.encD (T.index n r) x) (δ n) :=
    h₁.map fun o => T.encD (T.index n r) (o.getD default)
  have eA : (fun s : T.sample.Coins n => T.encD (T.index n r) (T.perm (T.index n r)
      ((T.decD (T.index n r) (T.sample.runAt n (T.index n r) s)).getD default))) =
      fun s => T.eval (pairEncode (T.index n r) (T.sample.runAt n (T.index n r) s)) := by
    funext s
    obtain ⟨x, hx, hev⟩ := (Collection.evalSampled_iff _).1 T.toCollection.evalSampled n r s
    rw [hx, Option.getD_some, hev, T.f_perm]
  have eC : (fun s : T.sample.Coins n => T.encD (T.index n r)
      ((T.decD (T.index n r) (T.sample.runAt n (T.index n r) s)).getD default)) =
      fun s => T.sample.runAt n (T.index n r) s := by
    funext s
    obtain ⟨x, hx, -⟩ := (Collection.evalSampled_iff _).1 T.toCollection.evalSampled n r s
    rw [hx, Option.getD_some, ((Collection.decD_eq_some_iff _).1 hx).symm]
  rw [eA] at hA
  rw [eC] at hC
  have hB : StatClose (fun x => T.encD (T.index n r) (T.perm (T.index n r) x))
      (fun x => T.encD (T.index n r) x) 0 :=
    (StatClose.refl fun x => T.encD (T.index n r) x).comp_equiv_left (T.perm (T.index n r))
  exact ((hA.trans hB).trans hC.symm).mono (by linarith)

/-- **Alice's real sampler on typed coins**: on `(r, s₁, s₂)` (`realCoins`), it is
`⟨⟨⟨1^n, a⟩, ⟨r, [y, []]⟩⟩, [a_b]⟩` with `y = ⟨eval ⟨i, w₁⟩, w₂⟩` (`⟨w₂, eval ⟨i, w₁⟩⟩` if `b`),
`i = index n r` and `w_j = Sample(i; s_j)`. -/
theorem realA_realCoins {π : Protocol} (hπ : IsOT T H π)
    (hout : ∀ x (a : Fin 2 → Bool) (b : Fin 1 → Bool) (r : π.ExecCoins π.P x),
      π.outV π.P x (List.ofFn a) (List.ofFn b) r = [a (if b 0 then 1 else 0)])
    (n : ℕ) (a : Fin (otFunctionality.inA.eval n) → Bool)
    (b : Fin (otFunctionality.inB.eval n) → Bool)
    (p : T.gen.Coins n × (T.sample.Coins n × T.sample.Coins n)) :
    otFunctionality.realA π n a b ((realCoins T H hπ n).symm p) =
      pairEncode (pairEncode (pairEncode (List.replicate n true) (List.ofFn a))
        (pairEncode (List.ofFn p.1)
          (pairEncode
            (if inB1 b 0 then
              pairEncode (T.sample.runAt n (T.index n p.1) p.2.2)
                (T.eval (pairEncode (T.index n p.1) (T.sample.runAt n (T.index n p.1) p.2.1)))
            else
              pairEncode
                (T.eval (pairEncode (T.index n p.1) (T.sample.runAt n (T.index n p.1) p.2.1)))
                (T.sample.runAt n (T.index n p.1) p.2.2))
            (pairEncode [] []))))
        [inA2 a (if inB1 b 0 then 1 else 0)] := by
  have hlen : (List.ofFn p.2.1).length = T.sample.coins.eval n := length_ofFn_coins _ n _
  rw [Functionality.realA_eq, Protocol.viewP_eq, View.encode_mk, transcriptWith_isOT T H hπ,
    ← ofFn_inA2 a, ← ofFn_inB1 b, hout, ofFn_inA2, ofFn_inB1, realCoins_symm_fst_ofFn,
    realCoins_symm_snd_ofFn, receiverNext_single, List.length_replicate, List.take_left' hlen,
    List.drop_left' hlen, ofFn_eq_inB1, List.headD_cons, ← NUPPT.runAt_eq, ← NUPPT.runAt_eq,
    ← NUPPT.runAt_eq, ← Collection.index_eq, Strategy.encodeMsgs_cons, Strategy.encodeMsgs_cons,
    Strategy.encodeMsgs_nil]

/-- **Alice's ideal sampler on typed coins**: on `(r, s₁, s₂)` (`simACoins`), it is
`⟨⟨⟨1^n, a⟩, ⟨r, [⟨w₁, w₂⟩, []]⟩⟩, [a_b]⟩` with `w_j = Sample(index n r; s_j)`. -/
theorem idealA_simACoins {S : NUPPT} (hS : IsSimA T S) (n : ℕ)
    (a : Fin (otFunctionality.inA.eval n) → Bool) (b : Fin (otFunctionality.inB.eval n) → Bool)
    (p : T.gen.Coins n × (T.sample.Coins n × T.sample.Coins n)) :
    otFunctionality.idealA S n a b ((simACoins T hS n).symm p) =
      pairEncode (pairEncode (pairEncode (List.replicate n true) (List.ofFn a))
        (pairEncode (List.ofFn p.1)
          (pairEncode (pairEncode (T.sample.runAt n (T.index n p.1) p.2.1)
              (T.sample.runAt n (T.index n p.1) p.2.2))
            (pairEncode [] []))))
        [inA2 a (if inB1 b 0 then 1 else 0)] := by
  rw [Functionality.idealA_eq, ((isSimA_iff T S).1 hS).2, simACoins_symm_ofFn, simAView_layout,
    pairFstD_pairEncode, ofFn_f_snd]

/-- **Alice's side of Proposition 161.5** [PS10]: for a protocol of the shape of Protocol 160.4
(with Bob's output `[a_b]`, `hout`), a machine of `S_A`'s shape and a sampler within `δ` of
uniform, every distinguisher's advantage between Alice's real and ideal samplers is at most
`2δ(n)`: `distAdv (realA π n a b) (idealA S n a b) (D.distinguisherL n) ≤ 2 * δ n`.

**Proof sketch.** Relabel both coin spaces as `Coins_Gen × (Coins_Sample × Coins_Sample)`
(`acceptProb_comp_equiv`). The samplers are then `W r (y_real)` and `W r (y_sim)` for one map
`W` (`realA_realCoins`, `idealA_simACoins`). For each `r`, `y_real` is `2δ(n)`-close to `y_sim`:
`StatClose.prod` of `statClose_eval_sample` with the identical raw sample (after swapping the two
sample blocks when `b`). So the joint samplers are `2δ(n)`-close (`statClose_prod_of_forall`,
`StatClose.map`), and `distAdv_le_of_statClose` concludes. -/
theorem distAdv_realA_idealA_le {π : Protocol} (hπ : IsOT T H π)
    (hout : ∀ x (a : Fin 2 → Bool) (b : Fin 1 → Bool) (r : π.ExecCoins π.P x),
      π.outV π.P x (List.ofFn a) (List.ofFn b) r = [a (if b 0 then 1 else 0)])
    {S : NUPPT} (hS : IsSimA T S) {δ : ℕ → ℝ} (hδ : T.SampleClose δ) (D : NUPPT) (n : ℕ)
    (a : Fin (otFunctionality.inA.eval n) → Bool) (b : Fin (otFunctionality.inB.eval n) → Bool) :
    distAdv (otFunctionality.realA π n a b) (otFunctionality.idealA S n a b)
      (D.distinguisherL n) ≤ 2 * δ n := by
  have h0 : 0 ≤ 2 * δ n := by
    have := ((Collection.sampleClose_iff _ _).1 hδ n fun _ => false).nonneg
    linarith
  rw [distAdv_def, ← acceptProb_comp_equiv (realCoins T H hπ n).symm,
    ← acceptProb_comp_equiv (simACoins T hS n).symm, ← distAdv_def]
  simp only [realA_realCoins T H hπ hout, idealA_simACoins T hS]
  refine distAdv_le_of_statClose _ _ ?_ _
  -- the per-index closeness of Bob's message
  have hY : ∀ r : T.gen.Coins n, StatClose
      (fun s : T.sample.Coins n × T.sample.Coins n =>
        if inB1 b 0 then
          pairEncode (T.sample.runAt n (T.index n r) s.2)
            (T.eval (pairEncode (T.index n r) (T.sample.runAt n (T.index n r) s.1)))
        else
          pairEncode (T.eval (pairEncode (T.index n r) (T.sample.runAt n (T.index n r) s.1)))
            (T.sample.runAt n (T.index n r) s.2))
      (fun s : T.sample.Coins n × T.sample.Coins n =>
        pairEncode (T.sample.runAt n (T.index n r) s.1) (T.sample.runAt n (T.index n r) s.2))
      (2 * δ n) := by
    intro r
    have he := statClose_eval_sample T hδ n r
    have hs := StatClose.refl fun s : T.sample.Coins n => T.sample.runAt n (T.index n r) s
    cases hb : inB1 b 0
    · have h := (he.prod hs).map fun q : List Bool × List Bool => pairEncode q.1 q.2
      simpa only [Bool.false_eq_true, if_false, add_zero] using h
    · have h := ((hs.prod he).map fun q : List Bool × List Bool =>
        pairEncode q.1 q.2).comp_equiv_left (Equiv.prodComm (T.sample.Coins n) (T.sample.Coins n))
      simpa only [if_true, zero_add, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap] using h
  exact (statClose_prod_of_forall h0 hY).map fun q : T.gen.Coins n × List Bool =>
    pairEncode (pairEncode (pairEncode (List.replicate n true) (List.ofFn a))
      (pairEncode (List.ofFn q.1) (pairEncode q.2 (pairEncode [] []))))
      [inA2 a (if inB1 b 0 then 1 else 0)]

end TCSlib.Cryptography.SecureComputation.OT

## ===== TCSlib/Cryptography/SecureComputation/ObliviousTransfer/Predictor.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.ObliviousTransfer.Simulators
import TCSlib.Cryptography.Encryption.PublicKey.Trapdoor

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Oblivious transfer: the view-building distinguisher behind Bob's side

On Bob's side of [PS10, Proposition 161.5] a distinguisher `D` of Bob's real and simulated views
becomes a predictor of the enhanced hard-core bit `h(f_i⁻¹(y_{1−b}))` from `⟨i, s'⟩`, `s'` the
sampler coins of `y_{1−b}`. The predictor is the machine `tdpPredictor D' flip` of Algorithm
104.3's proof, run on the distinguisher `D'` built here: on `⟨i, ⟨s', [β]⟩⟩` with its own coins
`s₁ ++ ρ`, `D'` assembles Bob's view with tape `s₁ ++ s'`, index `i`, the selected mask
`z_b = H ⟨i, Sample(i; s₁)⟩ ⊕ a_b` and the unselected mask `z_{1−b} = β ⊕ a_{1−b}` (`OT.bobView`),
and runs `D` on it with the coins `ρ`. The choice and sender bits `(b, a₀, a₁)` are fixed in the
machine.

## Main definitions

* `OT.bobView`: Bob's view (paired with Alice's empty output) with a given unselected mask bit.
* `OT.viewRaw`, `OT.viewDistRaw`: the raw functions of the view and of `D'`.
* `OT.viewDist`: the machine `D'`; `OT.viewDistCoins`: its coins as `Coins_Sample × Coins_D`.

## Main results

* `OT.polyTimeComputable_bobView`, `OT.polyTimeComputable_viewDistRaw`: they are
  polynomial-time.
* `OT.distinguisherL_viewDist`: `D'` accepts `⟨i, ⟨s', [β]⟩⟩` on `(s₁, ρ)` iff `D` accepts the
  view `bobView … β` on `ρ`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2.4, Proposition 161.5, and Theorem 104.4 (the predictor), book pp. 104, 161–162.
-/

namespace TCSlib.Cryptography.SecureComputation.OT

open Complexity Turing TCSlib.Cryptography

variable (T : TrapdoorCollection) (H : List Bool → List Bool)

/-- **Bob's view with the unselected mask bit `β`** [PS10, Proposition 161.5], paired with
Alice's empty output: `⟨⟨⟨u, [b]⟩, ⟨s, [i, Z, []]⟩⟩, []⟩` with
`Z = ⟨[β ⊕ a₀], H ⟨i, w⟩ ⊕ [a₁]⟩` if `b`, else `⟨H ⟨i, w⟩ ⊕ [a₀], [β ⊕ a₁]⟩`. -/
def bobView (u : List Bool) (b a₀ a₁ : Bool) (i s w : List Bool) (β : Bool) : List Bool :=
  pairEncode (pairEncode (pairEncode u [b]) (pairEncode s (pairEncode i (pairEncode
    (if b then pairEncode [xor β a₀] (List.zipWith xor (H (pairEncode i w)) [a₁])
      else pairEncode (List.zipWith xor (H (pairEncode i w)) [a₀]) [xor β a₁])
    (pairEncode [] []))))) []

/-- The defining equation of `bobView`: `bobView H u b a₀ a₁ i s w β =
⟨⟨⟨u, [b]⟩, ⟨s, [i, Z, []]⟩⟩, []⟩` with `Z` ordered by `b`. -/
theorem bobView_eq (u : List Bool) (b a₀ a₁ : Bool) (i s w : List Bool) (β : Bool) :
    bobView H u b a₀ a₁ i s w β =
      pairEncode (pairEncode (pairEncode u [b]) (pairEncode s (pairEncode i (pairEncode
        (if b then pairEncode [xor β a₀] (List.zipWith xor (H (pairEncode i w)) [a₁])
          else pairEncode (List.zipWith xor (H (pairEncode i w)) [a₀]) [xor β a₁])
        (pairEncode [] []))))) [] := rfl

/-- **Bob's view is polynomial-time** in its string arguments, for polynomial-time `H`
(pairing, one XOR of bits `BinArith.polyTimeComputable_xor`, `polyTimeComputable_pairXor`, a
branch on the fixed bit `b`): `PolyTimeComputable (fun z =>
bobView H (U z) b a₀ a₁ (I z) (S z) (W z) ((B z).headD false))`. -/
theorem polyTimeComputable_bobView {H : List Bool → List Bool} (hH : PolyTimeComputable H)
    (b a₀ a₁ : Bool) {U I S W B : List Bool → List Bool} (hU : PolyTimeComputable U)
    (hI : PolyTimeComputable I) (hS : PolyTimeComputable S) (hW : PolyTimeComputable W)
    (hB : PolyTimeComputable B) :
    PolyTimeComputable fun z => bobView H (U z) b a₀ a₁ (I z) (S z) (W z) ((B z).headD false) := by
  have hβ := polyTimeComputable_headD.comp' hB
  have hx : ∀ a : Bool, PolyTimeComputable fun z => [xor ((B z).headD false) a] := fun a =>
    BinArith.polyTimeComputable_xor hβ (polyTimeComputable_const [a])
  have hm : ∀ a : Bool, PolyTimeComputable fun z =>
      List.zipWith xor (H (pairEncode (I z) (W z))) [a] := fun a =>
    (polyTimeComputable_pairXor.comp' ((hH.comp' (hI.pairEncode hW)).pairEncode
      (polyTimeComputable_const [a]))).congr fun z => by
        rw [pairFstD_pairEncode, pairSndD_pairEncode]
  have hZ := polyTimeComputable_ite (p := fun _ => b) (polyTimeComputable_const [b])
    ((hx a₀).pairEncode (hm a₁)) ((hm a₀).pairEncode (hx a₁))
  have h := ((hU.pairEncode (polyTimeComputable_const [b])).pairEncode (hS.pairEncode
    (hI.pairEncode (hZ.pairEncode (polyTimeComputable_const (pairEncode [] [])))))).pairEncode
    (polyTimeComputable_const [])
  exact h.congr fun z => (bobView_eq H _ _ _ _ _ _ _ _).symm

/-- The view built by `D'` on the raw layout `z = layout u ⟨i, ⟨s', [β]⟩⟩ α (s₁ ++ ρ)`:
`bobView u b a₀ a₁ i (s₁ ++ s') (Sample(u, i; s₁)) β`, with `s₁` the first `coins_Sample(|u|)`
coins. -/
def viewRaw (b a₀ a₁ : Bool) (z : List Bool) : List Bool :=
  bobView H (NUPPT.inParam z) b a₀ a₁ (pairFstD (NUPPT.inArg z))
    ((NUPPT.inCoins z).take (T.sample.coins.eval (NUPPT.inParam z).length) ++
      pairFstD (pairSndD (NUPPT.inArg z)))
    (T.sample.output (NUPPT.layout (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)) []
      ((NUPPT.inCoins z).take (T.sample.coins.eval (NUPPT.inParam z).length))))
    ((pairSndD (pairSndD (NUPPT.inArg z))).headD false)

/-- The defining equation of `viewRaw`: `viewRaw T H b a₀ a₁ z = bobView H u b a₀ a₁ i
(s₁ ++ s') (Sample(u, i; s₁)) β` read off the layout `z`. -/
theorem viewRaw_eq (b a₀ a₁ : Bool) (z : List Bool) :
    viewRaw T H b a₀ a₁ z =
      bobView H (NUPPT.inParam z) b a₀ a₁ (pairFstD (NUPPT.inArg z))
        ((NUPPT.inCoins z).take (T.sample.coins.eval (NUPPT.inParam z).length) ++
          pairFstD (pairSndD (NUPPT.inArg z)))
        (T.sample.output (NUPPT.layout (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)) []
          ((NUPPT.inCoins z).take (T.sample.coins.eval (NUPPT.inParam z).length))))
        ((pairSndD (pairSndD (NUPPT.inArg z))).headD false) := rfl

/-- The raw function of `D'`: `D` on the layout of `1^n`, the built view, the advice and the
coins after the first `coins_Sample(n)`: `viewDistRaw T H D b a₀ a₁ z = D.output (layout
(inParam z) (viewRaw T H b a₀ a₁ z) (inAdvice z) ((inCoins z).drop coins_Sample(n)))`. -/
def viewDistRaw (D : NUPPT) (b a₀ a₁ : Bool) (z : List Bool) : List Bool :=
  D.output (NUPPT.layout (NUPPT.inParam z) (viewRaw T H b a₀ a₁ z) (NUPPT.inAdvice z)
    ((NUPPT.inCoins z).drop (T.sample.coins.eval (NUPPT.inParam z).length)))

/-- The defining equation of `viewDistRaw`: `viewDistRaw T H D b a₀ a₁ z = D.output (layout
(inParam z) (viewRaw T H b a₀ a₁ z) (inAdvice z) ((inCoins z).drop coins_Sample(n)))`. -/
theorem viewDistRaw_eq (D : NUPPT) (b a₀ a₁ : Bool) (z : List Bool) :
    viewDistRaw T H D b a₀ a₁ z =
      D.output (NUPPT.layout (NUPPT.inParam z) (viewRaw T H b a₀ a₁ z) (NUPPT.inAdvice z)
        ((NUPPT.inCoins z).drop (T.sample.coins.eval (NUPPT.inParam z).length))) := rfl

/-- **The raw function of `D'` is polynomial-time** (`polyTimeComputable_bobView`, the sampler's
and `D`'s output functions, `polyTimeComputable_pairTakePoly`, `polyTimeComputable_pairDropPoly`,
`PolyTimeComputable.append`): `PolyTimeComputable (viewDistRaw T H D b a₀ a₁)`.

**Proof sketch.** Build the projections, the first coin block and the remaining coins, the sampled
element on the first block, the tape `s₁ ++ s'` and the built view (`polyTimeComputable_bobView`),
then `D`'s output on the layout; match the definition by the pairing readers. -/
theorem polyTimeComputable_viewDistRaw {H : List Bool → List Bool} (hH : PolyTimeComputable H)
    (D : NUPPT) (b a₀ a₁ : Bool) : PolyTimeComputable (viewDistRaw T H D b a₀ a₁) := by
  have hU := NUPPT.polyTimeComputable_inParam
  have hi := polyTimeComputable_pairFstD.comp' NUPPT.polyTimeComputable_inArg
  have htake := (polyTimeComputable_pairTakePoly T.sample.coins).comp'
    (hU.pairEncode NUPPT.polyTimeComputable_inCoins)
  have hdrop := (polyTimeComputable_pairDropPoly T.sample.coins).comp'
    (hU.pairEncode NUPPT.polyTimeComputable_inCoins)
  have hs := htake.append (polyTimeComputable_pairFstD.comp'
    (polyTimeComputable_pairSndD.comp' NUPPT.polyTimeComputable_inArg))
  have hw := T.sample.polyTimeComputable_output.comp' (NUPPT.polyTimeComputable_layout hU hi
    (polyTimeComputable_const []) htake)
  have hβ := polyTimeComputable_pairSndD.comp'
    (polyTimeComputable_pairSndD.comp' NUPPT.polyTimeComputable_inArg)
  have hv := polyTimeComputable_bobView hH b a₀ a₁ hU hi hs hw hβ
  have h := D.polyTimeComputable_output.comp' (NUPPT.polyTimeComputable_layout hU hv
    NUPPT.polyTimeComputable_inAdvice hdrop)
  refine h.congr fun z => ?_
  simp only [viewDistRaw_eq, viewRaw_eq, pairFstD_pairEncode, pairSndD_pairEncode]

/-- **The view-building distinguisher `D'`** for the fixed bits `(b, a₀, a₁)`: `D`'s advice and
coins `coins_Sample + coins_D`: `viewDist T hH D b a₀ a₁ = NUPPT.ofPolyTime
(polyTimeComputable_viewDistRaw T hH D b a₀ a₁) (.add T.sample.coins D.coins) D.adv D.advice
D.advice_length`. -/
noncomputable def viewDist {H : List Bool → List Bool} (hH : PolyTimeComputable H) (D : NUPPT)
    (b a₀ a₁ : Bool) : NUPPT :=
  NUPPT.ofPolyTime (polyTimeComputable_viewDistRaw T hH D b a₀ a₁) (.add T.sample.coins D.coins)
    D.adv D.advice D.advice_length

/-- The coin polynomial of `D'` is `coins_Sample + coins_D`:
`(viewDist T hH D b a₀ a₁).coins = .add T.sample.coins D.coins`. -/
theorem viewDist_coins {H : List Bool → List Bool} (hH : PolyTimeComputable H) (D : NUPPT)
    (b a₀ a₁ : Bool) : (viewDist T hH D b a₀ a₁).coins = .add T.sample.coins D.coins :=
  NUPPT.coins_ofPolyTime _ _ _ _ _

/-- **`D'`'s coins** as a sampler block and `D`'s coins:
`(viewDist T hH D b a₀ a₁).Coins n ≃ T.sample.Coins n × D.Coins n` (`splitLen`). -/
noncomputable def viewDistCoins {H : List Bool → List Bool} (hH : PolyTimeComputable H) (D : NUPPT)
    (b a₀ a₁ : Bool) (n : ℕ) : (viewDist T hH D b a₀ a₁).Coins n ≃ T.sample.Coins n × D.Coins n :=
  splitLen (by rw [NUPPT.coinLen_eq, viewDist_coins, PolyExpr.eval_add, NUPPT.coinLen_eq,
    NUPPT.coinLen_eq])

/-- The tape of `D'` from blocks: `ofFn ((viewDistCoins …).symm (s₁, ρ)) = ofFn s₁ ++ ofFn ρ`. -/
theorem viewDistCoins_symm_ofFn {H : List Bool → List Bool} (hH : PolyTimeComputable H)
    (D : NUPPT) (b a₀ a₁ : Bool) (n : ℕ) (p : T.sample.Coins n × D.Coins n) :
    List.ofFn ((viewDistCoins T hH D b a₀ a₁ n).symm p) = List.ofFn p.1 ++ List.ofFn p.2 :=
  splitLen_symm_ofFn _ p

/-- **`D'` runs `D` on the built view**: on `⟨i, ⟨s', [β]⟩⟩` with coins `s₁ ++ ρ`,
`D'(1^n, ⟨i, ⟨s', [β]⟩⟩; s₁ ++ ρ) = D(1^n, bobView (1^n) b a₀ a₁ i (s₁ ++ s') w β; ρ)` with
`w = Sample(1^n, i; s₁)`. -/
theorem runAtL_viewDist {H : List Bool → List Bool} (hH : PolyTimeComputable H) (D : NUPPT)
    (b a₀ a₁ : Bool) (n : ℕ) (i s' : List Bool) (β : Bool) (s₁ : T.sample.Coins n)
    (ρ : List Bool) :
    (viewDist T hH D b a₀ a₁).runAtL n (pairEncode i (pairEncode s' [β])) (List.ofFn s₁ ++ ρ) =
      D.runAtL n (bobView H (List.replicate n true) b a₀ a₁ i (List.ofFn s₁ ++ s')
        (T.sample.runAt n i s₁) β) ρ := by
  have hl : (List.ofFn s₁).length = T.sample.coins.eval (List.replicate n true).length := by
    rw [length_ofFn_coins, List.length_replicate]
  unfold viewDist
  rw [NUPPT.runAtL_ofPolyTime, NUPPT.advInput_eq, ← NUPPT.layout_eq, viewDistRaw_eq, viewRaw_eq,
    NUPPT.inParam_layout, NUPPT.inArg_layout, NUPPT.inAdvice_layout, NUPPT.inCoins_layout,
    List.take_left' hl, List.drop_left' hl, pairFstD_pairEncode, pairSndD_pairEncode,
    pairFstD_pairEncode, pairSndD_pairEncode, List.headD_cons, NUPPT.runAtL_eq_output_layout,
    NUPPT.runAt_eq, NUPPT.runAtL_eq_output_layout, NUPPT.Uniform.advice_eq T.sample_uniform]

/-- **`D'` accepts iff `D` accepts the built view**: `D'.distinguisherL n ⟨i, ⟨s', [β]⟩⟩ (s₁, ρ) =
D.distinguisherL n (bobView (1^n) b a₀ a₁ i (s₁ ++ s') (Sample(1^n, i; s₁)) β) ρ`. -/
theorem distinguisherL_viewDist {H : List Bool → List Bool} (hH : PolyTimeComputable H)
    (D : NUPPT) (b a₀ a₁ : Bool) (n : ℕ) (i s' : List Bool) (β : Bool)
    (p : T.sample.Coins n × D.Coins n) :
    (viewDist T hH D b a₀ a₁).distinguisherL n (pairEncode i (pairEncode s' [β]))
        ((viewDistCoins T hH D b a₀ a₁ n).symm p) =
      D.distinguisherL n (bobView H (List.replicate n true) b a₀ a₁ i (List.ofFn p.1 ++ s')
        (T.sample.runAt n i p.1) β) p.2 := by
  rw [NUPPT.distinguisherL_eq, NUPPT.distinguisherL_eq, NUPPT.runAt_eq, NUPPT.runAt_eq,
    viewDistCoins_symm_ofFn, runAtL_viewDist]

end TCSlib.Cryptography.SecureComputation.OT

## ===== TCSlib/Cryptography/SecureComputation/ObliviousTransfer/ViewB.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.ObliviousTransfer.ViewA
import TCSlib.Cryptography.SecureComputation.ObliviousTransfer.Predictor

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Oblivious transfer: Bob's side of Proposition 161.5

Bob's real view of Protocol 160.4 differs from `S_B`'s only in the unselected mask:
`z_{1−b} = h(f_i⁻¹(y_{1−b})) ⊕ a_{1−b}` in the real view, a fresh coin in the simulated one
[PS10, Proposition 161.5, the proof left as an exercise]. Both are `OT.bobView` with the
unselected mask `β ⊕ a_{1−b}`, where `β = h(f_i⁻¹(y_{1−b}))` (real) or `β` is uniform
(simulated). Writing `P(β)` for `D`'s acceptance probability, the real one is `E_r P(B)`, the
simulated one `E_r (P(B) + P(¬B))/2`, so the advantage is `|E_r P(B) − E_r P(¬B)| / 2`. The
signed predictor (`uprob_signedPredictor_false`, `_true`) run on the view-building distinguisher
`D'` (`OT.viewDist`) predicts `B` from `⟨i, s'⟩` with probability `1/2 ± (P(B) − P(¬B))/2`, so the
enhanced hard-core hypothesis bounds the advantage by `|ε_false(n)| + |ε_true(n)|` for the fixed
bits `(b, a₀, a₁)`. The eight choices of these bits give sixteen machines; the sum of their
bounds is negligible and uniform over the inputs.

## Main definitions

* `OT.hcBit`: the enhanced hard-core bit `h_i(f_i⁻¹(Sample(i; s)))` of a sampled element.
* `OT.accB`: `D`'s acceptance probability of Bob's view with a given unselected bit.

## Main results

* `OT.uprob_signedPredictor_false`, `OT.uprob_signedPredictor_true`: the signed-predictor
  identity of Algorithm 104.3's proof for a uniform challenge `x` and a bit `B x`.
* `OT.uprob_xor_shear`, `OT.negligible_finset_sum`: a uniform bit masked by a fixed bit, and
  finite sums of negligible functions.
* `OT.mask_eval`, `OT.mask_raw`: Alice's two masks on Bob's real pair.
* `OT.realB_realCoins`, `OT.idealB_simBCoins`: Bob's real and ideal samplers on typed coins;
  `OT.acceptProb_realB`, `OT.acceptProb_idealB`: their acceptance probabilities through `accB`.
* `OT.acceptProb_viewDist`, `OT.uprob_predictor_false`, `OT.uprob_predictor_true`: the
  prediction experiments of the two predictors.
* `OT.distAdv_realB_idealB_le`, `OT.exists_negligible_bob`: the bound on Bob's side.
* `OT.simulators_of_isOT`: Proposition 161.5 with its simulators, for every protocol and pair of
  machines of the shapes of Protocol 160.4 and of `S_A`, `S_B`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2.4, Proposition 161.5, and Theorem 104.4 (the predictor), book pp. 104, 161–162.
* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2*, Cambridge University Press,
  2004, §7.3.2 (the enhanced predicate in the OT argument).
-/

namespace TCSlib.Cryptography.SecureComputation.OT

open Complexity Turing TCSlib.Cryptography

variable (T : TrapdoorCollection) (H : List Bool → List Bool)

/-! ### The signed predictor -/

/-- **The signed predictor, unflipped** (the identity behind [PS10, Theorem 104.4, proof], for a
uniform challenge `x` and a bit `B x`): drawing `c` and coins `ρ`, outputting `c` if `D(x, c; ρ)`
accepts and `¬c` otherwise, predicts `B x` with probability
`1/2 + (Pr[D(x, B x) = 1] − Pr[D(x, ¬B x) = 1]) / 2`.

**Proof sketch.** Substitute `c = d ⊕ B x` (a bijection of `Bool × (α × ρ)`) and split on `d`
(`uprob_bool_prod`): for `d = 0` the prediction is right iff `D(x, B x)` accepts, for `d = 1` iff
`D(x, ¬B x)` rejects (`uprob_not`). -/
theorem uprob_signedPredictor_false {α ρ : Type*} [Fintype α] [Fintype ρ] [Nonempty α]
    [Nonempty ρ] (B : α → Bool) (D : α × Bool → ρ → Bool) :
    uprob (fun z : α × (Bool × ρ) =>
        xor (if D (z.1, z.2.1) z.2.2 then z.2.1 else !z.2.1) false = B z.1) =
      1 / 2 + (acceptProb (fun x => (x, B x)) D - acceptProb (fun x => (x, !B x)) D) / 2 := by
  let e : Bool × (α × ρ) ≃ α × (Bool × ρ) :=
    { toFun := fun v => (v.2.1, (xor v.1 (B v.2.1), v.2.2))
      invFun := fun z => (xor z.2.1 (B z.1), (z.1, z.2.2))
      left_inv := fun v => by simp
      right_inv := fun z => by simp }
  rw [← uprob_comp_equiv e, uprob_bool_prod, acceptProb_def, acceptProb_def,
    show ∀ a b : ℝ, 1 / 2 + (a - b) / 2 = (a + (1 - b)) / 2 by intro a b; ring, ← uprob_not]
  congr 2
  · congr 1
    funext w
    apply propext
    simp only [e, Equiv.coe_fn_mk, Bool.false_xor, Bool.xor_false]
    cases D (w.1, B w.1) w.2 <;> cases B w.1 <;> simp
  · congr 1
    funext w
    apply propext
    simp only [e, Equiv.coe_fn_mk, Bool.true_xor, Bool.xor_false]
    cases D (w.1, !B w.1) w.2 <;> cases B w.1 <;> simp

/-- **The signed predictor, flipped**: the same predictor negated predicts `B x` with probability
`1/2 − (Pr[D(x, B x) = 1] − Pr[D(x, ¬B x) = 1]) / 2`.

**Proof sketch.** As `uprob_signedPredictor_false`: substitute `c = d ⊕ B x` and split on `d`.
With the output negated, for `d = 0` the prediction is right iff `D(x, B x)` rejects
(`uprob_not`), and for `d = 1` iff `D(x, ¬B x)` accepts. -/
theorem uprob_signedPredictor_true {α ρ : Type*} [Fintype α] [Fintype ρ] [Nonempty α]
    [Nonempty ρ] (B : α → Bool) (D : α × Bool → ρ → Bool) :
    uprob (fun z : α × (Bool × ρ) =>
        xor (if D (z.1, z.2.1) z.2.2 then z.2.1 else !z.2.1) true = B z.1) =
      1 / 2 - (acceptProb (fun x => (x, B x)) D - acceptProb (fun x => (x, !B x)) D) / 2 := by
  let e : Bool × (α × ρ) ≃ α × (Bool × ρ) :=
    { toFun := fun v => (v.2.1, (xor v.1 (B v.2.1), v.2.2))
      invFun := fun z => (xor z.2.1 (B z.1), (z.1, z.2.2))
      left_inv := fun v => by simp
      right_inv := fun z => by simp }
  rw [← uprob_comp_equiv e, uprob_bool_prod, acceptProb_def, acceptProb_def,
    show ∀ a b : ℝ, 1 / 2 - (a - b) / 2 = ((1 - a) + b) / 2 by intro a b; ring, ← uprob_not]
  congr 2
  · congr 1
    funext w
    apply propext
    simp only [e, Equiv.coe_fn_mk, Bool.false_xor, Bool.xor_true]
    cases D (w.1, B w.1) w.2 <;> cases B w.1 <;> simp
  · congr 1
    funext w
    apply propext
    simp only [e, Equiv.coe_fn_mk, Bool.true_xor, Bool.xor_true]
    cases D (w.1, !B w.1) w.2 <;> cases B w.1 <;> simp

/-- **A uniform bit masked by a fixed bit, re-centred on `g x`**: over uniform `(β, x)`,
`Pr[Q (β ⊕ a) x] = (Pr[Q (g x) x] + Pr[Q (¬g x) x]) / 2` (the bijection `β ↦ β ⊕ a ⊕ g x`, then
`uprob_bool_prod`). -/
theorem uprob_xor_shear {X : Type*} [Fintype X] (g : X → Bool) (a : Bool) (Q : Bool → X → Prop) :
    uprob (fun w : Bool × X => Q (xor w.1 a) w.2) =
      (uprob (fun x => Q (g x) x) + uprob (fun x => Q (!g x) x)) / 2 := by
  let e : Bool × X ≃ Bool × X :=
    { toFun := fun w => (xor (xor w.1 (g w.2)) a, w.2)
      invFun := fun w => (xor (xor w.1 a) (g w.2), w.2)
      left_inv := fun w => by simp
      right_inv := fun w => by simp }
  rw [← uprob_comp_equiv e, uprob_bool_prod]
  congr 2 <;> congr 1 <;> funext x <;> simp only [e, Equiv.coe_fn_mk] <;> cases g x <;>
    cases a <;> rfl

/-- **A finite sum of negligible functions is negligible** (`Negligible.add` by induction on the
finite set): `(∀ i ∈ s, Negligible (f i)) → Negligible (fun n => ∑ i ∈ s, f i n)`. -/
theorem negligible_finset_sum {ι : Type*} (s : Finset ι) {f : ι → ℕ → ℝ}
    (h : ∀ i ∈ s, Negligible (f i)) : Negligible fun n => ∑ i ∈ s, f i n := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using negligible_zero
  | insert i s hi ih =>
    simp_rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-! ### The enhanced bit and the two masks -/

/-- **The enhanced hard-core bit of a sampled element** [Gol04, §7.3.2]: at the index
`i = index n r`, `hcBit T h n r s = h_i(perm_i⁻¹(dec_i(Sample(i; s))))`. -/
def hcBit (h : ∀ i, T.D i → Bool) (n : ℕ) (r : T.gen.Coins n) (s : T.sample.Coins n) : Bool :=
  h (T.index n r) ((T.perm (T.index n r)).symm
    ((T.decD (T.index n r) (T.sample.runAt n (T.index n r) s)).getD default))

/-- The defining equation of `hcBit`: `hcBit T h n r s =
h_i (perm_i⁻¹ ((dec_i (Sample(i; s))).getD default))` with `i = index n r`. -/
theorem hcBit_eq (h : ∀ i, T.D i → Bool) (n : ℕ) (r : T.gen.Coins n) (s : T.sample.Coins n) :
    hcBit T h n r s = h (T.index n r) ((T.perm (T.index n r)).symm
      ((T.decD (T.index n r) (T.sample.runAt n (T.index n r) s)).getD default)) := rfl

/-- **The inverter on the all-`true` tape** [PS10, Definition 56.1 (6)]:
`Inv(1^n, ⟨t, encD y⟩; 1^{inv(n)}) = encD (perm⁻¹ y)` (`TrapdoorCollection.inv_eq_encD`). -/
theorem inv_runAtL_ones (n : ℕ) (r : T.gen.Coins n) (y : T.D (T.index n r)) :
    T.inv.runAtL n (pairEncode (T.trap n r) (T.encD _ y))
        (List.replicate (T.inv.coins.eval n) true) =
      T.encD _ ((T.perm _).symm y) := by
  rw [← NUPPT.coinLen_eq, ← List.ofFn_const, ← NUPPT.runAt_eq]
  exact T.inv_eq_encD n r y fun _ => true

/-- **The selected mask** [PS10, Protocol 160.4]: on `y_b = eval ⟨i, w⟩` with `w = Sample(i; s)`,
Alice's mask is `H ⟨i, w⟩ ⊕ [c]` (the inverter returns `w`'s element, `H` is correct on it). -/
theorem mask_eval {h : ∀ i, T.D i → Bool}
    (henc : ∀ i (x : T.D i), H (pairEncode i (T.encD i x)) = [h i x]) (n : ℕ)
    (r : T.gen.Coins n) (s : T.sample.Coins n) (c : Bool) :
    mask T H n (T.index n r) (T.trap n r)
        (T.eval (pairEncode (T.index n r) (T.sample.runAt n (T.index n r) s))) c =
      List.zipWith xor (H (pairEncode (T.index n r) (T.sample.runAt n (T.index n r) s))) [c] := by
  obtain ⟨x, hx, hev⟩ := (Collection.evalSampled_iff _).1 T.toCollection.evalSampled n r s
  have hw : H (pairEncode (T.index n r) (T.sample.runAt n (T.index n r) s)) = [h _ x] :=
    T.toCollection.apply_of_decD (v := fun i x => [h i x]) henc hx
  rw [mask_eq, hev, T.f_perm, inv_runAtL_ones, Equiv.symm_apply_apply, henc, hw]

/-- **The unselected mask** [PS10, Protocol 160.4]: on the raw sample `w' = Sample(i; s)`,
Alice's mask is `[hcBit T h n r s ⊕ c]` (the inverter returns the encoding of
`perm⁻¹(dec w')`). -/
theorem mask_raw {h : ∀ i, T.D i → Bool}
    (henc : ∀ i (x : T.D i), H (pairEncode i (T.encD i x)) = [h i x]) (n : ℕ)
    (r : T.gen.Coins n) (s : T.sample.Coins n) (c : Bool) :
    mask T H n (T.index n r) (T.trap n r) (T.sample.runAt n (T.index n r) s) c =
      [xor (hcBit T h n r s) c] := by
  obtain ⟨x, hx, -⟩ := (Collection.evalSampled_iff _).1 T.toCollection.evalSampled n r s
  have hw : T.sample.runAt n (T.index n r) s = T.encD _ x :=
    (Collection.decD_eq_some_iff _).1 hx
  rw [mask_eq, hcBit_eq, hx, Option.getD_some, hw, inv_runAtL_ones, henc]
  rfl

/-! ### Bob's real and ideal samplers -/

/-- Alice's input string is the two-bit list `[a₀, a₁]`:
`List.ofFn (inA2 a) = [inA2 a 0, inA2 a 1]`. -/
theorem ofFn_inA2_eq {n : ℕ} (a : Fin (otFunctionality.inA.eval n) → Bool) :
    List.ofFn (inA2 a) = [inA2 a 0, inA2 a 1] := by
  rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
  rfl

/-- **Bob's real sampler on typed coins**: on `(r, s₁, s₂)` (`realCoins`) it is
`bobView (1^n) b a₀ a₁ i (s₁ ++ s₂) (Sample(i; s₁)) (hcBit T h n r s₂)` with `i = index n r`.

**Proof sketch.** Unfold the real sampler to the transcript (`transcriptWith_isOT`) on the
assembled tapes (`realCoins_symm_fst_ofFn`, `realCoins_symm_snd_ofFn`), with Alice's output `[]`
(`houtP`). Then cases on `b`: the selected mask is `mask_eval`, the unselected one `mask_raw`. -/
theorem realB_realCoins {h : ∀ i, T.D i → Bool}
    (henc : ∀ i (x : T.D i), H (pairEncode i (T.encD i x)) = [h i x]) {π : Protocol}
    (hπ : IsOT T H π)
    (houtP : ∀ x (a : Fin 2 → Bool) (b : Fin 1 → Bool) (r : π.ExecCoins π.P x),
      π.outP x (List.ofFn a) (List.ofFn b) r = [])
    (n : ℕ) (a : Fin (otFunctionality.inA.eval n) → Bool)
    (b : Fin (otFunctionality.inB.eval n) → Bool)
    (p : T.gen.Coins n × (T.sample.Coins n × T.sample.Coins n)) :
    otFunctionality.realB π n a b ((realCoins T H hπ n).symm p) =
      bobView H (List.replicate n true) (inB1 b 0) (inA2 a 0) (inA2 a 1) (T.index n p.1)
        (List.ofFn p.2.1 ++ List.ofFn p.2.2) (T.sample.runAt n (T.index n p.1) p.2.1)
        (hcBit T h n p.1 p.2.2) := by
  have hlen : (List.ofFn p.2.1).length = T.sample.coins.eval n := length_ofFn_coins _ n _
  rw [Functionality.realB_eq, Protocol.viewV_eq, View.encode_mk, transcriptWith_isOT T H hπ,
    ← ofFn_inA2 a, ← ofFn_inB1 b, houtP, ofFn_inB1, ofFn_eq_inB1, ofFn_inA2_eq,
    realCoins_symm_fst_ofFn, realCoins_symm_snd_ofFn, senderNext_single, receiverNext_single,
    List.length_replicate, List.take_left' hlen, List.drop_left' hlen, List.headD_cons,
    ← NUPPT.runAt_eq, ← NUPPT.runAt_eq, ← NUPPT.runAt_eq, ← Collection.index_eq,
    ← Collection.trap_eq, Strategy.encodeMsgs_cons, Strategy.encodeMsgs_cons,
    Strategy.encodeMsgs_cons, Strategy.encodeMsgs_nil, bobView_eq]
  cases inB1 b 0
  · simp only [Bool.false_eq_true, if_false, pairFstD_pairEncode, pairSndD_pairEncode,
      mask_eval T H henc, mask_raw T H henc, List.getD_cons_zero, List.getD_cons_succ]
  · simp only [if_true, pairFstD_pairEncode, pairSndD_pairEncode,
      mask_eval T H henc, mask_raw T H henc, List.getD_cons_zero, List.getD_cons_succ]

/-- **Bob's ideal sampler on typed coins**: on `(r, s₁, s₂, c)` (`simBCoins`) it is
`bobView (1^n) b a₀ a₁ i (s₁ ++ s₂) (Sample(i; s₁)) (c ⊕ a_{1−b})` with `i = index n r`. -/
theorem idealB_simBCoins {S : NUPPT} (hS : IsSimB T H S) (n : ℕ)
    (a : Fin (otFunctionality.inA.eval n) → Bool) (b : Fin (otFunctionality.inB.eval n) → Bool)
    (p : T.gen.Coins n × (T.sample.Coins n × (T.sample.Coins n × (Fin 1 → Bool)))) :
    otFunctionality.idealB S n a b ((simBCoins T H hS n).symm p) =
      bobView H (List.replicate n true) (inB1 b 0) (inA2 a 0) (inA2 a 1) (T.index n p.1)
        (List.ofFn p.2.1 ++ List.ofFn p.2.2.1) (T.sample.runAt n (T.index n p.1) p.2.1)
        (xor (p.2.2.2 0) (if inB1 b 0 then inA2 a 0 else inA2 a 1)) := by
  have hc : List.ofFn p.2.2.2 = [p.2.2.2 0] := by rw [List.ofFn_succ, List.ofFn_zero]
  rw [Functionality.idealB_eq, ((isSimB_iff T H S).1 hS).2, simBCoins_symm_ofFn, simBView_layout,
    pairFstD_pairEncode, pairSndD_pairEncode, ofFn_f_snd, ofFn_f_fst, ofFn_eq_inB1,
    List.headD_cons, hc, bobView_eq]
  cases inB1 b 0 <;> simp

/-! ### Acceptance probabilities -/

/-- `D`'s acceptance probability of Bob's view at the index of `r` with the unselected bit
`g(s₂)`: `accB T H D n b a₀ a₁ r g = Pr_{s₁, s₂, ρ}[D(bobView … (s₁ ++ s₂) (Sample(i; s₁))
(g s₂); ρ) = 1]`. -/
noncomputable def accB (D : NUPPT) (n : ℕ) (b a₀ a₁ : Bool) (r : T.gen.Coins n)
    (g : T.sample.Coins n → Bool) : ℝ :=
  uprob fun q : (T.sample.Coins n × T.sample.Coins n) × D.Coins n =>
    D.distinguisherL n (bobView H (List.replicate n true) b a₀ a₁ (T.index n r)
      (List.ofFn q.1.1 ++ List.ofFn q.1.2) (T.sample.runAt n (T.index n r) q.1.1) (g q.1.2))
      q.2 = true

/-- The defining equation of `accB`: `accB T H D n b a₀ a₁ r g =
Pr_{((s₁, s₂), ρ)}[D(bobView … (s₁ ++ s₂) (Sample(i; s₁)) (g s₂); ρ) = 1]`. -/
theorem accB_eq (D : NUPPT) (n : ℕ) (b a₀ a₁ : Bool) (r : T.gen.Coins n)
    (g : T.sample.Coins n → Bool) :
    accB T H D n b a₀ a₁ r g =
      uprob fun q : (T.sample.Coins n × T.sample.Coins n) × D.Coins n =>
        D.distinguisherL n (bobView H (List.replicate n true) b a₀ a₁ (T.index n r)
          (List.ofFn q.1.1 ++ List.ofFn q.1.2) (T.sample.runAt n (T.index n r) q.1.1) (g q.1.2))
          q.2 = true := rfl

/-- **Bob's real acceptance** is the average over `Gen`'s coins of `accB` with the enhanced bit:
`acceptProb realB D = E_r accB … r (hcBit T h n r)`. -/
theorem acceptProb_realB {h : ∀ i, T.D i → Bool}
    (henc : ∀ i (x : T.D i), H (pairEncode i (T.encD i x)) = [h i x]) {π : Protocol}
    (hπ : IsOT T H π)
    (houtP : ∀ x (a : Fin 2 → Bool) (b : Fin 1 → Bool) (r : π.ExecCoins π.P x),
      π.outP x (List.ofFn a) (List.ofFn b) r = [])
    (D : NUPPT) (n : ℕ) (a : Fin (otFunctionality.inA.eval n) → Bool)
    (b : Fin (otFunctionality.inB.eval n) → Bool) :
    acceptProb (otFunctionality.realB π n a b) (D.distinguisherL n) =
      uexp fun r => accB T H D n (inB1 b 0) (inA2 a 0) (inA2 a 1) r (hcBit T h n r) := by
  rw [← acceptProb_comp_equiv (realCoins T H hπ n).symm, acceptProb_def]
  simp only [realB_realCoins T H henc hπ houtP]
  rw [← uprob_comp_equiv (Equiv.prodAssoc _ _ _).symm, uprob_prod]
  congr 1

/-- **Bob's ideal acceptance** is the average of the two `accB` with the enhanced bit and its
negation: `acceptProb idealB D = E_r (accB … r B + accB … r ¬B) / 2`.

**Proof sketch.** Relabel the coins as `(r, s₁, s₂, c)` (`simBCoins`, `idealB_simBCoins`), reorder
them as `(r, (c₀, ((s₁, s₂), ρ)))` by an explicit bijection `E` (`c` read as its bit `c₀`), average
over `r` (`uprob_prod`), and apply `uprob_xor_shear` to the unselected bit `c₀ ⊕ a_{1−b}`,
re-centred on `B(s₂)`. -/
theorem acceptProb_idealB {h : ∀ i, T.D i → Bool} {S : NUPPT} (hS : IsSimB T H S) (D : NUPPT)
    (n : ℕ) (a : Fin (otFunctionality.inA.eval n) → Bool)
    (b : Fin (otFunctionality.inB.eval n) → Bool) :
    acceptProb (otFunctionality.idealB S n a b) (D.distinguisherL n) =
      uexp fun r => (accB T H D n (inB1 b 0) (inA2 a 0) (inA2 a 1) r (hcBit T h n r) +
        accB T H D n (inB1 b 0) (inA2 a 0) (inA2 a 1) r (fun s => !hcBit T h n r s)) / 2 := by
  let E : T.gen.Coins n × (Bool × ((T.sample.Coins n × T.sample.Coins n) × D.Coins n)) ≃
      (T.gen.Coins n × (T.sample.Coins n × (T.sample.Coins n × (Fin 1 → Bool)))) × D.Coins n :=
    { toFun := fun w => ((w.1, (w.2.2.1.1, (w.2.2.1.2, fun _ => w.2.1))), w.2.2.2)
      invFun := fun z => (z.1.1, (z.1.2.2.2 0, ((z.1.2.1, z.1.2.2.1), z.2)))
      left_inv := fun w => rfl
      right_inv := fun z => by
        obtain ⟨⟨r, s₁, s₂, c⟩, ρ⟩ := z
        refine Prod.ext (Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (funext fun j => ?_)))) rfl
        rw [Subsingleton.elim j 0] }
  rw [← acceptProb_comp_equiv (simBCoins T H hS n).symm, acceptProb_def]
  simp only [idealB_simBCoins T H hS]
  rw [← uprob_comp_equiv E, uprob_prod]
  congr 1
  funext r
  simp only [E, Equiv.coe_fn_mk]
  rw [accB_eq, accB_eq]
  have key := uprob_xor_shear
    (fun q : (T.sample.Coins n × T.sample.Coins n) × D.Coins n => hcBit T h n r q.1.2)
    (if inB1 b 0 then inA2 a 0 else inA2 a 1) fun β q =>
      D.distinguisherL n (bobView H (List.replicate n true) (inB1 b 0) (inA2 a 0) (inA2 a 1)
        (T.index n r) (List.ofFn q.1.1 ++ List.ofFn q.1.2)
        (T.sample.runAt n (T.index n r) q.1.1) β) q.2 = true
  exact key

/-! ### The predictor machines -/

/-- **`D'`'s acceptance on `⟨i, ⟨s', [g s']⟩⟩` is `accB`**: over uniform `s'` and `D'`'s coins,
`D'` accepts `⟨i, ⟨s', [g s']⟩⟩` with probability `accB T H D n b a₀ a₁ r g` (`viewDistCoins`,
`distinguisherL_viewDist`, and the reordering `(s₂, (s₁, ρ)) ↦ ((s₁, s₂), ρ)`):
`acceptProb (fun x => (x, g x)) (fun yc ρ => D'.distinguisherL n ⟨i, ⟨ofFn yc.1, [yc.2]⟩⟩ ρ) =
accB T H D n b a₀ a₁ r g` with `D' = viewDist T hH D b a₀ a₁` and `i = T.index n r`. -/
theorem acceptProb_viewDist (hH : PolyTimeComputable H) (D : NUPPT) (n : ℕ) (b a₀ a₁ : Bool)
    (r : T.gen.Coins n) (g : T.sample.Coins n → Bool) :
    acceptProb (fun x : T.sample.Coins n => (x, g x))
        (fun (yc : T.sample.Coins n × Bool) (ρ : (viewDist T hH D b a₀ a₁).Coins n) =>
          (viewDist T hH D b a₀ a₁).distinguisherL n
            (pairEncode (T.index n r) (pairEncode (List.ofFn yc.1) [yc.2])) ρ) =
      accB T H D n b a₀ a₁ r g := by
  let e : (T.sample.Coins n × T.sample.Coins n) × D.Coins n ≃
      T.sample.Coins n × (viewDist T hH D b a₀ a₁).Coins n :=
    { toFun := fun q => (q.1.2, (viewDistCoins T hH D b a₀ a₁ n).symm (q.1.1, q.2))
      invFun := fun z => ((((viewDistCoins T hH D b a₀ a₁ n) z.2).1, z.1),
        ((viewDistCoins T hH D b a₀ a₁ n) z.2).2)
      left_inv := fun q => by simp
      right_inv := fun z => by simp }
  rw [acceptProb_def, accB_eq, ← uprob_comp_equiv e]
  congr 1
  funext q
  simp only [e, Equiv.coe_fn_mk]
  rw [distinguisherL_viewDist]

/-- **The unflipped predictor's prediction experiment** at the index of `r`: the machine
`tdpPredictor D' false` predicts `hcBit T h n r s'` from `⟨i, s'⟩` with probability
`1/2 + (accB … r B − accB … r ¬B) / 2` (`uprob_tdpPredictor`, `uprob_signedPredictor_false`,
`acceptProb_viewDist`): `uprob (fun z => P.distinguisherL n ⟨T.index n r, ofFn z.1⟩ z.2 = B z.1) =
1 / 2 + (accB T H D n b a₀ a₁ r B - accB T H D n b a₀ a₁ r (fun s => !B s)) / 2` with
`P = tdpPredictor (viewDist T hH D b a₀ a₁) false` and `B = hcBit T h n r`. -/
theorem uprob_predictor_false (h : ∀ i, T.D i → Bool) (hH : PolyTimeComputable H) (D : NUPPT)
    (n : ℕ) (b a₀ a₁ : Bool) (r : T.gen.Coins n) :
    uprob (fun z : T.sample.Coins n × (tdpPredictor (viewDist T hH D b a₀ a₁) false).Coins n =>
        (tdpPredictor (viewDist T hH D b a₀ a₁) false).distinguisherL n
          (pairEncode (T.index n r) (List.ofFn z.1)) z.2 = hcBit T h n r z.1) =
      1 / 2 + (accB T H D n b a₀ a₁ r (hcBit T h n r) -
        accB T H D n b a₀ a₁ r (fun s => !hcBit T h n r s)) / 2 := by
  have h₁ := uprob_tdpPredictor (viewDist T hH D b a₀ a₁) false n (T.index n r)
    (id : T.sample.Coins n → T.sample.Coins n) (hcBit T h n r) List.ofFn
  have h₂ := uprob_signedPredictor_false (hcBit T h n r)
    (fun (yc : T.sample.Coins n × Bool) (ρ : (viewDist T hH D b a₀ a₁).Coins n) =>
      (viewDist T hH D b a₀ a₁).distinguisherL n
        (pairEncode (T.index n r) (pairEncode (List.ofFn yc.1) [yc.2])) ρ)
  rw [acceptProb_viewDist T H hH D n b a₀ a₁ r (hcBit T h n r),
    acceptProb_viewDist T H hH D n b a₀ a₁ r (fun s => !hcBit T h n r s)] at h₂
  exact h₁.trans h₂

/-- **The flipped predictor's prediction experiment**: `tdpPredictor D' true` predicts
`hcBit T h n r s'` with probability `1/2 − (accB … r B − accB … r ¬B) / 2`:
`uprob (fun z => P.distinguisherL n ⟨T.index n r, ofFn z.1⟩ z.2 = B z.1) =
1 / 2 - (accB T H D n b a₀ a₁ r B - accB T H D n b a₀ a₁ r (fun s => !B s)) / 2` with
`P = tdpPredictor (viewDist T hH D b a₀ a₁) true` and `B = hcBit T h n r`. -/
theorem uprob_predictor_true (h : ∀ i, T.D i → Bool) (hH : PolyTimeComputable H) (D : NUPPT)
    (n : ℕ) (b a₀ a₁ : Bool) (r : T.gen.Coins n) :
    uprob (fun z : T.sample.Coins n × (tdpPredictor (viewDist T hH D b a₀ a₁) true).Coins n =>
        (tdpPredictor (viewDist T hH D b a₀ a₁) true).distinguisherL n
          (pairEncode (T.index n r) (List.ofFn z.1)) z.2 = hcBit T h n r z.1) =
      1 / 2 - (accB T H D n b a₀ a₁ r (hcBit T h n r) -
        accB T H D n b a₀ a₁ r (fun s => !hcBit T h n r s)) / 2 := by
  have h₁ := uprob_tdpPredictor (viewDist T hH D b a₀ a₁) true n (T.index n r)
    (id : T.sample.Coins n → T.sample.Coins n) (hcBit T h n r) List.ofFn
  have h₂ := uprob_signedPredictor_true (hcBit T h n r)
    (fun (yc : T.sample.Coins n × Bool) (ρ : (viewDist T hH D b a₀ a₁).Coins n) =>
      (viewDist T hH D b a₀ a₁).distinguisherL n
        (pairEncode (T.index n r) (pairEncode (List.ofFn yc.1) [yc.2])) ρ)
  rw [acceptProb_viewDist T H hH D n b a₀ a₁ r (hcBit T h n r),
    acceptProb_viewDist T H hH D n b a₀ a₁ r (fun s => !hcBit T h n r s)] at h₂
  exact h₁.trans h₂

/-! ### Bob's side -/

/-- **Bob's side for fixed inputs**: if the two predictors `tdpPredictor D' false/true` for the
bits `(b, a₀, a₁)` of the inputs predict the enhanced bit with probability at most `1/2 + ε_false`
and `1/2 + ε_true` at `n`, then `D`'s advantage between Bob's real and ideal samplers is at most
`|ε_false| + |ε_true|`:
`distAdv (realB π n a b) (idealB S n a b) (D.distinguisherL n) ≤ |εf| + |εt|` under `hf`, `ht`.

**Proof sketch.** With `U± = E_r accB … r (±B)`, the real acceptance is `U+`
(`acceptProb_realB`) and the ideal one `(U+ + U−)/2` (`acceptProb_idealB`), so the advantage is
`|U+ − U−| / 2`. The predictors give `U+ − U− ≤ 2ε_false` and `U− − U+ ≤ 2ε_true`
(`uprob_predictor_false/true`, `uexp_half_add/sub`). -/
theorem distAdv_realB_idealB_le {h : ∀ i, T.D i → Bool} (hH : PolyTimeComputable H)
    (henc : ∀ i (x : T.D i), H (pairEncode i (T.encD i x)) = [h i x]) {π : Protocol}
    (hπ : IsOT T H π)
    (houtP : ∀ x (a : Fin 2 → Bool) (b : Fin 1 → Bool) (r : π.ExecCoins π.P x),
      π.outP x (List.ofFn a) (List.ofFn b) r = [])
    {S : NUPPT} (hS : IsSimB T H S) (D : NUPPT) (n : ℕ)
    (a : Fin (otFunctionality.inA.eval n) → Bool) (b : Fin (otFunctionality.inB.eval n) → Bool)
    {εf εt : ℝ}
    (hf : uexp (fun r : T.gen.Coins n => uprob fun z : T.sample.Coins n ×
        (tdpPredictor (viewDist T hH D (inB1 b 0) (inA2 a 0) (inA2 a 1)) false).Coins n =>
      (tdpPredictor (viewDist T hH D (inB1 b 0) (inA2 a 0) (inA2 a 1)) false).distinguisherL n
        (pairEncode (T.index n r) (List.ofFn z.1)) z.2 = hcBit T h n r z.1) ≤ 1 / 2 + εf)
    (ht : uexp (fun r : T.gen.Coins n => uprob fun z : T.sample.Coins n ×
        (tdpPredictor (viewDist T hH D (inB1 b 0) (inA2 a 0) (inA2 a 1)) true).Coins n =>
      (tdpPredictor (viewDist T hH D (inB1 b 0) (inA2 a 0) (inA2 a 1)) true).distinguisherL n
        (pairEncode (T.index n r) (List.ofFn z.1)) z.2 = hcBit T h n r z.1) ≤ 1 / 2 + εt) :
    distAdv (otFunctionality.realB π n a b) (otFunctionality.idealB S n a b)
      (D.distinguisherL n) ≤ |εf| + |εt| := by
  simp only [uprob_predictor_false T H h hH D n, uprob_predictor_true T H h hH D n] at hf ht
  rw [uexp_half_add] at hf
  rw [uexp_half_sub] at ht
  rw [distAdv_def, acceptProb_realB T H henc hπ houtP, acceptProb_idealB T H (h := h) hS,
    show (fun r => (accB T H D n (inB1 b 0) (inA2 a 0) (inA2 a 1) r (hcBit T h n r) +
        accB T H D n (inB1 b 0) (inA2 a 0) (inA2 a 1) r (fun s => !hcBit T h n r s)) / 2) =
      fun r => (1 / 2 : ℝ) * (accB T H D n (inB1 b 0) (inA2 a 0) (inA2 a 1) r (hcBit T h n r) +
        accB T H D n (inB1 b 0) (inA2 a 0) (inA2 a 1) r (fun s => !hcBit T h n r s)) from
      funext fun r => by ring,
    HardcoreBit.uexp_const_mul, HardcoreBit.uexp_add]
  generalize uexp (fun r => accB T H D n (inB1 b 0) (inA2 a 0) (inA2 a 1) r (hcBit T h n r)) = U₁
    at hf ht ⊢
  generalize uexp (fun r => accB T H D n (inB1 b 0) (inA2 a 0) (inA2 a 1) r
    (fun s => !hcBit T h n r s)) = U₂ at hf ht ⊢
  have h₁ := le_abs_self εf
  have h₂ := le_abs_self εt
  have h₃ := abs_nonneg εf
  have h₄ := abs_nonneg εt
  rw [abs_le]
  constructor <;> linarith

/-- **Bob's side of Proposition 161.5** [PS10]: under the enhanced hard-core hypothesis (stated
explicitly, `hEHC`), for every distinguisher `D` there is a negligible `ε ≥ 0` bounding `D`'s
advantage between Bob's real and ideal samplers for all `n` and all inputs.

**Proof sketch.** `hEHC` gives a negligible `ε_{t, fl}` for each of the sixteen predictors
`tdpPredictor (viewDist D t) fl`, `t = (b, a₀, a₁)`, `fl ∈ {0, 1}`. Take
`ε(n) = Σ_t Σ_fl |ε_{t, fl}(n)|` (negligible by `negligible_finset_sum`): for the inputs' bits
`t`, `distAdv_realB_idealB_le` bounds the advantage by `|ε_{t, 0}(n)| + |ε_{t, 1}(n)| ≤ ε(n)`. -/
theorem exists_negligible_bob {h : ∀ i, T.D i → Bool} (hH : PolyTimeComputable H)
    (henc : ∀ i (x : T.D i), H (pairEncode i (T.encD i x)) = [h i x]) {π : Protocol}
    (hπ : IsOT T H π)
    (houtP : ∀ x (a : Fin 2 → Bool) (b : Fin 1 → Bool) (r : π.ExecCoins π.P x),
      π.outP x (List.ofFn a) (List.ofFn b) r = [])
    {S : NUPPT} (hS : IsSimB T H S)
    (hEHC : ∀ A : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n,
      uexp (fun r : T.gen.Coins n =>
        uprob fun z : T.sample.Coins n × A.Coins n =>
          A.distinguisherL n (pairEncode (T.index n r) (List.ofFn z.1)) z.2 =
            h (T.index n r) ((T.perm (T.index n r)).symm
              ((T.decD (T.index n r) (T.sample.runAt n (T.index n r) z.1)).getD default)))
        ≤ 1 / 2 + ε n)
    (D : NUPPT) :
    ∃ ε : ℕ → ℝ, Negligible ε ∧ (∀ n, 0 ≤ ε n) ∧
      ∀ n (a : Fin (otFunctionality.inA.eval n) → Bool)
        (b : Fin (otFunctionality.inB.eval n) → Bool),
        distAdv (otFunctionality.realB π n a b) (otFunctionality.idealB S n a b)
          (D.distinguisherL n) ≤ ε n := by
  choose ε hε hb using fun (t : Bool × Bool × Bool) (fl : Bool) =>
    hEHC (tdpPredictor (viewDist T hH D t.1 t.2.1 t.2.2) fl)
  refine ⟨fun n => ∑ t : Bool × Bool × Bool, ∑ fl : Bool, |ε t fl n|,
    negligible_finset_sum _ fun t _ => negligible_finset_sum _ fun fl _ =>
      (hε t fl).mono ⟨0, fun n _ => (abs_abs _).le⟩,
    fun n => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _,
    fun n a b => ?_⟩
  refine (distAdv_realB_idealB_le T H hH henc hπ houtP hS D n a b
    (hb (inB1 b 0, inA2 a 0, inA2 a 1) false n) (hb (inB1 b 0, inA2 a 0, inA2 a 1) true n)).trans ?_
  have hsum : ∑ fl : Bool, |ε (inB1 b 0, inA2 a 0, inA2 a 1) fl n| =
      |ε (inB1 b 0, inA2 a 0, inA2 a 1) false n| + |ε (inB1 b 0, inA2 a 0, inA2 a 1) true n| := by
    rw [Fintype.sum_bool, add_comm]
  rw [← hsum]
  exact Finset.single_le_sum (f := fun t => ∑ fl : Bool, |ε t fl n|)
    (fun t _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ _)

/-- **Proposition 161.5 with its simulators** [PS10], for every protocol of the shape of
Protocol 160.4 (with Bob's output `[a_b]` and Alice's `[]`) and every pair of machines of the
shapes of `S_A` and `S_B`: for a collection of one-way trapdoor permutations with an enhanced
hard-core predicate (`hEHC`, explicit) evaluated on encodings by `H`, each distinguisher has
a negligible `ε` bounding both advantages for all `n` and all inputs:
`∀ D, ∃ ε, Negligible ε ∧ ∀ n x y, distAdv (realA π n x y) (idealA SA n x y) (D.distinguisherL n)
≤ ε n ∧ distAdv (realB π n x y) (idealB SB n x y) (D.distinguisherL n) ≤ ε n`.

**Proof sketch.** `T.OneWay` gives a negligible `δ` with `SampleClose δ`. Alice's side is at
most `2δ(n)` (`distAdv_realA_idealA_le`), Bob's at most a negligible `ε_B(n) ≥ 0`
(`exists_negligible_bob`). Take `ε(n) = 2|δ(n)| + ε_B(n)`. -/
theorem simulators_of_isOT {h : ∀ i, T.D i → Bool} (hH : PolyTimeComputable H)
    (henc : ∀ i (x : T.D i), H (pairEncode i (T.encD i x)) = [h i x]) {π : Protocol}
    (hπ : IsOT T H π)
    (houtV : ∀ x (a : Fin 2 → Bool) (b : Fin 1 → Bool) (r : π.ExecCoins π.P x),
      π.outV π.P x (List.ofFn a) (List.ofFn b) r = [a (if b 0 then 1 else 0)])
    (houtP : ∀ x (a : Fin 2 → Bool) (b : Fin 1 → Bool) (r : π.ExecCoins π.P x),
      π.outP x (List.ofFn a) (List.ofFn b) r = [])
    {SA SB : NUPPT} (hSA : IsSimA T SA) (hSB : IsSimB T H SB) (hT : T.OneWay)
    (hEHC : ∀ A : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n,
      uexp (fun r : T.gen.Coins n =>
        uprob fun z : T.sample.Coins n × A.Coins n =>
          A.distinguisherL n (pairEncode (T.index n r) (List.ofFn z.1)) z.2 =
            h (T.index n r) ((T.perm (T.index n r)).symm
              ((T.decD (T.index n r) (T.sample.runAt n (T.index n r) z.1)).getD default)))
        ≤ 1 / 2 + ε n) :
    ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n (x : Fin (otFunctionality.inA.eval n) → Bool)
        (y : Fin (otFunctionality.inB.eval n) → Bool),
        distAdv (otFunctionality.realA π n x y) (otFunctionality.idealA SA n x y)
            (D.distinguisherL n) ≤ ε n ∧
          distAdv (otFunctionality.realB π n x y) (otFunctionality.idealB SB n x y)
            (D.distinguisherL n) ≤ ε n := by
  obtain ⟨δ, hδ, hδS⟩ := ((TrapdoorCollection.oneWay_iff T).1 hT).sampleClose
  intro D
  obtain ⟨εB, hεB, h0, hB⟩ := exists_negligible_bob T H hH henc hπ houtP hSB hEHC D
  refine ⟨fun n => 2 * |δ n| + εB n,
    ((hδ.mono ⟨0, fun n _ => (abs_abs _).le⟩).const_mul 2).add hεB, fun n x y => ⟨?_, ?_⟩⟩
  · have hA := distAdv_realA_idealA_le T H hπ houtV hSA hδS D n x y
    have := le_abs_self (δ n)
    have := h0 n
    linarith
  · have := hB n x y
    have := abs_nonneg (δ n)
    linarith

end TCSlib.Cryptography.SecureComputation.OT

## ===== TCSlib/Cryptography/SecureComputation/Defs.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.ZeroKnowledge.Interaction
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Foundations.Experiments
import TCSlib.Cryptography.Foundations.Negligible

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Two-party secure computation in the honest-but-curious model (definitions)

[PS10, Definition 155.1]: a protocol `π` with security parameter `1^n` securely computes
`f(x, y)` in the honest-but-curious model if there are non-uniform PPT simulators `S_A`, `S_B`
such that, for all inputs `x, y`,
- `{S_A(x, f(x, y)), f(x, y)} ≈ {e ← [A(x) ↔ B(y)] : view_A(e), out_B(e)}`, and
- `{S_B(y, f(x, y)), f(x, y)} ≈ {e ← [A(x) ↔ B(y)] : view_B(e), out_A(e)}`.

The output clause makes the definition imply correctness: without it, a protocol in which both
parties output `0` would be secure (the source's remark).

**On the ch. 2–4 interaction model** (D8; ruling of 2026-11-05: strategies define). Alice plays
the prover's role and Bob the verifier's. The common input is `1^n`; Alice's input travels as the
prover's private input `y` of `Protocol` and Bob's as the verifier's auxiliary input `z`. The views
are `Protocol.viewP` and `Protocol.viewV`, the outputs `Protocol.outP` and `Protocol.outV`, and
a view reaches the distinguisher encoded (`View.encode`).

**Deviations.**
- **Private outputs.** The functionality has an output for each party, `f = (f_A, f_B)`. The
  definition writes one `f(x, y)` for both, but the oblivious-transfer functionality it is
  applied to (Def 160.a) has private outputs `(⊥, a_b)`.
- **Lengths.** Inputs and outputs have polynomial lengths in `n`, not exactly `n` (OT's inputs
  are bits).
- **Uniformity.** "For all `x, y`" is read with one negligible bound for all inputs of each
  length (`ε` before `x, y`), the convention of the ch. 2–4 layer's security definitions.
- **Polynomial time** (ruling of 2026-11-05). The definition leaves the parties' efficiency to
  §4.4's convention; here it is required (`Functionality.PolyTime`). Both strategies are PPT, and
  the messages of honest executions are polynomially bounded. Under D8, `Strategy.Efficient`
  alone bounds an activation by the length of the messages received, not by `n`.

## Main definitions

* `SecureComputation.Functionality`: a two-party functionality with private outputs.
* `Functionality.realA`, `idealA`, `realB`, `idealB`: the four samplers of Def 155.1.
* `SecureComputation.Functionality.PolyTime`: the parties run in polynomial time.
* `SecureComputation.HBCSecure`: [PS10, Definition 155.1].
* `SecureComputation.otFunctionality`: [PS10, Def 160.a], `OT(a₁, a₂, b) = (⊥, a_b)`.

## Main results

* `Functionality.realA_eq`, `realB_eq`, `idealA_eq`, `idealB_eq`: the four sampler equations.
* `Functionality.polyTime_iff`, `SecureComputation.hbcSecure_iff`: the time and security clauses.
* `SecureComputation.otFunctionality_inA`, `otFunctionality_inB`, `otFunctionality_outA`,
  `otFunctionality_outB`, `otFunctionality_f`: the OT functionality's fields.
* `SecureComputation.otFunctionality_f_snd`: the OT functionality gives Bob the chosen bit.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2, Definition 155.1 and §6.2.4 (book pp. 155–156, 160).
-/

namespace TCSlib.Cryptography.SecureComputation

open Complexity Turing TCSlib.Cryptography

/-- A **two-party functionality** with private outputs: Alice's and Bob's inputs have
`inA(n)` and `inB(n)` bits, and `f` gives Alice an `outA(n)`-bit and Bob an `outB(n)`-bit
output. -/
structure Functionality where
  /-- Alice's input length. -/
  inA : PolyExpr
  /-- Bob's input length. -/
  inB : PolyExpr
  /-- Alice's output length. -/
  outA : PolyExpr
  /-- Bob's output length. -/
  outB : PolyExpr
  /-- The function `(x, y) ↦ (f_A(x, y), f_B(x, y))`. -/
  f : ∀ n, (Fin (inA.eval n) → Bool) → (Fin (inB.eval n) → Bool) →
    (Fin (outA.eval n) → Bool) × (Fin (outB.eval n) → Bool)

namespace Functionality

variable (F : Functionality)

/-- **The real sampler for Alice's side**: on the coins of an honest execution
`A(x) ↔ B(y)` with common input `1^n`, the pair `⟨view_A, out_B⟩`. -/
def realA (π : Protocol) (n : ℕ) (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) :
    π.ExecCoins π.P (List.replicate n true) → List Bool := fun r =>
  pairEncode (π.viewP (List.replicate n true) (List.ofFn x) (List.ofFn y) r).encode
    (π.outV π.P (List.replicate n true) (List.ofFn x) (List.ofFn y) r)

/-- Alice's real sampler pairs her encoded view with Bob's output on the honest tapes. -/
theorem realA_eq (π : Protocol) (n : ℕ) (x : Fin (F.inA.eval n) → Bool)
    (y : Fin (F.inB.eval n) → Bool) (r : π.ExecCoins π.P (List.replicate n true)) :
    F.realA π n x y r =
      pairEncode (π.viewP (List.replicate n true) (List.ofFn x) (List.ofFn y) r).encode
        (π.outV π.P (List.replicate n true) (List.ofFn x) (List.ofFn y) r) := rfl

/-- **The real sampler for Bob's side**: `⟨view_B, out_A⟩`. -/
def realB (π : Protocol) (n : ℕ) (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) :
    π.ExecCoins π.P (List.replicate n true) → List Bool := fun r =>
  pairEncode (π.viewV (List.replicate n true) (List.ofFn x) (List.ofFn y) r).encode
    (π.outP (List.replicate n true) (List.ofFn x) (List.ofFn y) r)

/-- Bob's real sampler pairs his encoded view with Alice's output on the honest tapes. -/
theorem realB_eq (π : Protocol) (n : ℕ) (x : Fin (F.inA.eval n) → Bool)
    (y : Fin (F.inB.eval n) → Bool) (r : π.ExecCoins π.P (List.replicate n true)) :
    F.realB π n x y r =
      pairEncode (π.viewV (List.replicate n true) (List.ofFn x) (List.ofFn y) r).encode
        (π.outP (List.replicate n true) (List.ofFn x) (List.ofFn y) r) := rfl

/-- **The ideal sampler for Alice's side**: `⟨S_A(1^n, ⟨x, f_A(x, y)⟩), f_B(x, y)⟩`. -/
def idealA (S : NUPPT) (n : ℕ) (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) :
    S.Coins n → List Bool := fun s =>
  pairEncode (S.runAt n (pairEncode (List.ofFn x) (List.ofFn (F.f n x y).1)) s)
    (List.ofFn (F.f n x y).2)

/-- Alice's ideal sampler pairs her simulation from her input and output with Bob's output. -/
theorem idealA_eq (S : NUPPT) (n : ℕ) (x : Fin (F.inA.eval n) → Bool)
    (y : Fin (F.inB.eval n) → Bool) (s : S.Coins n) :
    F.idealA S n x y s =
      pairEncode (S.runAt n (pairEncode (List.ofFn x) (List.ofFn (F.f n x y).1)) s)
        (List.ofFn (F.f n x y).2) := rfl

/-- **The ideal sampler for Bob's side**: `⟨S_B(1^n, ⟨y, f_B(x, y)⟩), f_A(x, y)⟩`. -/
def idealB (S : NUPPT) (n : ℕ) (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) :
    S.Coins n → List Bool := fun s =>
  pairEncode (S.runAt n (pairEncode (List.ofFn y) (List.ofFn (F.f n x y).2)) s)
    (List.ofFn (F.f n x y).1)

/-- Bob's ideal sampler pairs his simulation from his input and output with Alice's output. -/
theorem idealB_eq (S : NUPPT) (n : ℕ) (x : Fin (F.inA.eval n) → Bool)
    (y : Fin (F.inB.eval n) → Bool) (s : S.Coins n) :
    F.idealB S n x y s =
      pairEncode (S.runAt n (pairEncode (List.ofFn y) (List.ofFn (F.f n x y).2)) s)
        (List.ofFn (F.f n x y).1) := rfl

/-- **The parties run in polynomial time** on `F`'s inputs (ruling of 2026-11-05).
- Both strategies are PPT (`Strategy.Efficient`).
- For a polynomial `B`, in every honest execution with common input `1^n` and inputs of `F`'s
  lengths, every message has at most `B(n)` bits.

Under D8 a PPT strategy's activation is polynomial in its whole input, the messages received
included. With the honest messages bounded and `rounds(n)` activations, each party's work in an
honest execution (the only kind in this model) is polynomial in `n`. -/
def PolyTime (π : Protocol) : Prop :=
  π.P.Efficient ∧ π.V.Efficient ∧ ∃ B : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool)
    (y : Fin (F.inB.eval n) → Bool) (r : π.ExecCoins π.P (List.replicate n true)),
    ∀ msg ∈ (π.transcript (List.replicate n true) (List.ofFn x) (List.ofFn y) r).1 ++
        (π.transcript (List.replicate n true) (List.ofFn x) (List.ofFn y) r).2,
      msg.length ≤ B.eval n

/-- Polynomial time means efficient strategies and a uniform polynomial bound on every
message in every honest execution on inputs of the functionality's lengths. -/
theorem polyTime_iff (π : Protocol) :
    F.PolyTime π ↔
      π.P.Efficient ∧ π.V.Efficient ∧ ∃ B : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool)
        (y : Fin (F.inB.eval n) → Bool) (r : π.ExecCoins π.P (List.replicate n true)),
        ∀ msg ∈ (π.transcript (List.replicate n true) (List.ofFn x) (List.ofFn y) r).1 ++
            (π.transcript (List.replicate n true) (List.ofFn x) (List.ofFn y) r).2,
          msg.length ≤ B.eval n := Iff.rfl

end Functionality

/-- **Honest-but-curious security** [PS10, Definition 155.1]: the parties run in polynomial time
(`Functionality.PolyTime`; see the module docstring), and there are non-uniform PPT simulators
`S_A`, `S_B` such that for every non-uniform PPT distinguisher `D` there is a negligible `ε` with,
for all `n` and all inputs `x`, `y`, `D`'s advantage between Alice's real and ideal samplers, and
between Bob's, at most `ε(n)`. -/
def HBCSecure (π : Protocol) (F : Functionality) : Prop :=
  F.PolyTime π ∧ ∃ SA SB : NUPPT, ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool),
      distAdv (F.realA π n x y) (F.idealA SA n x y) (D.distinguisherL n) ≤ ε n ∧
        distAdv (F.realB π n x y) (F.idealB SB n x y) (D.distinguisherL n) ≤ ε n

/-- Honest-but-curious security consists of polynomial time and two simulators whose
distinguishing advantages have a negligible bound uniform over inputs of each length. -/
theorem hbcSecure_iff (π : Protocol) (F : Functionality) :
    HBCSecure π F ↔
      F.PolyTime π ∧ ∃ SA SB : NUPPT, ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
        ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool),
          distAdv (F.realA π n x y) (F.idealA SA n x y) (D.distinguisherL n) ≤ ε n ∧
            distAdv (F.realB π n x y) (F.idealB SB n x y) (D.distinguisherL n) ≤ ε n := Iff.rfl

/-- **1-out-of-2 oblivious transfer** [PS10, Def 160.a]: the sender Alice holds bits `(a₁, a₂)`,
the receiver Bob a choice bit `b` (`false` for `1`, `true` for `2`);
`OT(a₁, a₂, b) = (⊥, a_b)`, with Alice's `⊥` the empty output. -/
def otFunctionality : Functionality where
  inA := .const 2
  inB := .const 1
  outA := .const 0
  outB := .const 1
  f _ (a : Fin 2 → Bool) (b : Fin 1 → Bool) := (Fin.elim0, fun _ => a (if b 0 then 1 else 0))

/-- Alice's OT input consists of two bits. -/
theorem otFunctionality_inA : otFunctionality.inA = .const 2 := rfl

/-- Bob's OT input consists of one choice bit. -/
theorem otFunctionality_inB : otFunctionality.inB = .const 1 := rfl

/-- Alice's OT output is empty. -/
theorem otFunctionality_outA : otFunctionality.outA = .const 0 := rfl

/-- Bob's OT output consists of one bit. -/
theorem otFunctionality_outB : otFunctionality.outB = .const 1 := rfl

/-- OT returns the empty output to Alice and the selected input bit to Bob. -/
theorem otFunctionality_f (n : ℕ) (a : Fin 2 → Bool) (b : Fin 1 → Bool) :
    otFunctionality.f n a b =
      ((Fin.elim0 : Fin 0 → Bool), fun _ : Fin 1 => a (if b 0 then 1 else 0)) := rfl

/-- The OT functionality gives Bob the chosen bit. -/
theorem otFunctionality_f_snd (n : ℕ) (a : Fin 2 → Bool) (b : Fin 1 → Bool) :
    ((otFunctionality.f n a b).2 : Fin 1 → Bool) = fun _ => a (if b 0 then 1 else 0) := rfl

/-- Bob's OT output at any typed output index is Alice's input selected by Bob's typed choice
bit. The input indices use the published identifications of OT's two-bit and one-bit domains. -/
theorem otFunctionality_f_snd_apply (n : ℕ)
    (a : Fin (otFunctionality.inA.eval n) → Bool)
    (b : Fin (otFunctionality.inB.eval n) → Bool)
    (j : Fin (otFunctionality.outB.eval n)) :
    (otFunctionality.f n a b).2 j =
      a (Fin.cast ((congrArg (fun p : PolyExpr => p.eval n) otFunctionality_inA).trans
          (PolyExpr.eval_const 2 n)).symm
        (if b (Fin.cast ((congrArg (fun p : PolyExpr => p.eval n) otFunctionality_inB).trans
            (PolyExpr.eval_const 1 n)).symm (0 : Fin 1)) then (1 : Fin 2) else 0)) := rfl

end TCSlib.Cryptography.SecureComputation

## ===== TCSlib/Cryptography/Encryption/PublicKey/TrapdoorPredictor.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.Closure
import TCSlib.Complexity.Randomized.Repetition
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.OneWayFunctions.Basic
import Mathlib.Logic.Equiv.Fin.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Predictor support for trapdoor encryption

This module develops the predictor used for the security of Algorithm 104.3.
It gives the predictor's polynomial-time machine, coin split and probability identity.

## Main definitions

* `TCSlib.Cryptography.tdpPredFun` computes the predictor's output from a
  distinguisher verdict and its extra coin.
* `TCSlib.Cryptography.tdpPredictor` is the predictor machine and
  `TCSlib.Cryptography.predCoins` is its coin bijection.

## Main results

* `TCSlib.Cryptography.tdpPredictor_runAtL` gives the machine's run equation.
* `TCSlib.Cryptography.uprob_tdpPredictor` gives the probability identity used in
  the prediction lemma. `TCSlib.Cryptography.uexp_half_add` and
  `TCSlib.Cryptography.uexp_half_sub` evaluate the corresponding averages.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Theorem 104.4.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Theorem 3.2 (the predictor from a distinguisher).
-/

namespace TCSlib.Cryptography

open Complexity Turing

/-! ## The predictor machine of Theorem 104.4 -/

/-- The raw function of the predictor `A_flip` of [PS10, Theorem 104.4, proof] on the layout
`⟨⟨⟨1^n, ⟨i, y⟩⟩, α⟩, c :: ρ⟩`: run `D` on `⟨1^n, ⟨i, ⟨y, [c]⟩⟩⟩` with advice `α` and coins `ρ`,
and output `[c ⊕ ¬verdict ⊕ flip]` (`c` if `D` accepts, `1 − c` otherwise, negated when `flip`). -/
def tdpPredFun (D : NUPPT) (flip : Bool) (z : List Bool) : List Bool :=
  [xor (xor ((NUPPT.inCoins z).headD false)
    (!decide (D.output (NUPPT.layout (NUPPT.inParam z)
      (pairEncode (pairFstD (NUPPT.inArg z))
        (pairEncode (pairSndD (NUPPT.inArg z)) [(NUPPT.inCoins z).headD false]))
      (NUPPT.inAdvice z) (NUPPT.inCoins z).tail) = [true]))) flip]

/-- The raw predictor is polynomial-time (`polyTimeComputable_headD`, `Complexity.polyTimeComputable_tail`,
`polyTimeComputable_pairEq` for the verdict,
`BinArith.polyTimeComputable_xor`/`polyTimeComputable_not`).

**Proof sketch.** The first coin `c` is the head of the coin projection; `D` runs on the
layout with argument `⟨fst y, ⟨snd y, [c]⟩⟩`, the advice and the remaining coins (the tail,
`polyTimeComputable_tail` through `List.drop_one`), which is `D.polyTimeComputable_output`
after `NUPPT.polyTimeComputable_layout`; the verdict `[D's output = [true]]` is
`polyTimeComputable_pairEq`; the output `c ⊕ ¬verdict ⊕ flip` is two
`BinArith.polyTimeComputable_xor` with `polyTimeComputable_not` and a constant. -/
theorem tdpPredFun_poly (D : NUPPT) (flip : Bool) : PolyTimeComputable (tdpPredFun D flip) := by
  have hc : PolyTimeComputable fun z => [(NUPPT.inCoins z).headD false] :=
    polyTimeComputable_headD.comp NUPPT.polyTimeComputable_inCoins
  have hout := D.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout
    NUPPT.polyTimeComputable_inParam
    ((polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg).pairEncode
      ((polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg).pairEncode hc))
    NUPPT.polyTimeComputable_inAdvice
      ((polyTimeComputable_tail.congr fun _ => List.drop_one).comp
        NUPPT.polyTimeComputable_inCoins))
  have hv : PolyTimeComputable fun z => [decide (D.output (NUPPT.layout (NUPPT.inParam z)
      (pairEncode (pairFstD (NUPPT.inArg z))
        (pairEncode (pairSndD (NUPPT.inArg z)) [(NUPPT.inCoins z).headD false]))
      (NUPPT.inAdvice z) (NUPPT.inCoins z).tail) = [true])] := by
    convert polyTimeComputable_pairEq.comp (hout.pairEncode (polyTimeComputable_const [true]))
      using 1
    funext z
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  exact BinArith.polyTimeComputable_xor (BinArith.polyTimeComputable_xor hc
      (polyTimeComputable_not hv))
    (polyTimeComputable_const [flip])

/-- **The predictor machine** `A_flip` of [PS10, Theorem 104.4, proof]: `D`'s advice, coins
`1 + D.coins` (the extra bit `c` first). -/
noncomputable def tdpPredictor (D : NUPPT) (flip : Bool) : NUPPT :=
  NUPPT.ofPolyTime (tdpPredFun_poly D flip) (.add (.const 1) D.coins) D.adv D.advice
    D.advice_length

/-- The coin polynomial of the predictor machine. -/
@[simp] theorem tdpPredictor_coins (D : NUPPT) (flip : Bool) :
    (tdpPredictor D flip).coins = .add (.const 1) D.coins := by
  unfold tdpPredictor
  exact NUPPT.coins_ofPolyTime _ _ _ _ _

/-- The coin count of the predictor machine: `1 + |D's coins at n|`. -/
theorem tdpPredictor_coinLen (D : NUPPT) (n : ℕ) :
    1 + D.coinLen n = (PolyExpr.add (.const 1) D.coins).eval n := by
  rw [NUPPT.coinLen_eq, PolyExpr.eval_add, PolyExpr.eval_const]

/-- Unfolding of the predictor machine: on `⟨i, y⟩` with coins `c :: ρ` it outputs
`[c ⊕ ¬[D(1^n, ⟨i, ⟨y, [c]⟩⟩; ρ) = 1] ⊕ flip]`. -/
theorem tdpPredictor_runAtL (D : NUPPT) (flip : Bool) (n : ℕ) (i y : List Bool) (c : Bool)
    (ρ : List Bool) :
    (tdpPredictor D flip).runAtL n (pairEncode i y) (c :: ρ) =
      [xor (xor c (!decide (D.runAtL n (pairEncode i (pairEncode y [c])) ρ = [true]))) flip] := by
  unfold tdpPredictor
  rw [NUPPT.runAtL_ofPolyTime]
  simp [tdpPredFun, NUPPT.inCoins_eq, NUPPT.inParam_eq, NUPPT.inArg_eq, NUPPT.inAdvice_eq,
      NUPPT.advInput_eq,
    NUPPT.layout_eq, NUPPT.runAtL_eq]

/-- The coins of the predictor machine: the bit `c` followed by the coins of `D`. -/
noncomputable def predCoins (D : NUPPT) (flip : Bool) (n : ℕ) :
    Bool × D.Coins n ≃ (tdpPredictor D flip).Coins n :=
  ((Equiv.funUnique (Fin 1) Bool).symm.prodCongr (Equiv.refl _)).trans
    ((Fin.appendEquiv 1 (D.coinLen n)).trans
      ((Equiv.arrowCongr (finCongr (tdpPredictor_coinLen D n)) (Equiv.refl Bool)).trans
        (NUPPT.coinsEquivPoly (tdpPredictor_coins D flip) n).symm))

/-- The coin string of `predCoins (c, ρ)` is `c :: ρ`. -/
theorem ofFn_predCoins (D : NUPPT) (flip : Bool) (n : ℕ) (c : Bool) (ρ : D.Coins n) :
    List.ofFn (predCoins D flip n (c, ρ)) = c :: List.ofFn ρ := by
  unfold predCoins
  rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.trans_apply, NUPPT.coinsEquivPoly_symm_ofFn]
  refine (List.ofFn_congr (tdpPredictor_coinLen D n) (Fin.appendEquiv 1 (D.coinLen n)
    (((Equiv.funUnique (Fin 1) Bool).symm.prodCongr (Equiv.refl (D.Coins n))) (c, ρ)))).symm.trans
    ?_
  exact (List.ofFn_fin_append _ _).trans rfl

/-- `if v then c else ¬c` is `c ⊕ ¬v`. -/
theorem ite_eq_xor_not (v c : Bool) : (if v = true then c else !c) = xor c (!v) := by
  cases v <;> cases c <;> rfl

/-- The verdict convention on a one-bit output: `[b] = [true]` iff `b`. -/
theorem decide_singleton_eq_true (b : Bool) : decide ([b] = [true]) = b := by
  cases b <;> rfl

/-- **The prediction experiment of the predictor machine** is the concrete predictor
experiment: over uniform `x` and the coins `c :: ρ`, `A_flip(1^n, ⟨i, enc (f x)⟩) = h x` has the
probability that `(if D(⟨i, ⟨enc (f x), [c]⟩⟩; ρ) then c else ¬c) ⊕ flip = h x`
(`uprob_comp_equiv` along `predCoins`, `tdpPredictor_runAtL`). -/
theorem uprob_tdpPredictor {α : Type*} [Fintype α] (D : NUPPT) (flip : Bool) (n : ℕ)
    (i : List Bool) (f : α → α) (h : α → Bool) (enc : α → List Bool) :
    uprob (fun z : α × (tdpPredictor D flip).Coins n =>
        (tdpPredictor D flip).distinguisherL n (pairEncode i (enc (f z.1))) z.2 = h z.1) =
      uprob (fun z : α × (Bool × D.Coins n) =>
        xor (if D.distinguisherL n (pairEncode i (pairEncode (enc (f z.1)) [z.2.1])) z.2.2
          then z.2.1 else !z.2.1) flip = h z.1) := by
  rw [← uprob_comp_equiv ((Equiv.refl α).prodCongr (predCoins D flip n))]
  congr 1
  funext z
  obtain ⟨x, c, ρ⟩ := z
  simp only [Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply, NUPPT.distinguisherL_eq,
    NUPPT.runAt_eq, ofFn_predCoins, tdpPredictor_runAtL, decide_singleton_eq_true, ite_eq_xor_not]

/-! ## Averages -/

/-- The average of `1/2 + (a − b)/2` is `1/2 + (E a − E b)/2` (`OneWay.uexp_add`,
`OneWay.uexp_const_mul`, `HardcoreBit.uexp_sub`). -/
theorem uexp_half_add {κ : Type*} [Fintype κ] [Nonempty κ] (a b : κ → ℝ) :
    uexp (fun r => 1 / 2 + (a r - b r) / 2) = 1 / 2 + (uexp a - uexp b) / 2 := by
  have e : (fun r => 1 / 2 + (a r - b r) / 2) = fun r => 1 / 2 + (1 / 2) * (a r - b r) := by
    funext r; ring
  rw [e, OneWay.uexp_add, OneWay.uexp_const, OneWay.uexp_const_mul, HardcoreBit.uexp_sub]
  ring

/-- The average of `1/2 − (a − b)/2` is `1/2 − (E a − E b)/2`. -/
theorem uexp_half_sub {κ : Type*} [Fintype κ] [Nonempty κ] (a b : κ → ℝ) :
    uexp (fun r => 1 / 2 - (a r - b r) / 2) = 1 / 2 - (uexp a - uexp b) / 2 := by
  have e : (fun r => 1 / 2 - (a r - b r) / 2) = fun r => 1 / 2 + (b r - a r) / 2 := by
    funext r; ring
  rw [e, uexp_half_add]
  ring

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Encryption/PublicKey/Trapdoor.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.HardCoreCollection
import TCSlib.Cryptography.Asymptotic.Sampling
import TCSlib.Cryptography.Encryption.PublicKey.EnsembleSecurity
import TCSlib.Cryptography.Encryption.PublicKey.TrapdoorPredictor
import TCSlib.Cryptography.Pseudorandom.GeneratorFromPermutation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Trapdoor bit encryption

This module builds the trapdoor construction of Algorithm 104.3. The predictor
machine for the security reduction is in `TrapdoorPredictor`. The Goldreich–Levin
bridge supplies the hard-core predicate under the encoding-width premise.

**Deviation.** The single-bit scheme samples `r ← D_i` with the collection's sampler.
It carries `⟨1^n, ⟨i, t⟩⟩` as the secret key, runs the trapdoor inverter on the
all-`true` coin string, and takes the predicate evaluator `H` as explicit data.
Honest sampling is the field `Collection.sample_spec`.

## Main definitions

* `TCSlib.Cryptography.Collection.PredEvaluator` is a polynomial-time evaluator
  of a predicate on a collection.
* `TCSlib.Cryptography.TrapdoorCollection.tdpBitScheme` packages the key generator,
  encryptor and decryptor of Algorithm 104.3.
* `TCSlib.Cryptography.pkPredictor` turns a ciphertext distinguisher into a predictor.

## Main results

* `TCSlib.Cryptography.Collection.HardCore.nonempty_predEvaluator` obtains a predicate
  evaluator by canonical decoding.
* `TCSlib.Cryptography.TrapdoorCollection.tdpBitScheme_singleBitSecure` proves single-bit
  security from one-wayness and a hard-core predicate.
* `TCSlib.Cryptography.TrapdoorCollection.OneWay.exists_glPad_singleBitSecure` supplies
  the predicate and its evaluator through Goldreich–Levin under the width premise `henc`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Algorithm 104.3 and Theorem 104.4.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Theorem 3.2 (the predictor from a distinguisher).
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ## Algorithm 104.3: a single-bit scheme from a trapdoor permutation with a hard-core bit -/

/-- A **polynomial-time evaluator of a predicate on a collection**: `H ⟨i, w⟩ = [h_i(x)]` for
every string `w` that decodes to `x ∈ D_i` (the efficiency clause of `Collection.HardCore`,
stated on every decodable string, such as the outputs of the sampler and of the trapdoor
inverter). Since
decoding is canonical (`Collection.encD_decD`, gate 03b ruling G3-1), every hard-core predicate
has one (`Collection.HardCore.nonempty_predEvaluator`). -/
structure Collection.PredEvaluator (F : Collection) (h : ∀ i, F.D i → Bool) where
  /-- The evaluator. -/
  H : List Bool → List Bool
  /-- The evaluator is polynomial-time. -/
  poly : PolyTimeComputable H
  /-- `H ⟨i, w⟩ = [h_i x]` whenever `w` decodes to `x`. -/
  spec : ∀ i w x, F.decD i w = some x → H (pairEncode i w) = [h i x]

/-- **Every hard-core predicate has a predicate evaluator**: the evaluator of `Collection.HardCore`,
correct on encodings, is correct on every decodable string under canonical decoding
(`Collection.HardCore.evaluator`). -/
theorem Collection.HardCore.nonempty_predEvaluator {F : Collection} {h : ∀ i, F.D i → Bool}
    (hh : F.HardCore h) : Nonempty (F.PredEvaluator h) :=
  let ⟨H, hH, hspec⟩ := hh.evaluator
  ⟨⟨H, hH, hspec⟩⟩

namespace TrapdoorCollection

variable (T : TrapdoorCollection)

/-- The raw key generator of [PS10, Algorithm 104.3] on `⟨⟨⟨1^n, []⟩, []⟩, r⟩`: run `Gen_T(1^n; r) = ⟨i, t⟩`
and output `⟨pk, sk⟩ = ⟨i, ⟨1^n, ⟨i, t⟩⟩⟩`. -/
def tdpGenFun (z : List Bool) : List Bool :=
  pairEncode (pairFstD (T.gen.output (NUPPT.layout (NUPPT.inParam z) [] [] (NUPPT.inCoins z))))
    (pairEncode (NUPPT.inParam z)
      (pairEncode (pairFstD (T.gen.output (NUPPT.layout (NUPPT.inParam z) [] [] (NUPPT.inCoins z))))
        (pairSndD (T.gen.output (NUPPT.layout (NUPPT.inParam z) [] [] (NUPPT.inCoins z))))))

/-- The raw key generator is polynomial-time. -/
theorem tdpGenFun_poly : PolyTimeComputable T.tdpGenFun :=
  have ho : PolyTimeComputable fun z =>
      T.gen.output (NUPPT.layout (NUPPT.inParam z) [] [] (NUPPT.inCoins z)) :=
    T.gen.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout
      NUPPT.polyTimeComputable_inParam (polyTimeComputable_const []) (polyTimeComputable_const [])
      NUPPT.polyTimeComputable_inCoins)
  (polyTimeComputable_pairFstD.comp ho).pairEncode (NUPPT.polyTimeComputable_inParam.pairEncode
    ((polyTimeComputable_pairFstD.comp ho).pairEncode (polyTimeComputable_pairSndD.comp ho)))

/-- The raw encryptor of [PS10, Algorithm 104.3] on `⟨⟨⟨1^n, ⟨i, [m]⟩⟩, []⟩, s⟩`: sample
`w ← Sample(1^n, i; s)` and output `⟨eval ⟨i, w⟩, H ⟨i, w⟩ ⊕ [m]⟩ = ⟨f_i(r), b_i(r) ⊕ m⟩`. -/
def tdpEncFun (H : List Bool → List Bool) (z : List Bool) : List Bool :=
  pairEncode
    (T.eval (pairEncode (pairFstD (NUPPT.inArg z))
      (T.sample.output (NUPPT.layout (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)) [] (NUPPT.inCoins z)))))
    (List.zipWith xor
      (H (pairEncode (pairFstD (NUPPT.inArg z))
        (T.sample.output (NUPPT.layout (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)) [] (NUPPT.inCoins z)))))
      (pairSndD (NUPPT.inArg z)))

/-- The raw encryptor is polynomial-time (`polyTimeComputable_pairXor` for the mask). -/
theorem tdpEncFun_poly {H : List Bool → List Bool} (hH : PolyTimeComputable H) :
    PolyTimeComputable (T.tdpEncFun H) := by
  have hi := polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg
  have hiw := hi.pairEncode (T.sample.polyTimeComputable_output.comp
    (NUPPT.polyTimeComputable_layout NUPPT.polyTimeComputable_inParam hi
      (polyTimeComputable_const []) NUPPT.polyTimeComputable_inCoins))
  have h := (T.eval_poly.comp hiw).pairEncode (polyTimeComputable_pairXor.comp
    ((hH.comp hiw).pairEncode (polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg)))
  convert h using 1
  funext z
  simp only [tdpEncFun, Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]

/-- The raw decryptor of [PS10, Algorithm 104.3] on `⟨⟨u, ⟨i, t⟩⟩, ⟨c₁, c₂⟩⟩`: run the trapdoor
inverter `Inv(u, ⟨t, c₁⟩)` on the all-`true` coin string of length `coins(|u|)` and output
`H ⟨i, Inv(…)⟩ ⊕ c₂ = b_i(f_i^{-1}(c₁)) ⊕ c₂`. -/
def tdpDecFun (H : List Bool → List Bool) (z : List Bool) : List Bool :=
  List.zipWith xor
    (H (pairEncode (pairFstD (pairSndD (pairFstD z)))
      (T.inv.output (NUPPT.layout (pairFstD (pairFstD z))
        (pairEncode (pairSndD (pairSndD (pairFstD z))) (pairFstD (pairSndD z))) []
        (List.replicate (T.inv.coins.eval (pairFstD (pairFstD z)).length) true)))))
    (pairSndD (pairSndD z))

/-- The raw decryptor is polynomial-time (`polyTimeComputable_unaryPoly` for the coin string). -/
theorem tdpDecFun_poly {H : List Bool → List Bool} (hH : PolyTimeComputable H) :
    PolyTimeComputable (T.tdpDecFun H) := by
  have hsk := polyTimeComputable_pairFstD
  have hu := polyTimeComputable_pairFstD.comp hsk
  have hi := polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp hsk)
  have ht := polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp hsk)
  have hc₁ := polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hc₂ := polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have hw := T.inv.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout hu
    (ht.pairEncode hc₁) (polyTimeComputable_const [])
    ((polyTimeComputable_unaryPoly T.inv.coins).comp hu))
  have h := polyTimeComputable_pairXor.comp ((hH.comp (hi.pairEncode hw)).pairEncode hc₂)
  convert h using 1
  funext z
  simp only [tdpDecFun, Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]

/-- The key generator of [PS10, Algorithm 104.3]: `Gen_T`'s coins, output `⟨i, ⟨1^n, ⟨i, t⟩⟩⟩`. -/
noncomputable def tdpGen : NUPPT := NUPPT.ofPolyTimeUniform T.tdpGenFun_poly T.gen.coins

/-- The encryptor of [PS10, Algorithm 104.3] with the predicate evaluator `H`: the sampler's coins. -/
noncomputable def tdpEnc {h : ∀ i, T.D i → Bool} (E : T.toCollection.PredEvaluator h) : NUPPT :=
  NUPPT.ofPolyTimeUniform (T.tdpEncFun_poly E.poly) T.sample.coins

/-- The key generator has the coins of `Gen_T`. -/
theorem coins_tdpGen : T.tdpGen.coins = T.gen.coins := by
  unfold tdpGen
  exact NUPPT.coins_ofPolyTimeUniform _ _

/-- **The key generator runs on the coins of `Gen_T`**: the published equivalence
`T.tdpGen.Coins n ≃ T.gen.Coins n` (`NUPPT.coinsCongr` along `coins_tdpGen`). -/
noncomputable def tdpGen_coinsEquiv (n : ℕ) : T.tdpGen.Coins n ≃ T.gen.Coins n :=
  NUPPT.coinsCongr T.coins_tdpGen n

/-- The coin equivalence keeps the coin string:
`List.ofFn (T.tdpGen_coinsEquiv n r) = List.ofFn r`. -/
theorem tdpGen_coinsEquiv_ofFn (n : ℕ) (r : T.tdpGen.Coins n) :
    List.ofFn (T.tdpGen_coinsEquiv n r) = List.ofFn r :=
  NUPPT.coinsCongr_ofFn T.coins_tdpGen n r

/-- The encryptor has the coins of the sampler. -/
theorem coins_tdpEnc {h : ∀ i, T.D i → Bool} (E : T.toCollection.PredEvaluator h) :
    (T.tdpEnc E).coins = T.sample.coins := by
  unfold tdpEnc
  exact NUPPT.coins_ofPolyTimeUniform _ _

/-- **The encryptor runs on the coins of the sampler**: the published equivalence
`(T.tdpEnc E).Coins n ≃ T.sample.Coins n` (`NUPPT.coinsCongr` along `coins_tdpEnc`). -/
noncomputable def tdpEnc_coinsEquiv {h : ∀ i, T.D i → Bool} (E : T.toCollection.PredEvaluator h)
    (n : ℕ) : (T.tdpEnc E).Coins n ≃ T.sample.Coins n :=
  NUPPT.coinsCongr (T.coins_tdpEnc E) n

/-- The coin equivalence keeps the coin string:
`List.ofFn (T.tdpEnc_coinsEquiv E n s) = List.ofFn s`. -/
theorem tdpEnc_coinsEquiv_ofFn {h : ∀ i, T.D i → Bool} (E : T.toCollection.PredEvaluator h)
    (n : ℕ) (s : (T.tdpEnc E).Coins n) : List.ofFn (T.tdpEnc_coinsEquiv E n s) = List.ofFn s :=
  NUPPT.coinsCongr_ofFn (T.coins_tdpEnc E) n s

/-- Unfolding: `Gen(1^n; r) = ⟨i, ⟨1^n, ⟨i, t⟩⟩⟩` with `⟨i, t⟩ = Gen_T(1^n; φ r)`, the coins read
through `φ = T.tdpGen_coinsEquiv n`. -/
theorem tdpGen_runAt (n : ℕ) (r : T.tdpGen.Coins n) :
    T.tdpGen.runAt n [] r =
      pairEncode (T.index n (T.tdpGen_coinsEquiv n r)) (pairEncode (List.replicate n true)
        (pairEncode (T.index n (T.tdpGen_coinsEquiv n r)) (T.trap n (T.tdpGen_coinsEquiv n r)))) := by
  rw [Collection.index_eq, Collection.trap_eq, T.gen_uniform.runAt_eq, T.tdpGen_coinsEquiv_ofFn,
    NUPPT.runAt_eq]
  unfold tdpGen
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  simp only [tdpGenFun, NUPPT.inParam_eq, NUPPT.inCoins_eq, NUPPT.advInput_eq, pairFstD_pairEncode,
    pairSndD_pairEncode]
  rw [NUPPT.layout_eq]

/-- Unfolding: `Enc(1^n, ⟨i, [b]⟩; s) = ⟨eval ⟨i, w⟩, H ⟨i, w⟩ ⊕ [b]⟩` with
`w = Sample(1^n, i; φ s)`, the coins read through `φ = T.tdpEnc_coinsEquiv E n`. -/
theorem tdpEnc_runAt {h : ∀ i, T.D i → Bool} (E : T.toCollection.PredEvaluator h) (n : ℕ)
    (i : List Bool) (b : Bool) (s : (T.tdpEnc E).Coins n) :
    (T.tdpEnc E).runAt n (pairEncode i [b]) s =
      pairEncode (T.eval (pairEncode i (T.sample.runAt n i (T.tdpEnc_coinsEquiv E n s))))
        (List.zipWith xor (E.H (pairEncode i (T.sample.runAt n i (T.tdpEnc_coinsEquiv E n s))))
          [b]) := by
  rw [T.sample_uniform.runAt_eq, T.tdpEnc_coinsEquiv_ofFn, NUPPT.runAt_eq]
  unfold tdpEnc
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  simp only [tdpEncFun, NUPPT.inParam_eq, NUPPT.inArg_eq, NUPPT.inCoins_eq, NUPPT.advInput_eq,
    pairFstD_pairEncode, pairSndD_pairEncode]
  rw [NUPPT.layout_eq]

/-- Unfolding: `Dec(⟨⟨1^n, ⟨i, t⟩⟩, ⟨c₁, c₂⟩⟩) = H ⟨i, Inv(1^n, ⟨t, c₁⟩; 1^{coins n})⟩ ⊕ c₂`. -/
theorem tdpDecFun_apply (H : List Bool → List Bool) (n : ℕ) (i t c₁ c₂ : List Bool) :
    T.tdpDecFun H (pairEncode (pairEncode (List.replicate n true) (pairEncode i t)) (pairEncode c₁ c₂)) =
      List.zipWith xor (H (pairEncode i (T.inv.runAt n (pairEncode t c₁) fun _ => true))) c₂ := by
  rw [T.inv_uniform.runAt_eq, NUPPT.advInput_eq, List.ofFn_const, NUPPT.coinLen_eq]
  simp only [tdpDecFun, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate,
    NUPPT.layout_eq]

/-- **The single-bit scheme of [PS10, Algorithm 104.3]** from a collection of trapdoor
permutations `T` with a predicate `h` (its hard-core bit), given a polynomial-time evaluator `E`
of `h`: `Gen(1^n) = ⟨i, ⟨1^n, ⟨i, t⟩⟩⟩` with `⟨i, t⟩ ← Gen_T(1^n)`,
`Enc_i(m) = ⟨f_i(r), h_i(r) ⊕ m⟩` for `r ← Sample(1^n, i)`, `Dec(c₁, c₂) = h_i(f_i^{-1}(c₁)) ⊕ c₂`.

**Deviation:** `r ← D_i` through the collection's sampler (the text's `r ← {0,1}^n`); the secret
key carries `1^n` and `i` (the text's `f_i^{-1}` "knows" `i`); the inverter runs on the all-`true`
coin string (`inv_spec` holds for every coin string); `E` is explicit data. Repair (run-3 audit
P3-1): the former hypothesis `hS : T.toCollection.EvalSampled` is dropped, being
`T.toCollection.evalSampled` (the field `Collection.sample_spec`).

**Proof sketch** (of correctness). `tdpGen_runAt`, `tdpEnc_runAt`, `tdpDecFun_apply`;
`T.toCollection.evalSampled` gives `x` with `decD i w = some x` and
`eval ⟨i, w⟩ = f_i x = encD i (perm i x)` (`f_perm`);
`inv_spec` at `perm i x` decodes the inverter's answer to `x` (`Equiv.symm_apply_apply`); `E.spec`
twice gives `H = [h_i x]` on both strings, and `a ⊕ (a ⊕ b) = b`. -/
noncomputable def tdpBitScheme {h : ∀ i, T.D i → Bool} (E : T.toCollection.PredEvaluator h) :
    BitPublicKeyScheme where
  gen := T.tdpGen
  enc := T.tdpEnc E
  dec := T.tdpDecFun E.H
  gen_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  enc_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  dec_poly := T.tdpDecFun_poly E.poly
  correct := by
    intro n b rg' re'
    rw [tdpGen_runAt]
    simp only [pairFstD_pairEncode, pairSndD_pairEncode]
    rw [tdpEnc_runAt, tdpDecFun_apply]
    set rg := T.tdpGen_coinsEquiv n rg'
    set re := T.tdpEnc_coinsEquiv E n re'
    obtain ⟨x, hx, hev⟩ := (Collection.evalSampled_iff _).1 T.toCollection.evalSampled n rg re
    rw [hev, T.f_perm]
    have hinv : T.decD (T.index n rg) (T.inv.runAt n
        (pairEncode (T.trap n rg) (T.encD (T.index n rg) (T.perm (T.index n rg) x))) fun _ => true) =
        some x := by
      rw [T.inv_eq_encD n rg (T.perm _ x) (fun _ => true), Equiv.symm_apply_apply]
      exact T.decD_encD _ x
    rw [E.spec _ _ _ hinv, E.spec _ _ _ hx]
    cases h (T.index n rg) x <;> cases b <;> rfl

end TrapdoorCollection

/-! ## Lem-104.a: from a ciphertext distinguisher to a predictor of the hard-core bit -/

/-- The predictor `A'` of [PS10, Theorem 104.4, proof] built from a distinguisher `D` of
`(f(r), b(r))` versus `(f(r), ¬b(r))` (the encryptions of `0` and `1`): on input `y = f(r)`, draw
`c ← {0,1}` and coins for `D`, output `c` if `D(y, c)` accepts and `1 − c` otherwise (negated when
`flip`); this is `owpPredictor` with the pass-through component removed. -/
def pkPredictor {α ρ : Type*} (D : α × Bool → ρ → Bool) (flip : Bool) : α → Bool × ρ → Bool :=
  fun y c => xor (if D (y, c.1) c.2 then c.1 else !c.1) flip

/-- The predictor is `owpPredictor` on `α × Unit`. -/
private theorem predProb_pkPredictor_eq {α ρ : Type*} [Fintype α] [Fintype ρ] (f : α ≃ α)
    (B : α → Bool) (D : α × Bool → ρ → Bool) (flip : Bool) :
    predProb f B (pkPredictor D flip) =
      predProb (owpPair (β := Unit) f) (fun w => B w.1)
        (owpPredictor (fun v : α × Unit × Bool => fun r => D (v.1, v.2.2) r) flip) := by
  simp only [predProb_def]
  exact uprob_eq_of_equiv ((Equiv.prodPUnit α).symm.prodCongr (Equiv.refl _)) fun _ => Iff.rfl

/-- `acceptProb` of the generator `owpGen` on `α × Unit` is that of `(f(x), B(x))`. -/
private theorem acceptProb_owpGen_unit {α ρ : Type*} [Fintype α] [Fintype ρ] (f : α ≃ α)
    (B : α → Bool) (D : α × Bool → ρ → Bool) :
    acceptProb (owpGen (β := Unit) f fun w => B w.1) (fun v : α × Unit × Bool => fun r => D (v.1, v.2.2) r) =
      acceptProb (fun x => (f x, B x)) D := by
  simp only [acceptProb_def]
  exact uprob_eq_of_equiv ((Equiv.prodPUnit α).prodCongr (Equiv.refl _)) fun _ => Iff.rfl

/-- `acceptProb` of `owpGenNot` on `α × Unit` is that of `(f(x), ¬B(x))`. -/
private theorem acceptProb_owpGenNot_unit {α ρ : Type*} [Fintype α] [Fintype ρ] (f : α ≃ α)
    (B : α → Bool) (D : α × Bool → ρ → Bool) :
    acceptProb (owpGenNot (β := Unit) f fun w => B w.1) (fun v : α × Unit × Bool => fun r => D (v.1, v.2.2) r) =
      acceptProb (fun x => (f x, !B x)) D := by
  simp only [acceptProb_def]
  exact uprob_eq_of_equiv ((Equiv.prodPUnit α).prodCongr (Equiv.refl _)) fun _ => Iff.rfl

/-- **The predictor `pkPredictor D false` predicts `B` from `f(x)` with probability exactly
`1/2 + (Pr[D(f(x), B(x)) = 1] − Pr[D(f(x), ¬B(x)) = 1]) / 2`** (Lem-104.a, signed form; the
identity behind [PS10, Theorem 104.4, proof] and [Gar26, Theorem 3.2]). The sign is uniform over
the index in the collection setting, so the forms with a fixed `flip` average over `Gen`'s coins.

**Proof sketch.** `predProb_owpPredictor_false` on `α × Unit` (`predProb_pkPredictor_eq`,
`acceptProb_owpGen_unit`, `acceptProb_owpGenNot_unit`). -/
theorem predProb_pkPredictor_false {α ρ : Type*} [Fintype α] [Fintype ρ] [Nonempty α] [Nonempty ρ]
    (f : α ≃ α) (B : α → Bool) (D : α × Bool → ρ → Bool) :
    predProb f B (pkPredictor D false) =
      1 / 2 + (acceptProb (fun x => (f x, B x)) D - acceptProb (fun x => (f x, !B x)) D) / 2 := by
  rw [predProb_pkPredictor_eq, predProb_owpPredictor_false, acceptProb_owpGen_unit,
    acceptProb_owpGenNot_unit]

/-- **The flipped predictor `pkPredictor D true` predicts `B` with probability exactly
`1/2 − (Pr[D(f(x), B(x)) = 1] − Pr[D(f(x), ¬B(x)) = 1]) / 2`** (Lem-104.a, the other sign). -/
theorem predProb_pkPredictor_true {α ρ : Type*} [Fintype α] [Fintype ρ] [Nonempty α] [Nonempty ρ]
    (f : α ≃ α) (B : α → Bool) (D : α × Bool → ρ → Bool) :
    predProb f B (pkPredictor D true) =
      1 / 2 - (acceptProb (fun x => (f x, B x)) D - acceptProb (fun x => (f x, !B x)) D) / 2 := by
  rw [predProb_pkPredictor_eq, predProb_owpPredictor_true, acceptProb_owpGen_unit,
    acceptProb_owpGenNot_unit]

/-- **Lem-104.a**: a distinguisher `D` of `(f(r), b(r))` versus `(f(r), ¬b(r))` with advantage `ε`
yields, for one choice of `flip`, a predictor of `b` from `f(r)` with success exactly `1/2 + ε/2`
([PS10, Theorem 104.4, proof: "we can now use `A` to construct a machine `A'` that predicts the
hard-core predicate"]; [Gar26, Theorem 3.2]). -/
theorem exists_pkPredictor {α ρ : Type*} [Fintype α] [Fintype ρ] [Nonempty α] [Nonempty ρ]
    (f : α ≃ α) (B : α → Bool) (D : α × Bool → ρ → Bool) :
    ∃ flip : Bool, predProb f B (pkPredictor D flip) =
      1 / 2 + distAdv (fun x => (f x, B x)) (fun x => (f x, !B x)) D / 2 := by
  simp only [distAdv_def]
  rcases le_total 0 (acceptProb (fun x => (f x, B x)) D - acceptProb (fun x => (f x, !B x)) D) with
    h | h
  · exact ⟨false, by rw [predProb_pkPredictor_false, abs_of_nonneg h]⟩
  · exact ⟨true, by rw [predProb_pkPredictor_true, abs_of_nonpos h]; ring⟩

/-! ## Theorem 104.4 -/

/-- The sampled element of `D_i` behind the honest ciphertext: the decoding of
`Sample(1^n, i; s)` (always `some`, by `Collection.sample_spec`), with the default as fallback. -/
private def tdpSampled (T : TrapdoorCollection) (n : ℕ) (r : T.gen.Coins n) (s : T.sample.Coins n) :
    T.D (T.index n r) :=
  (T.decD (T.index n r) (T.sample.runAt n (T.index n r) s)).getD default

/-- **The honest ciphertext of Algorithm 104.3** is `⟨i, ⟨f_i(x), [h_i(x) ⊕ b]⟩⟩` for the sampled
element `x` (`tdpGen_runAt`, `tdpEnc_runAt`, `Collection.evalSampled`, `E.spec`, `f_perm`). -/
private theorem tdpBitScheme_pkEncDist (T : TrapdoorCollection) {h : ∀ i, T.D i → Bool}
    (E : T.toCollection.PredEvaluator h) (n : ℕ) (b : Bool) (r₀ : T.tdpGen.Coins n)
    (s₀ : (T.tdpEnc E).Coins n) :
    (T.tdpBitScheme E).pkEncDist n b (r₀, s₀) =
      pairEncode (T.index n (T.tdpGen_coinsEquiv n r₀))
        (pairEncode (T.encD _ (T.perm _ (tdpSampled T n (T.tdpGen_coinsEquiv n r₀)
          (T.tdpEnc_coinsEquiv E n s₀))))
        [xor (h _ (tdpSampled T n (T.tdpGen_coinsEquiv n r₀) (T.tdpEnc_coinsEquiv E n s₀))) b]) := by
  rw [BitPublicKeyScheme.pkEncDist_eq]
  show pairEncode (pairFstD (T.tdpGen.runAt n [] r₀))
      ((T.tdpEnc E).runAt n (pairEncode (pairFstD (T.tdpGen.runAt n [] r₀)) [b]) s₀) = _
  rw [TrapdoorCollection.tdpGen_runAt]
  simp only [pairFstD_pairEncode]
  set r := T.tdpGen_coinsEquiv n r₀
  set s := T.tdpEnc_coinsEquiv E n s₀
  obtain ⟨x, hx, hev⟩ := (Collection.evalSampled_iff _).1 T.toCollection.evalSampled n r s
  rw [TrapdoorCollection.tdpEnc_runAt, hev, T.f_perm, E.spec _ _ _ hx]
  simp only [tdpSampled, hx, Option.getD_some]
  rfl

/-- **[PS10, Theorem 104.4]: the scheme of Algorithm 104.3 is a secure single-bit public-key
encryption scheme** when `T` is a collection of one-way trapdoor permutations and `h` is a
hard-core predicate for it.

**Deviation:** the hypothesis includes the hard-core predicate `hHC` (the text's "if trapdoor
permutations exist" omits it; `TrapdoorCollection.OneWay.glPad_hardCore` supplies one from
trapdoor permutations whose generated indices encode elements in exactly `m(n)` bits (`henc`,
which no candidate of the library satisfies as parametrized; see `Collection.glPad`), see
`OneWay.exists_glPad_singleBitSecure`); the proof's "`D`"
in the display after the prediction lemma is the predictor `A`.

**Proof sketch.** Fix a non-uniform PPT `D`; let `μ n` be its advantage between
`pkEncDist n false` and `pkEncDist n true` (by `singleBitSecure_iff` it suffices to bound `μ`).
For `flip ∈ {false, true}` build the machine `A_flip` with coins `const 1 + D.coins` and advice
`D.advice`: on `⟨1^n, ⟨i, y⟩⟩` it reads the coin `c`, runs `D` on `⟨1^n, ⟨i, ⟨y, [c]⟩⟩⟩` with the
remaining coins (`NUPPT.exists_split (const 1)`, `NUPPT.exists_comp` with `pre` the re-pairing),
and outputs `[c ⊕ verdict ⊕ flip]` (`polyTimeComputable_pairEq` for the verdict `= [true]`,
`polyTimeComputable_pairXor`) — the text's `A'` composed with the prediction lemma's sign choice.
`hHC.2 A_flip` gives a negligible `ε_flip` with, for all `n`,
`E_r[Pr_{x, c, ρ}[A_flip(1^n, ⟨i, f_i x⟩) = h_i x]] ≤ 1/2 + ε_flip n`. For a fixed `r` (index
`i = index n r`), the inner probability is `predProb (perm i) (h i) (pkPredictor D_i flip)` with
`D_i (y, c) ρ := D.distinguisherL n ⟨i, ⟨encD i y, [c]⟩⟩ ρ` (`f_perm`, `uprob_comp_equiv` on the
coin split), which `predProb_pkPredictor_false/true` evaluates as
`1/2 ± (Pr[D_i(f_i x, h_i x)] − Pr[D_i(f_i x, ¬h_i x)])/2` over the ideal uniform `x ∈ D_i`.
Averaging over `r` (`OneWay.uexp_add`, `uexp_const`) gives
`1/2 ± (P₀ − P₁)/2 ≤ 1/2 + ε_flip n` where `P_b` is `D`'s acceptance of `⟨i, ⟨f_i x, [h_i x ⊕ b]⟩⟩`
with ideal `x`. By `tdpGen_runAt`/`tdpEnc_runAt` the honest sample `pkEncDist n b` is the same
string with `x` replaced by the sampler's output `decD i (Sample(1^n, i; s))`
(`T.toCollection.evalSampled`, `E.spec`), so `|acceptProb (pkEncDist n b) D − P_b| ≤ δ n` by
`hT.sampleClose = ⟨δ, hδ, hS'⟩` and `StatClose.abs_uprob_sub_le_prod` averaged over `r`
(`OneWay.uexp_mono`). Hence `μ n ≤ 2 (ε_false n + ε_true n) + 2 δ n` for every `n` (the sign of
`P₀ − P₁` selects the flip), negligible by `Negligible.add`, `Negligible.const_mul`,
`Negligible.mono`. (Formally: the machines are `tdpPredictor D flip`, the coin split is
`predCoins`, the per-index identity is `uprob_tdpPredictor`, the honest ciphertext is
`tdpBitScheme_pkEncDist` and the bound is `2 δ(n) + 2 (|ε_false(n)| + |ε_true(n)|)`.) -/
theorem TrapdoorCollection.tdpBitScheme_singleBitSecure (T : TrapdoorCollection)
    {h : ∀ i, T.D i → Bool} (E : T.toCollection.PredEvaluator h)
    (hT : T.OneWay) (hHC : T.toCollection.HardCore h) : (T.tdpBitScheme E).SingleBitSecure := by
  rw [BitPublicKeyScheme.singleBitSecure_iff]
  intro D
  obtain ⟨δ, hδ, hδS⟩ := ((TrapdoorCollection.oneWay_iff T).1 hT).sampleClose
  replace hδS := (Collection.sampleClose_iff _ _).1 hδS
  obtain ⟨εf, hεf, hAf⟩ := ((Collection.hardCore_iff _ _).1 hHC).2 (tdpPredictor D false)
  obtain ⟨εt, hεt, hAt⟩ := ((Collection.hardCore_iff _ _).1 hHC).2 (tdpPredictor D true)
  -- the concrete distinguisher of `(f_i(x), c)` at the index `i = index n r`
  let Di : ∀ n (r : T.gen.Coins n), T.D (T.index n r) × Bool → D.Coins n → Bool :=
    fun n r yc ρ =>
      D.distinguisherL n (pairEncode (T.index n r) (pairEncode (T.encD _ yc.1) [yc.2])) ρ
  -- the honest acceptance probability is within `δ n` of the ideal one
  have hclose : ∀ n (b : Bool),
      |acceptProb ((T.tdpBitScheme E).pkEncDist n b) (D.distinguisherL n) -
        uexp (fun r : T.gen.Coins n =>
          acceptProb (fun x : T.D (T.index n r) => (T.perm _ x, xor (h _ x) b)) (Di n r))| ≤ δ n := by
    intro n b
    have e1 : acceptProb ((T.tdpBitScheme E).pkEncDist n b) (D.distinguisherL n) =
        uexp fun r : T.gen.Coins n => uprob fun w : T.sample.Coins n × D.Coins n =>
          D.distinguisherL n (pairEncode (T.index n r)
            (pairEncode (T.encD _ (T.perm _ (tdpSampled T n r w.1)))
              [xor (h _ (tdpSampled T n r w.1)) b])) w.2 = true := by
      rw [acceptProb_def, ← uprob_comp_equiv ((Equiv.prodAssoc (T.gen.Coins n) (T.sample.Coins n)
        (D.Coins n)).symm.trans (((T.tdpGen_coinsEquiv n).symm.prodCongr
          (T.tdpEnc_coinsEquiv E n).symm).prodCongr (Equiv.refl _))), uprob_prod]
      congr 1
      funext r
      congr 1
      funext w
      obtain ⟨s, ρ⟩ := w
      simp only [Equiv.trans_apply, Equiv.prodAssoc_symm_apply, Equiv.prodCongr_apply,
        Prod.map_apply, Equiv.refl_apply]
      rw [tdpBitScheme_pkEncDist]
      generalize hr' : (T.tdpGen_coinsEquiv n) ((T.tdpGen_coinsEquiv n).symm r) = r'
      generalize hs' : (T.tdpEnc_coinsEquiv E n) ((T.tdpEnc_coinsEquiv E n).symm s) = s'
      rw [Equiv.apply_symm_apply] at hr' hs'
      subst hr' hs'
      rfl
    rw [e1]
    refine abs_uexp_sub_le (hδS n (fun _ => false)).nonneg fun r => ?_
    have hs := (hδS n r).abs_uprob_sub_le_prod
      fun (o : Option (T.D (T.index n r))) (ρ : D.Coins n) =>
        D.distinguisherL n (pairEncode (T.index n r)
          (pairEncode (T.encD _ (T.perm _ (o.getD default))) [xor (h _ (o.getD default)) b])) ρ = true
    simp only [Option.getD_some] at hs
    rw [acceptProb_def]
    exact hs
  -- the prediction experiments of the two predictor machines
  have key : ∀ n (flip : Bool) (r : T.gen.Coins n),
      uprob (fun z : T.D (T.index n r) × (tdpPredictor D flip).Coins n =>
        (tdpPredictor D flip).distinguisherL n (pairEncode (T.index n r) (T.f _ z.1)) z.2 =
          h (T.index n r) z.1) =
      predProb (T.perm (T.index n r)) (h (T.index n r)) (pkPredictor (Di n r) flip) := by
    intro n flip r
    simp only [T.f_perm]
    rw [predProb_def]
    exact uprob_tdpPredictor D flip n (T.index n r) (T.perm _) (h _) (T.encD _)
  have hf : ∀ n, uexp (fun r : T.gen.Coins n =>
      acceptProb (fun x : T.D (T.index n r) => (T.perm _ x, h _ x)) (Di n r)) -
      uexp (fun r : T.gen.Coins n =>
        acceptProb (fun x : T.D (T.index n r) => (T.perm _ x, !h _ x)) (Di n r)) ≤ 2 * εf n := by
    intro n
    have := hAf n
    have e : uexp (fun r : T.gen.Coins n => 1 / 2 +
        (acceptProb (fun x : T.D (T.index n r) => (T.perm _ x, h _ x)) (Di n r) -
          acceptProb (fun x : T.D (T.index n r) => (T.perm _ x, !h _ x)) (Di n r)) / 2) ≤
        1 / 2 + εf n := by
      refine le_of_eq_of_le ?_ this
      congr 1
      funext r
      rw [← predProb_pkPredictor_false (T.perm _) (h _) (Di n r), ← key n false r]
    rw [uexp_half_add] at e
    linarith
  have ht : ∀ n, uexp (fun r : T.gen.Coins n =>
      acceptProb (fun x : T.D (T.index n r) => (T.perm _ x, !h _ x)) (Di n r)) -
      uexp (fun r : T.gen.Coins n =>
        acceptProb (fun x : T.D (T.index n r) => (T.perm _ x, h _ x)) (Di n r)) ≤ 2 * εt n := by
    intro n
    have := hAt n
    have e : uexp (fun r : T.gen.Coins n => 1 / 2 -
        (acceptProb (fun x : T.D (T.index n r) => (T.perm _ x, h _ x)) (Di n r) -
          acceptProb (fun x : T.D (T.index n r) => (T.perm _ x, !h _ x)) (Di n r)) / 2) ≤
        1 / 2 + εt n := by
      refine le_of_eq_of_le ?_ this
      congr 1
      funext r
      rw [← predProb_pkPredictor_true (T.perm _) (h _) (Di n r), ← key n true r]
    rw [uexp_half_sub] at e
    linarith
  -- the negligible bound `2 δ + 2 (|ε_false| + |ε_true|)`
  refine ((hδ.const_mul 2).add (((hεf.mono ⟨0, fun n _ => (abs_abs _).le⟩).add
    (hεt.mono ⟨0, fun n _ => (abs_abs _).le⟩)).const_mul 2)).mono ⟨0, fun n _ => ?_⟩
  have hc0 := hclose n false
  have hc1 := hclose n true
  simp only [Bool.xor_false, Bool.xor_true] at hc0 hc1
  rw [distAdv_def]
  set A₀ := acceptProb ((T.tdpBitScheme E).pkEncDist n false) (D.distinguisherL n) with hA₀
  set A₁ := acceptProb ((T.tdpBitScheme E).pkEncDist n true) (D.distinguisherL n) with hA₁
  set Qa := uexp (fun r : T.gen.Coins n =>
    acceptProb (fun x : T.D (T.index n r) => (T.perm _ x, h _ x)) (Di n r)) with hQa
  set Qb := uexp (fun r : T.gen.Coins n =>
    acceptProb (fun x : T.D (T.index n r) => (T.perm _ x, !h _ x)) (Di n r)) with hQb
  have hmid : |Qa - Qb| ≤ 2 * (|εf n| + |εt n|) := by
    have h1 := hf n
    have h2 := ht n
    have h3 := le_abs_self (εf n)
    have h4 := le_abs_self (εt n)
    have h5 := abs_nonneg (εf n)
    have h6 := abs_nonneg (εt n)
    rw [abs_sub_le_iff]
    constructor <;> linarith
  have hδ0 : 0 ≤ δ n := (hδS n (fun _ => false)).nonneg
  have htri1 := abs_sub_le A₀ Qa A₁
  have htri2 := abs_sub_le Qa Qb A₁
  have hpos : 0 ≤ 2 * δ n + 2 * (|εf n| + |εt n|) := by positivity
  rw [abs_of_nonneg hpos]
  show |(|A₀ - A₁|)| ≤ _
  rw [abs_abs, abs_sub_comm A₁ Qb] at *
  linarith

/-- **Trapdoor permutations give a secure single-bit public-key encryption scheme** — the text's
reading of [PS10, Theorem 104.4] with the hard-core bit supplied by Goldreich–Levin
([PS10, Theorem 87.3], collection form): for a collection of one-way trapdoor permutations `T`
with encoding length `m(n)` at generated indices, the scheme of Algorithm 104.3 for the padded
collection `T.glPad m` with the predicate `⟨x, r⟩` (read through the published domain
equivalence `T.glPad_domEquiv`) is single-bit secure (given its predicate evaluator, which always
exists: `OneWay.exists_glPad_singleBitSecure`). The cost of `henc`: no candidate of the library
satisfies it as parametrized (see `Collection.glPad`). -/
theorem TrapdoorCollection.OneWay.glPad_tdpBitScheme_singleBitSecure {T : TrapdoorCollection}
    (m : PolyExpr)
    (henc : ∀ n (r : T.gen.Coins n) (x : T.D (T.index n r)), (T.encD (T.index n r) x).length = m.eval n)
    (hT : T.OneWay)
    (E : (T.glPad m henc).toCollection.PredEvaluator
      fun i z => T.glBit i (T.glPad_domEquiv m henc i z)) :
    ((T.glPad m henc).tdpBitScheme E).SingleBitSecure :=
  (T.glPad m henc).tdpBitScheme_singleBitSecure E (hT.glPad m henc)
    (hT.glPad_hardCore_domEquiv m henc)

/-- **Trapdoor permutations give a secure single-bit public-key encryption scheme**, without a
supplied evaluator — the text's reading of [PS10, Theorem 104.4] through Goldreich–Levin
([PS10, Theorem 87.3], collection form): for a collection of one-way trapdoor permutations `T`
with encoding length `m(n)` at generated indices (`henc`; see `Collection.glPad` for its cost),
some predicate evaluator `E` of `⟨x, r⟩` (read through `T.glPad_domEquiv`) on `T.glPad m` makes
the scheme of Algorithm 104.3 single-bit secure. The evaluator comes from the hard-core predicate
(`TrapdoorCollection.OneWay.glPad_hardCore_domEquiv`, `Collection.HardCore.nonempty_predEvaluator`,
canonical decoding). -/
theorem TrapdoorCollection.OneWay.exists_glPad_singleBitSecure {T : TrapdoorCollection}
    (m : PolyExpr)
    (henc : ∀ n (r : T.gen.Coins n) (x : T.D (T.index n r)), (T.encD (T.index n r) x).length = m.eval n)
    (hT : T.OneWay) :
    ∃ E : (T.glPad m henc).toCollection.PredEvaluator
        fun i z => T.glBit i (T.glPad_domEquiv m henc i z),
      ((T.glPad m henc).tdpBitScheme E).SingleBitSecure :=
  let ⟨E⟩ := (hT.glPad_hardCore_domEquiv m henc).nonempty_predEvaluator
  ⟨E, hT.glPad_tdpBitScheme_singleBitSecure m henc E⟩

end TCSlib.Cryptography
