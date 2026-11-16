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
