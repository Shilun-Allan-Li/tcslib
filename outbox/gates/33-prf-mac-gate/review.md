# prf-mac · maintainer delivery review (r1)

**Verdict: ACCEPT WITH LANDING EDITS.** One finding, F-01, is resolved by Seyoon's ruling: the duplicated lemma is
promoted first, in a separate PR, and prf-mac then re-points to it. The landing branch waits for that PR.

## Delivery and landing branch

**The delivery**
- **Worker and target.** A Claude worker proved `Authentication.prfMAC_secure`, [PS10, Theorem 135.4].
- **Exchange.** The final is at `51ae2c1215554ccda3dde19d8d72908ea74dd339`. Checkpoints were delivered at `f93d8a02` and `22b70519`.
- **Base.** The issue base is `107f1e8c`.

**The landing branch** `land/pass-shelat-prf-mac`
- **Head:** `bd45faecffa420497557dfeba9e2818d7d3cf4a3`, tree `25ad7a637d6c33353df4e463e02e2816e07d2aa2`.
- **Rebase:** it is rebased onto records tip `e7fa2605`. That tip includes #303 and #306–#309. The rebase had no conflict, and the Lean content is unchanged.
- **The worker's 4 commits:** `d8fb2380`, `99929a43`, `0872e5c1` and `fa72acc6` (Rule 10 repair).
- **LE-doc** `bd45faec`: two docstring-only formula fixes, one on `PRFMAC.macHandler`'s `simps` fields and one on the `FnForge` Decidable instance. The code is identical with doc comments blanked.

**Files**
- The owned file `MAC/FromPRF.lean` changes.
- Five helpers are new: `MAC/FromPRF/{Bound,Game,Handler,Random,Reduction}.lean`.
- No other file changes.

**Evidence:** `review-evidence.zip`, SHA-256 `e8038014cc178de78f93f194434f20795b396e1c918fa7d1140e5dd74e49cad5`.
- It has 373 entries, the manifest plus `SHA256SUMS`, and its manifest is `evidence-SHA256SUMS`.
- The overlap searches are in `landing/overlap-review.txt`.

## Checks
- **Integrity**
  - The manifests verify 693/693 and 680/680, with exact paths.
  - The issue package verifies 7/7, and its sources 208/208.
  - `git am` reproduces the 4 worker hashes. This works only with the environment's deterministic SSH commit signature (F-05).
- **Build**
  - 67 modules give rc 0 and 0 errors (both diagnostic forms). They are the 57 changed modules (51 base delta plus the unit's 6) and their downstream, through root `TCSlib` and `audits/pass-shelat/Checks`.
  - The whole-tree check at the head covers 1246 modules: OK.
  - There are no name clashes with #307, #308 or #309.
- **Statements:** decls2 gives 38 ADDED, 0 CHANGED, 0 REMOVED. All headers are byte-identical, the target's included.
- **Axioms:** the target uses only the standard three axioms. So do all 97 stored constants. There is no `@[simp]` and one instance.
- **Rule 10**
  - Seals A and B pass in both the strict and the coe variant: 6/6 at the head, 1/1 at the base.
  - Paired controls: 16 probes, 68 negatives, ALL_OK.
  - The explicit-unfold scan finds 0 foreign definitions.
- **Admissions:** 20 → 18. The two removed are `prfMAC_secure` and `dlHash_crh` (from #307).
- **Lint:** 92/101 at the tip and at the head, with identical lines. Widths are at most 100 characters.
- **Content**
  - The proof gives `Pr[forge] ≤ prfAdv(F_n, D^{q·1+1}) + 2⁻ⁿ` at every `n`.
  - It handles the edge cases: `n = 0`, budget 0, repeated queries, a queried output message, timeouts, and the `+1` final query.
- **Tooling:** the review runner was fixed to count both `error:` and `error(` (G26-N1).

## Findings

| # | Severity | Finding | Disposition |
|---|---|---|---|
| F-01 | major | **Undisclosed duplicate.** The local `hadv` in `Bound.exists_forgeGame_le` re-proves the public `ETTGame.prfAdv_eq_expect` (from #306) line for line. | **Ruling (Seyoon, 2026-11-15): promote it now.** A small PR promotes `prfAdv_eq_expect` to the PRF layer, beside `prfAdv`, and re-derives `ETTGame.prfAdv_eq_expect` from it with a proof-only change that keeps that API. prf-mac then re-points `hadv` to the promoted lemma with a proof-only landing edit. |
| F-02 | minor | **Undisclosed restatement.** `decide_fnForge`'s `hw`, `htake` and `hdrop` restate list readings of `splitBits`. The public relatives are `take_ofFn_castLE`, `CollectionsHelpers.ofFn_drop_take`, and, since #307, `FromDiscreteLog.ofFn_splitBits_fst`/`_snd`. | Erratum; ledger DL-44. |
| F-03 | minor | **Undisclosed nearest relative.** The `blocks`/`macState` encoding and `hits_nil_iff` have an undisclosed nearest relative, `GGMRed.tblEnc`/`lookup` (reused by cca2-ett as `tblW`). This is a different encoding, not a restatement. | Erratum; ledger DL-44. |
| F-04 | note | **Incomplete relative lists.** The rows for `key`/`hkey` and for `accept_forgeGame_eq` are incomplete. The missing relatives are `NUPPT.coinsEquiv_ofPolyTimeUniform(_ofFn)`, `ofFn_arrowCongr_finCongr` and Lamport's deterministic-signer lemmas. | Erratum. |
| F-05 | note | `COMMITS.tsv` hashes reproduce only with the environment's deterministic SSH commit signing. | Future briefs must record the signing or require `commit.gpgsign=false`. |
| F-06 | note | Two pre-existing items, both disclosed: the target's frozen first docstring paragraph has no formula, and the base `prfMAC.correct` has no proof sketch. | None. |
