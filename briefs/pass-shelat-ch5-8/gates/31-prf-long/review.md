# prf-long · maintainer delivery review (r1)

**Verdict: ACCEPT WITH LANDING EDITS.** The edits are LE-doc (three formula docstrings) and LE-ws (one blank line).
No undisclosed restatement was found.

## Delivery and landing branch

**Delivery**
- **Source:** Claude worker, ruling B3. Exchange final `8d44fa5b5cdd408b9361364a246697dc294151fb`; checkpoints
  `6941fe67` and `36067085`. Issue base `7b307d62`.
- **Scope:** the PRF machinery at ℓ(n)-bit outputs (D1–D4), added to the owned frozen `FromPRF`/PRF files, with the
  n-bit versions re-derived from it. The unit proves no admitted target, by design.

**Landing branch** `land/pass-shelat-prf-long`
- **Rebase:** onto records tip `dd98360d`, which includes #303, #306–#309, #311 and #312. No conflict.
- **Head:** `fbd37f447596d4207c8d08b7ef7602f57fe95198`, tree `c0609c53b694d1899f8e2b8b6b0f7fd9357dc4cf`.
- **Commits:** `2d4fb3f6` (D1, D2), `ccb51427` (D3), `05deb4d8` (readers), `2205e332` (D4 and the re-derivations),
  `ea50e92c` (LE-doc) and `fbd37f44` (LE-ws).
- **Files:** six, +908/−279.
  - modified: `Asymptotic/Defs.lean`, `FromPRF/Hybrid.lean`, `FromPRF/ReductionMachine.lean` (892 lines) and
    `FromPRF.lean`;
  - new: `FromPRF/MultiMsgOut.lean`;
  - modified: the `PrivateKey.lean` facade, by one import and one Contents bullet.

**Evidence:** `review-evidence.zip`, SHA-256 `0586d82ed786e77bf21aa4263e20bd0f9f2cd62f7adde8c003458d0a2126c4d4`.
- It has 645 entries: the manifest paths plus `SHA256SUMS`. The manifest is `evidence-SHA256SUMS`.
- The duplication and seal-B logs are in `landing/`.

## Checks

**Integrity**
- The manifests verify 1755/1755 and 1742/1742, with exact path sets.
- `git am` reproduces all four worker hashes, but only with the environment's SSH signing turned on (F-03).
- The issue package verifies 7/7, and its sources 434/434.

**Build**
- All 121 modules downstream of the changed modules, plus the 55-module base delta, give rc 0 with 0 errors. This runs
  through root `TCSlib` and both `audits/*/Checks`.
- The whole-tree check covers 1244 modules, and passes.

**Statements**
- **Frozen rule:** an independent `frozencheck.py` compared headers, the prose before each sketch, and whole
  definition bodies. It found 0 differences, and each of its five controls reports exactly one.
- **decls2:** 61 ADDED, 0 CHANGED, 0 REMOVED.
- **Signatures:** all 23 drafted D1–D4 signatures match. The only additions are disclosed extra helpers.

**Axioms**
- All 15 endpoints and all 321 stored constants use only the standard three.
- No type, attribute or axiom changed.

**Rule 10**
- Variant A (the canonical one) passes in every file, both strict and coe. Strict and coe agree.
- Variant B fails only where the base already fails, on `PolyExpr.eval`. The attribution is in
  `landing/seal-B-attribution.txt`.
- Paired controls: 14 per variant, ALL_OK.
- The explicit-unfold scan finds 0 foreign definitions.

**Admissions:** 40 in 19 modules, unchanged, as expected.

**Lint:** 92/101 at the tip and at the head, with no new line.

**Content**
- The n-bit results are literal cases of the `Out` forms.
- **The B1 consumer map is correct.**
  - Use the masks `w_i = 0^{o_i+n} ‖ m_i ‖ 0^…` and the post-map `P : (r,u) ↦ (r, (u.drop o).take (n+ℓ_i))`.
  - `P ∘ prfEncRealOut` is then exactly `sliceEnc`, on the same seed space.
  - The total D4 is uniform in the masks, so `sc-garble` obtains the maximization over slices directly.
- **Gate 27's hand-off is met by an equivalent general API.**
  - D3 has ℓ-bit answers, n-bit queries and keys, an evaluation identity for every oracle, and the coin
    equivalence.
  - The consumer does its post-processing inside `D`.
  - Caveats: the queries are a non-adaptive chain of uniform points, which is enough for the slice proof and for
    `spDecStr_wrongKey`. The advice and query bounds stay inside the existential.

**Overlap with #314:** the trial merge is clean, and neither PR touches the other's files. Whichever lands second
needs an integration rebuild of `Functions/Defs`' downstream.

## Findings

| # | Severity | Finding | Disposition |
|---|---|---|---|
| F-01 | minor, disclosed | `MultiMsg.encodeList_eq_flatMap` (`MultiMsgOut.lean`) is a third copy of the public `encodeList_eq_flatMap` (`Asymptotic/BlockEncryptor.lean`). The others are that public lemma and the frozen private copy in `FromPRF.lean`, which is now unused. A private/public name clash blocks reuse. | Ledger **DL-46**. The worker's promotion request goes to a follow-up: move the lemma to `EnsembleSecurity` and delete both copies. |
| F-02 | minor, disclosed | `histBlockLen` is kept beside `histBlockLenOut`: they are different `PolyExpr` terms, with no `rfl` bridge. `adviceBound` and the private `encodeList_eq_flatMap` are now unused. | Ledger **DL-46**. The unused frozen items go in a later cleanup. |
| F-03 | info | The commit hashes reproduce only with SSH signing on, and the signing is not recorded (same as prf-mac F-05). | Briefs going forward require a signing column in `COMMITS.tsv`, or `commit.gpgsign=false`. |
| F-04 | info | Three new public declarations had no formula docstring. | **Fixed** by LE-doc. |
| F-05 | info | A blank line was lost. | **Fixed** by LE-ws. |
| F-06 | info | Undisclosed near-relatives, not restatements: GGM's `encodeHist_eq_histEnc`, `histEnc_append_single`, `length_histEnc`, and `UniformTableauEmitter.encodeList_eq_flatMap`. | Ledger note, DL-46. |
| F-07 | info | Seal-B failures only on `PolyExpr.eval`, where the base also fails. | None. |
