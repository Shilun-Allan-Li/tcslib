# gsw-6b-statements · checkpoint 1 review (maintainer, static)

**Verdict: PROCEED WITH NOTES.** 0 blockers, 1 major (G6B-C1-F01, in O2, can be fixed before the final),
2 minors (F02, F03), 6 infos. The checkpoint is a full payload for its claim (lesson G6A-C1-F01 applied): both
series reproduce bit for bit, `src/` and `src-o2/` match the reproduced heads, and the build logs bind every
claimed source. O2 is correct and matches r3's interval form, but one step re-derives a Mathlib lemma (F01). The
four statement files match r3 §H5.9–§H5.12 and the brief, and I found no restatement of an existing lemma. One
fill prerequisite needs a ruling from Seyoon (F03, Q-C1).

## Delivery
- Exchange `1e0647b99de8ee4d11722b5bad862fe40837a2ce` ("stmt gsw-6b: checkpoint 1", 2026-11-17 18:37 UTC, unsigned),
  parent `8b901411b9ff723aeca422319d2f35b106aad88e`; 602 files, all under `inbox/fills/gsw-6b-statements/`
  (no other path is touched). Extracted with `git archive` into an empty scratch directory.
- Heads named in `REPORT.md`: O2 `dd84941f747bca798c2a5a792616f5ead21cfa0b`; stmt `6e01df6c7d5a4f36e92000040d8c83322cb7fef7`
  (Branching, DecryptFormula), `57815173072bf8c145a4bb774797989061fe96f4` (Bootstrap, Circular); base
  `3e51b5f28900db6190f1eb2e6d207d27ee15d541` (tree `b69a66a3…`).
- Contents: `REPORT.md`, `patches/o2/` (1 commit), `patches/stmt/` (2 commits), `src/` (5 files), `src-o2/` (1 file),
  `evidence/` (588 files), `SHA256SUMS`.

## Checks
- **Integrity.** The top-level `SHA256SUMS` (601 entries) and `evidence/SHA256SUMS` (588 entries) verify with rc 0. The
  delivered path sets equal the manifests exactly (nothing missing, nothing extra, no `./`). The issued pack's
  `SHA256SUMS` verifies 25/25.
- **Reproduction.** In a shared scratch clone, the issued `tools/mkbase.sh` prints `STEP1 04947bcf… tree 8eca9617…`
  and `BASE 3e51b5f2… tree b69a66a3…`, the same as the worker's `mkbase.log`. With a sparse checkout at the base
  (`LWE/`, `AdvancedEncryption/Homomorphic/`), `git am` with `COMMITS.tsv`'s committer data and no signing gives
  `dd84941f…`, `6e01df6c…` and `57815173…`. `src-o2/` and all five `src/` files are byte-equal to the heads. The diff
  base..head covers exactly the 4 new GSW files and `BitEncoding.lean` (957 insertions, 0 deletions). The head is
  unsigned (`gpgsig` 0) and every signing column reads `none`.
- **O2.** My own diff against the base shows insertions only: one entry in each of the module docstring's
  *Main definitions* and *Main results*, and the block after `decode_eq` (`:118–178`): `decodeLo` and `decodeHi` with
  `rfl` readers `decodeLo_eq` and `decodeHi_eq`, and `decode_iff_mem_Ico`, proved with no `sorry`. The headers equal
  r3 §H5.8 and the brief character for character, and each declaration has a formula docstring that says "Glue"; the
  theorem also has a proof sketch. `decode_codepoint_add` is not re-proved. Issued `o2check.py`: 0 mismatches for
  `2 ≤ q ≤ 600`. Worker evidence I checked: decls2 5 ADDED / 0 / 0; frozen check 0 violations, with controls; sweep
  18/18 rc 0 with source SHA-256 `ac627bf2…` = delivered; seals A/B/coe-A/coe-B 9 requests each, all PASS; the
  `decodeLo` controls fail sealed exactly once (`:117`, inside the example) and pass positive and unsealed; the axioms
  are standard, with no `sorryAx` in 31 constants. **But see F01.**
- **Statements (4 files).** Headers match r3 §H5.9–§H5.12 (G1–G3, G5–G8, G9–G13, G18, G15), with r3's elided
  hypotheses filled in and the *(fix)* constants settled: `decDepth_le` is `9⌈log₂N⌉ + 2⌈log₂(ℓ+⌈log₂N⌉+3)⌉ + 21`
  (no term linear in ℓ), and `bootNoise_le` is `4^33·N^19·X^4·(2β)`. I checked the derivation of both by hand: they
  follow from F10's `modSumDepth_le` and `4^⌈log₂y⌉ ≤ 4y²`. There are exactly 15 `sorry`, one at each target
  (Branching 3, DecryptFormula 6, Bootstrap 5, Circular 1). The sweep logs show the same counts as `sorry` warnings,
  0 errors in both forms, and source hashes equal to the delivered files. **G11** `encrypts_evalKey` is proved as
  `rw [evalKey_eq]; exact encrypts_encrypt …`, the LE-g45 pattern. **G14** is reader-only (`weakCircularSecure_iff`,
  `Iff.rfl`), and no `distAdv_fheView_le` exists (Q-6B-1 A). **G15** is stated over the evk-dropped projection of
  `fheView`, not over `realView`, as the brief requires. Every definition has its body and an `rfl` reader; `bootGate`
  has three case readers covering every argument list; `fheView` has non-simp `simps`. `Parameters.neZero_columns`
  is proved. The statements check out on paper (G1's `|1−b|+|b| = 1`, G2's step noise, G12's `m·B ≤ bootNoise`
  from `N ≥ 1`, G6's `decodeLo ≤ decodeHi ≤ q`). Every target docstring gives the formula, an `[TAG, loc, anchor]`
  or "Glue", its deviations and a `**Proof sketch.**`. The sketches cite 39 TCSlib and Mathlib names; all exist at
  the base or the Mathlib pin (`args_lt` and `output_lt` are structure fields).
- **Sources.** No `[Gen09]`. Every `pNNN-bNNN` anchor in the four files exists in the ingest of its tag at the base
  (script check over BV14, BV11, AP14, GSW13, Pei16 and Bar89).
- **Duplication.** I searched by name and by conclusion shape in `TCSlib/` at the base and at both tips (main
  `b986b862`, records `bfa1f5a4`) and in the Mathlib pin. No new declaration restates a public lemma. The near
  relatives are a citation (G11 ← `encrypts_encrypt`), a specialization (`decDepth_le` ← admitted F10
  `modSumDepth_le`, `ModSum.lean:179`, with ⌈log₂q⌉ widened to ℓ, so its right side is weaker) and different
  constructions (`fheEval` vs phase-5 `eval` with `homGate`; G12 vs `decrypt_keygen_eval`; `select` vs `Encrypts.nand`).
  There are no private helpers and no cross-file copies. New full names do not clash; the short names `Coins`,
  `PublicKey` and `select` exist only in unrelated namespaces (PPT, Hybrid, Interaction, RSA, Extraction). Two
  issues: one inline re-derivation in O2 (F01) and two fill-time risks in sketches (F02, F03).
- **Hygiene.** No `native_decide`, `admit`, `axiom`, `@[simp]`, `show`, `change` or `delta`. The only `unfold` is of
  the file's own `bootGate` in its three case readers. The `Nat.mul_ne_zero` step reads `Parameters.columns`, a
  reducible abbreviation (notation). Maximum line width is 99. Sizes: Branching 179, DecryptFormula 217, Bootstrap
  351, Circular 146, BitEncoding 206. No micro sign.
- **Evidence recount.** The bootstrap built 288/288 rc 0 with 99 `sorry` in 17 modules, as expected. Admissions at
  the O2 head are 289 in 55 and byte-equal to `base-sorries.txt`. Build logs: the 22 sweep modules at `57815173` are
  rc 0. Seal summary as above.

## Findings

| # | Severity | Finding | Disposition |
|---|---|---|---|
| G6B-C1-F01 | **major** (re-derivation; GF-F01, G48-01) | `decode_iff_mem_Ico` (`src-o2/…/BitEncoding.lean:156–162`) proves the inline helper `habs : y.valMinAbs.natAbs = if y.val ≤ q/2 then y.val else q − y.val` by `rw [ZMod.valMinAbs_def_pos]; split_ifs <;> omega`. This is Mathlib's `ZMod.valMinAbs_natAbs_eq_min` (`Mathlib/Data/ZMod/ValMinAbs.lean:160`, `a.valMinAbs.natAbs = min a.val (n − a.val)`, proved by `rw [valMinAbs_def_pos]; omega`), written in `if` form. The brief's *No re-derivation* rule grades it a major. REPORT §3's lemma list and the worker's duplication search miss it. | **Worker fixes before the final.** Delete `habs` and rewrite both distances with `ZMod.valMinAbs_natAbs_eq_min` (`omega` handles `min`); update the sketch. Rerun O2's checks (decls2, frozen, sweep, seals, controls, axioms) and rebase the stmt series on the new O2 head. |
| G6B-C1-F02 | minor (sketch; fill-time GF-F01 risk) | G15's sketch (`Circular.lean:133–135`) describes the marginalization step without naming a lemma: "a sampler that ignores an independent uniform coordinate has the same acceptance probability (`acceptProb_def`, `uprob` over a product with a constant factor)". That fact is public as `uprob_fst` (`Foundations/Probability.lean:175`) and `uprob_snd` (`Pseudorandom/Functions/LazySampling.lean:70`). | **Worker:** name `uprob_fst` (after `acceptProb_def` and `acceptProb_comp_equiv`, `Foundations/Experiments.lean:107`) in the sketch and list it in *Overlap and reuse*. |
| G6B-C1-F03 | minor (fill prerequisite; GF-F02 pattern) | G6's sketch (`DecryptFormula.lean:158–160`) needs `c_last − ⟨s, c_init⟩ = ⟨t, decryptColumn P C⟩` for `t = (−s, 1)`. At the base this is only step 1 (`hsplit`) of the **private** `decrypt_eq_decode_errorSum` (`GSW/Scheme.lean:213–231`). Rebuilding it in the U13 fill would copy private material across files, which Codex flagged as GF-F02. It is not a public lemma, so the statement surface is fine as delivered. | **Seyoon: Q-C1.** Under A, the worker lists it in the reader census as MISSING, with the proposed public lemma, beside `hybridPlant`. |
| G6B-C1-F04 | info | The checkpoint's admission scan (`admissions/graph/cp1`) reports 289, the same as the base, because the four new modules are not reached from the root until the facades import them (38 unreached modules against 34). The 15 new admissions show up only in the sweep logs and my grep. | Final: the check-4 comparison must cover the new modules (root reach through the facades, or the sweep plus the syntactic scan), with 23–26 names in the 8 GSW files. |
| G6B-C1-F05 | info (size watch) | `Bootstrap.lean` has 351 statement lines. With r3 §H7's U14 estimate (280–440 fill lines) it would fill to about 630–790: under the 1,000 cap, over the 600 target. The other three files project to 330–550. | Check in the final review. |
| G6B-C1-F06 | info (process) | (a) The lead stopped its own stray `git clone` with `pkill -f` instead of by its recorded PID (handoff rule 4), and disclosed it. (b) The split differs from the suggested one: the lead wrote every statement, and the sub-agents (`seal`, `probe`) only verify; this is recorded as the brief allows. (c) `axioms-summary.txt` and the lint lines describe the undelivered final-head files (24 targets traced, so G17 is presumably split), and I cannot verify them here. | Record only; (c) is verified at the final. |
| G6B-C1-F07 | info (freshness) | The records tip has moved to `bfa1f5a4` (#347 and #355 merged; 23 Lean files, none on a 6b path; `Asymptotic/Adversary.lean` gains declarations). `git merge-tree` of the tip with `57815173` is clean, and none of the 68 new names is declared at the tip. | Stay on the base (brief); the maintainer replays at landing. |
| G6B-C1-F08 | info (nit) | The type-level readers `PublicKey_eq`, `Secret_eq`, `Coins_eq`, `KeySeed_eq`, `FheView_eq` and `Seeds_eq` follow phase 5's `Ciphertext_eq` precedent. However, `FheView_eq` (type) and `fheView_eq` (sampler) differ only in case. | Optional: keep, or mention the pair in the docstrings; no action needed. |
| G6B-C1-F09 | info | REPORT defers the row map, *Statement changes against r3*, *Overlap and reuse*, the census and the probes to the final, which the checkpoint definition allows. No questions or scope requests from the worker. | Final. |

## For the worker (maintainer relays)

> Checkpoint 1 reviewed: PROCEED WITH NOTES. Reproduction, integrity, the build bindings and the four statement
> files are in order. Please fix three points before the final:
> 1. **O2 (major, G6B-C1-F01).** In `decode_iff_mem_Ico`, `habs` re-proves Mathlib's `ZMod.valMinAbs_natAbs_eq_min`
>    (`Mathlib/Data/ZMod/ValMinAbs.lean:160`, `a.valMinAbs.natAbs = min a.val (n - a.val)`) in `if` form. Delete
>    `habs`, rewrite with `ZMod.valMinAbs_natAbs_eq_min` (`omega` handles `min`), and update the proof sketch. Rerun
>    O2's evidence (decls2, frozen check, sweep, seals and controls, axioms), rebase `stmt/gsw-6b` on the new O2 head,
>    and list the lemma in *Overlap and reuse*.
> 2. **G15 sketch (G6B-C1-F02).** Name the marginalization lemma, `uprob_fst` (`Foundations/Probability.lean:175`),
>    after `acceptProb_def`/`acceptProb_comp_equiv`, instead of "`uprob` over a product with a constant factor".
> 3. **G6 prerequisite (G6B-C1-F03).** The step `c_last − ⟨s, c_init⟩ = ⟨secretVector P s, decryptColumn P C⟩` exists
>    only inside the private `decrypt_eq_decode_errorSum` (`GSW/Scheme.lean:213`). Do not restate it in a 6b file.
>    In the reader census, list it as MISSING with a proposed one-line public lemma in `Scheme.lean` (for example
>    `decrypt_eq_decode_dotProduct : decrypt P s C = decode P.lwe (secretVector P s ⬝ᵥ decryptColumn P C)`), beside
>    `hybridPlant`, and point G6's sketch at it. (Pending Seyoon's Q-C1; if he rules otherwise, I will tell you.)
> Also at the final: the admissions comparison must reach the new modules (G6B-C1-F04).

## Questions for Seyoon
- **Q-C1 (G6B-C1-F03): the decryption-residual step behind G6.**
  - **A (rec.)** Treat it as a fill prerequisite, like `hybridPlant`'s reader: an owner-side one-line public lemma in
    `GSW/Scheme.lean` (`decrypt_eq_decode_dotProduct`, promoted from step 1 of the private
    `decrypt_eq_decode_errorSum`, which then uses it), landed with the other owner-side readers before the U13 fill.
    The 6b statements stay unchanged.
  - **B** Let the U13 fill re-derive the step inline in `decryptFormula_eval` (about 7 lines) and disclose it in
    *Overlap and reuse*. This risks a GF-F02 or G48-01 finding at the fills gate.
  - **C** Approve a scope request now, so that this job adds the public lemma to `Scheme.lean` (a frozen-file edit)
    in the statement series.
