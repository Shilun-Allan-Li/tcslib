# learning · maintainer delivery review (r1)

**Verdict: ACCEPT WITH LANDING EDITS.** LE-doc is done. The landing edit **LE-reuse** is in progress: it re-proves two
undisclosed restatements (findings 1 and 2) from the published lemmas, by a proof-only change.

## Delivery and landing branch

**Delivery**
- **Source.** Claude worker. Exchange final `365d6639c0a3fbd2550e6ce792c2aee9b927010a`; checkpoints `8318ce34` and `6ebe473c`.
  The issue base is `107f1e8c`.
- **Target.** `Randomness.predictAdv_prfConcept_negligible`, [PS10, Theorem 179.1(b)].
- **Side effect.** Part (c), `not_weakLearnsUnder_prfConcept`, used the standard axioms plus `sorryAx` and now uses the
  standard axioms only. The census confirms it.

**Landing branch** `land/pass-shelat-learning`
- **Base.** Rebased onto records tip `4561c340`, which includes #303 and #306–#309. The rebase had no conflict.
- **Worker commits** (3, author Claude): `876145de`, `331c15f4`, `b4caa53b`.
- **LE-doc** `7f5bdd510c15357ca8e4bc28ca74ec6bcdf211c1` (tree `240da503`). It adds 17 docstring-only formulas. The code is
  identical when the doc comments are blanked.
- **Files.** The owned file `Randomness/Learning.lean`, plus four new helpers, `Learning/{Sample,Distinguisher,Law,Random}.lean`.

**Evidence.** `review-evidence.zip`, SHA-256 `88ab5b78391d33d67990e49e69db5c0360951f5c3e1d60c4ce259667573cc14d`.
- It holds 489 entries: the 488 manifest paths plus `SHA256SUMS`.
- The manifest is in `evidence-SHA256SUMS`.

## Checks

**Integrity.**
- The manifests verify 153/153 and 142/142 after normalizing the `./` prefix.
- `git am` with the `COMMITS.tsv` committer data reproduces every hash.
- The issue package verifies 7/7, and its sources 246/246.

**Build.** 66 modules give rc 0 and 0 errors, counting both diagnostic forms:
- the 51 base-delta modules;
- the unit's 5 modules;
- their downstream, through root `TCSlib` and `audits/pass-shelat/Checks`.

None of #307's modules is in the unit's closure. The whole-tree check covers 1245 modules plus PFR, and passes.

**Statements.**
- decls2 gives 47 ADDED, 0 CHANGED and 0 REMOVED.
- All 9 pre-existing headers are byte-identical.

**Axioms.** All 71 stored constants use only the standard axioms. There is no `@[simp]`, no instance and no abbreviation.

**Rule 10.**
- Seals A and B pass in both variants, at the head and at the base.
- The coe controls are ALL_OK.
- The explicit-unfold scan finds 0 foreign definitions.
- In the strict variant, two reader positives fail. This is a harness artifact of sealing the coercion, which is
  notation by ruling. Every strict negative fails exactly once.

**Admissions.** They go from 20 to 19.

**Lint.** 92/101 at the tip and at the head. Every line is at most 100 characters, and every file is at most 275 lines.

**Content.** The proof follows the book:
- the real game is the distinguisher with `f_k`;
- with a random function, the game is within `m(n)/2^n` of ½, by a bit-flip involution and a union bound;
- negligibility then follows from the PRF advantage.

The edge cases are handled: `n = 0`, `m = 0`, a fresh point equal to an example, and an output other than `[true]`.

## Findings

| # | Severity | Finding | Disposition |
|---|---|---|---|
| 1 | minor | **Undisclosed.** `LearnPRF.uprob_eq_point` is the public `OneWay.uprob_eq_one_div_card`, reversed, with `|X| = 2^n`. The worker also asked to promote it. | **LE-reuse**, proof only. The promotion request is withdrawn. Ledger DL-45. |
| 2 | minor | **Undisclosed inline re-proof.** `hpt`/`hdev` in `abs_gameProb_random_sub_half_le` re-prove `MultiMsg.abs_uexp_sub_le_uprob` (`FromPRF/HybridLemmas`). | **LE-reuse**, proof only, if the import is acyclic and the change modest. Otherwise ledger it. DL-45. |
| 3 | minor | The private `length_blk` re-proves `MultiMsg.length_histBlock`, for the disclosed private copy `blk` of `histBlock`. | Ledger DL-45, with the worker's reader request for `histBlock`. |
| 4 | info | `flip0`/`flip0_flip0` duplicate `flipBit`/`flipBit_flipBit` (BooleanAnalysis) and `flipAt` (DeterministicCC); both of those are outside the crypto closure. There is also a short-name reuse of `flipAt`. | Ledger DL-45. |
| 5 | info | The left side of `foldr_pairEncode_nil` is `Strategy.encodeMsgs`. `relabel`/`relabel_eq` share their short names with `Games.EffFill.relabel` (DL-36 family). | Ledger DL-45. |
| 6 | minor | 17 docstrings had no formula. | **Fixed** by LE-doc. |
| 7 | info | Strict-variant positive controls are a coercion-seal artifact. | Recorded. |
| 8 | info | Disclosed route deviation: `MultiMsg.exists_queryChain_nuppt` is reused, as a call. | None. |
| 9 | info | The manifest paths carry a `./` prefix. | None. |
