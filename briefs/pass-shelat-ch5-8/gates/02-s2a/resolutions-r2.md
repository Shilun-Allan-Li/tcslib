# Gate 02 (S2a, #185): round 2 resolutions. The gate is closed.

- **Round 2:** findings `gate02-s2a-r2-findings.md`, verbatim, SHA-256
  `104fc2f4f4242990b28885d104764a265e838b5b1e9259007bd3306615f3c038`; head
  `586510c1416afa21881b9a42b5a8d0578c9bd749`. The resolution verdicts are 9 fixed, 4 recorded and
  2 not resolved (both minors). The new findings are **0 blockers, 0 majors, 4 minors and
  2 notes**.
- **The gate closes at 0 blockers and 0 majors** (2026-11-05). The open minors and notes are
  swept in the closing commit below.
- **Review:** `review-r2/subagent-review.md` finds all six new findings true, at the auditor's
  severities. Of the fifteen resolution verdicts, 13 are true and 2 partly true (#8, M2). Its
  exact-rational model of the executor is `review-r2/scripts/model.py.txt`. It corrects M2's
  reason: [PS10] does state the guessing identity, as Lemma 73.8 (book p. 73), which the
  maintainer checked against the source text. It adds four small misses, folded in below.
- **The closing commit:** `a120c71567cda016ab1b8e0d35f8b99eca0082dc` on #185's branch. The branch
  then merged the current ch. 2–4 base (with `main`), giving the head
  `cdf78da1acc2f5814147b358dec9bf5325999d52`.
- **Verified at `cdf78da1`** (`evidence-close/`):
  - a clean replay of the 9-module closure: 9/9 pass, 0 errors, 0 warnings;
  - `#print axioms`: all 75 public theorems use only `propext`, `Classical.choice` and
    `Quot.sound` (the private helper is covered transitively);
  - both lints: 0 findings, and no line over 100 characters;
  - the name screen on the merged tree: no Games name declared twice, and no relative-name clash
    with `TCSlib.Cryptography`, `Complexity`, `TCSlib.InformationTheory` or `Turing`.

| # | Severity | Resolution |
|---|---|---|
| R1-#8 | minor | **Fixed.** [Sho04] is pinned to the revision of 18 January 2006, §1.1, Lemma 1 (the difference lemma), at `Hopping.lean`'s reference block and `abs_prob_sub_le_of_agree`. The location is the external auditor's direct reading of the author-hosted PDF. The review sub-agent could not reach `www.shoup.net` from this session, so it is not re-verified here. `identical_until_bad` no longer cites [Sho04]. [BR06] names its full version (ePrint 2004/331) and the named result, "the fundamental lemma", without a lemma number, which the auditor could not retrieve directly. |
| R1-M2 | minor | **Fixed.** `guessGame`, `accept_guessGame` and `guessAdv_eq_half_advantage` are tagged [PS10, Lemma 73.8] (the prediction lemma) and its proof. The docstring states the deviations (exact, for whole games, with the absolute value), says that Def 168.1 is in distinguishing form, and names the concrete counterpart `predict_eq`, recorded as DL-5 in the duplication ledger. |
| 1 | minor | **Fixed.** `Protocols.lean`'s module text and `exec` docstring describe a coroutine model that contains D8's and is broader in two respects (early returns; a separate return value). Agreement with D8 is claimed only for embedded strategies, through B4. The facade is updated to match. |
| 2 | minor | **Fixed.** Observations are traces: received messages and executed draws. Full [PS10] views come only from parties that sample their whole tape first. The `execT` tag says so. B4 will use that convention. |
| 3 | minor | **Fixed.** The `exec_zero` docstring covers both branches, and `@[simp]` is restored (the review found it dropped since round 1). |
| 4 | minor | **Fixed.** `exists_advantage_hybrid_gap` counts `n` hops (`n + 1` games, the review's addition) and discloses that it is sharper than the source's `ε/m` form. The module text says "for `n` hops". |
| 5 | note | **Scheduled with B4 (S2b).** The three trace invariants of `execT` hold: the review proved them by induction on paper, and its model found no violation in 13,336 outcomes. Stating them needs `AllOutputs` to move from `Hopping.lean` down to `OracleComp.lean`; B4 needs them anyway. |
| 6 | note | **Recorded.** "All 75 theorems" in pack-r2's attestation means the 75 public theorems; the private helper `expect_ite_one_split` is covered transitively. The pack is shipped, so this is pack erratum E4. |
| Review: design note | note | **Fixed.** `design/S2-game-framework.md`'s synchronization paragraph now uses the finding 1–2 wording and the ruling that strategies define interaction. Its coordination section is marked superseded. |
| Review: [Sho04] in `Advantage.lean` | note | **Fixed.** The unused reference is removed. |

**#185 is clear to merge.**
