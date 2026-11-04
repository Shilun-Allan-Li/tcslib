# Gate 01 (Pass–shelat ch. 5–8, prong zero, PR #183): resolutions

**Round 1 (the only round):** findings `gate01-p0-findings.md`, verbatim,
SHA-256 `b2b2dcc8d3ef4c24a2ea72c114e19856c47346c7b7224eab6229a2c5dbace0dc`.
- Audited head: `789cf450527ff6b8c779161e555f04093080b88d`.
- Counts: **0 blockers, 0 majors, 7 minors, 3 notes.**
- Review: a review sub-agent checked every finding against the code and the PDF independently
  (`review/subagent-review.md`). It found 8 findings true and 2 partly true, none false, and moved
  #5 from minor to note. It also found 3 minor items the auditor missed (M1–M3) and one cosmetic
  item (M4). The maintainer spot-checked the source claims against the PDF text: §8.3.3 is a bare
  heading; Def 152.1(3) says both "at most k" and "`|S′| < k`"; Lem 153.2 says "unique degree-n".
- **Closing commit:** `16e2bd02fac1a4656a736b3f0de128e148e60e8c`. Every minor is swept, and the
  optional items too. All edits are docstrings, except six `rfl`/`Iff.rfl` interface lemmas.
- **Re-verified on the closing head** (`evidence-closing/`):
  - the 18-module replay, fresh: 18/18, 0 errors, 0 warnings, 0 sorries;
  - 31 axiom prints, all exactly `[propext, Classical.choice, Quot.sound]`;
  - `SecretSharing/Defs.lean` and `Shamir.lean`: code byte-identical to `main` once comments are
    stripped (still docstring-only, as ruled);
  - lint: 0 findings on the new files; the 8 baseline findings from `main` are unchanged;
  - no line over 100 characters.
- The closing commit was not re-audited externally. Its text is the review's proposed snippets,
  applied verbatim, with the checks above.

## Per finding

| # | Auditor | Review | Resolution |
|---|---|---|---|
| 1 | minor: wrong [Vad12] numbers; [PS10] §8.3.3 described as stating the LHL | true ([PS10] part verified; [Vad12] numbers unverifiable here, host blocked) | **Fixed.** [Vad12] pointers made section-level (`§6.1`, "Ch. 6, strong extractors", `Thm 6.18` kept); §8.3.3 described as a bare heading in `IsStrongExtractor` and `isStrongExtractor_of_isUniversal`. Exact [Vad12] numbers can be restored after checking the published PDF (backlog). |
| 2 | minor: `IsFlatSource`'s `k : ℕ` undeclared | true | **Fixed:** the deviation note covers the natural-number `k` and points to `flat s` for other support sizes. |
| 3 | minor: threshold `Correct` = Def 152.1(2) omits locality | true | **Fixed** (docstring): "together with `LocalReconstruct`". |
| 4 | minor: Shamir comparison needs `k ≥ 1`; "degree"; Lem 153.2's "degree n" | true (only `1 ≤ k` needed) | **Fixed** (docstring): `1 ≤ k`, `correct` needs `0 < k`, `localReconstruct` named, "at most `k − 1`", and Lem 153.2's wording noted. |
| 5 | minor: no public equations for six definitions | partly true; **note** (the cited policy rule is not in `policy.md`; campaign rule 10 is the basis) | **Fixed anyway:** `shannonEntropy_eq`, `isFlatSource_iff`, `FinDist.probTrue_eq`, `isExtractor_iff`, `isStrongExtractor_iff`, `mem_seededSources`, all `rfl`/`Iff.rfl`. |
| 6 | minor: three results lack `[Tag, location]` | true; the same holds for `EpsClose.symm`/`trans` | **Fixed** on all five. |
| 7 | minor: signed difference called "advantage" | true | **Fixed.** |
| 8 | note: coin bijections mean equal laws only for finite uniform coins | true | **Fixed** (docstring) with M3. The auditor's proposed coin-law and party-restriction theorems would be code in `Defs.lean`/`Shamir.lean`, outside the docstring-only ruling: **recorded** as future API (backlog). |
| 9 | note: min-entropy's informal minimum needs the infinite-surprise convention | true | **Fixed** (optional phrase added). |
| 10 | note: `StatClose` overlap real, no copied proof established | partly true: the conclusion is outdated | **Recorded.** Pack erratum E1 and ledger DL-1 (accepted by the user) supersede "no copy established": `abs_sum_sub_le_statDist` on the concrete layer's branches duplicates `abs_probTrue_sub_le_statDist`. The sampler-to-`FinDist` bridge stays an integration obligation. |
| M1 | (missed) `IsStrongExtractor` generalizes [Vad12] with no deviation note | minor | **Fixed** (deviation note). |
| M2 | (missed) `isStrongExtractor_of_isUniversal` differs from [HILL99]/[Vad12] with no deviation note | minor | **Fixed** (deviation note). The same omission in `main`'s `leftover_hash` is out of scope (backlog). |
| M3 | (missed) Def 152.1(3)'s inconsistency silently resolved | minor | **Fixed** (parenthetical, docstring). |
| M4 | (missed, cosmetic) `shannonEntropy_uniform`'s generalization undeclared | — | **Fixed.** |

## Pack errata (the pack is not edited)

- **E1** (`pack-errata.md`): attestation 5's "no copy found" was wrong; see #10 and DL-1.
- **E2:** the pack's Known deviations line "`IsStrongExtractor`: … follows [Vad12, Def 6.13]"
  probably cites the wrong item. Secondary sources give Def 6.13 as the ordinary seeded extractor,
  not the strong one; this is unverified, since the published PDF could not be fetched here. The
  code no longer cites an item number.

## Backlog from this gate

1. Restore exact [Vad12] item numbers (statistical difference; strong extractors) after checking
   the published PDF.
2. Future API in `SecretSharing/` (another author's files; needs agreement): a theorem turning a
   coin bijection into equal view laws under finite uniform coins, and a party-restriction
   transport theorem.
3. `main`'s `leftover_hash`: add a deviation note on its hypotheses relative to [HILL99]/[Vad12]
   (another author's file).
4. Name-based duplication screens are not exhaustive: later screens add a statement-level search
   (`exact?` on each new lemma, as the ch. 3–4 workflow prescribes).

## Verdict

The gate **closes**: round 1 reported 0 blockers and 0 majors; every minor is swept in the
closing commit and re-verified on its head; the replay passes on the current head.
