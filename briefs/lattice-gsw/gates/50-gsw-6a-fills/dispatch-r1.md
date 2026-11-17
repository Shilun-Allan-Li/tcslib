# Dispatch · Gate 50 round 1 (GSW 6a fills: #366 with LE-g50, and #368)

The Codex pack is staged on the exchange at
[`b14712e545ce9a6e08d0070ef134358cc5c8d952`](https://github.com/Shilun-Allan-Li/tcslib/tree/b14712e545ce9a6e08d0070ef134358cc5c8d952/outbox/gates/50-gsw-6a-fills-gate),
folder `outbox/gates/50-gsw-6a-fills-gate/`. Seyoon dispatches.

## Prompt for Codex

```text
You are an external Codex auditor for Gate 50 of the GSW FHE campaign
(phase 6a, the fills gate), round 1, in
https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at b14712e545ce9a6e08d0070ef134358cc5c8d952.
   Read outbox/gates/50-gsw-6a-fills-gate/README.md, pack-r1.md and
   bundle.md. Verify the pack using SHA256SUMS, and verification-r1.zip using
   the SHA256SUMS inside it.
2. Audit two open draft PRs together, using the pack, with campaign records
   b1392d065d0a8f496db8e01b6bdad746bc847ffe
   (cryptography/pass-shelat-ch2-4; the pin files the records copy of this
   pack):
   - #366 (head 597fb736e545706a058cc212243a13f6dadfeceb, tree
     df05652d512a702fa8e379fe3f16258f0e1d20d5; merge base
     555f0fe1b10a20d1be72386a97c6fe7a2f39c204): the proofs of all 98 GSW 6a
     targets frozen at Gate 45 (#359 d154c8830fc8ffc52671b41992e7dbef61e30959).
     In scope: the 15 owner readers of #360 (never gated); #360 addendum 2
     (four promoted helpers); the in-house fills U1/U2, U3, U8, U6 (no
     external review before this gate); the external worker's units U4, U5,
     U7, U9, U10, U11 (7 cherry-picks); the landing edits LE-gf1 to LE-gf4
     (LE-gf2 is a ruled freeze exception to the layerNAND docstring); the two
     merges of the records tip; and LE-g50, the fix of this gate's
     pre-dispatch duplication sweep (items U1-U3). #366 contains #358 and
     #359; their content was audited at Gate 45 and is out of scope.
   - #368 (head 1953898b18a33ab2cd533820c5754a1aacffeb44, base
     55f553715f280be36827ad86a94c93db39ec56c3): the public
     decrypt_eq_decode_dotProduct in GSW/Scheme.lean (promoted from step 1
     of the private decrypt_eq_decode_errorSum, whose proof body changes)
     and the hybridPlant_eq reader in Encryption/PublicKey/EnsembleSecurity.lean.
   Check (pack, questions 1-9):
   - that every proof establishes its frozen statement (decls2 289 ADDED /
     1 REMOVED, the eval_node_nil move / 0 CHANGED), and every helper is
     true as used;
   - frozen-statement fidelity: no header changed; docstring changes only
     in proof sketches, except LE-gf2's ruled sentence;
   - the readers, the promoted public lemmas and #368's lemma and reader
     (homes, binders, docstrings);
   - the landing edits, LE-g50 included;
   - docstrings, sources and sketches;
   - duplication (an undisclosed or unaccepted re-proof of a public lemma,
     including an inline re-derivation of a Mathlib lemma, is a major):
     the phase-1 table and LE-gf1/3/4, the pre-dispatch sweep's U1-U3 and
     LE-g50, and anything the reviews and the sweep missed;
   - Rule 10 (canonical coe-A seals on 22 owners, root coe-A, paired
     controls, unfold scan; #368's seals) and whether that suffices;
   - the evidence binding: phase 2 on snapshot #6, the re-replay on #7 at
     93ae671e, LE-g50 on #8 at 597fb736, and #368's replays on #7 and on #8
     (at its merge with the tip, tree ab098201): does each bind to the
     commit or merge claimed?
   - whether anything is undisclosed (pack, known slips), and grade the
     review findings GF-F01 to GF-F09 and the sweep items U1-U3.
   Out of scope: #358/#359 content (Gate 45), the 6b statements (Gate 46),
   cleanup Stage 1 and #365. Snapshot adoption and the merge order of #366
   and #368 are maintainer merge conditions, not audit items.
3. Return gate50-gsw-6a-fills-findings.md as Markdown in this chat, with
   findings numbered G50-01, G50-02, ..., counts by severity, and a verdict
   per PR (#366, #368) and overall: CLEAR (zero blockers and zero majors)
   or HOLD. If you need multiple evidence files, return a ZIP containing
   that Markdown and evidence.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```

## State at staging

- **Records pin:** `b1392d065d0a8f496db8e01b6bdad746bc847ffe`. It is the signed commit that files this directory (`pack-r1.md`, the diffs, the PR
  descriptions, `source-head-r1.json`, both ZIPs and `SHA256SUMS-r1`) on the records tip
  `f19b8056488fb01214d00915064669dda7e65cc2`, and it is pushed to `cryptography/pass-shelat-ch2-4`. This file was filled
  with the pin and the exchange hash in a later small commit; `SHA256SUMS-r1` does not cover it.
- **Exchange:** `b14712e545ce9a6e08d0070ef134358cc5c8d952`. It is one SSH-signed commit on the exchange tip `f921560204530a9488f6ff955d884ae51d0bc6ba ("Deliver completed RAM word-size fill")`, adding only
  `outbox/gates/50-gsw-6a-fills-gate/`, and it is pushed to `exchange/pass-shelat-ch5-8` as a fast-forward.
  - `SHA256SUMS` (`19034e6075ede7758a4185f0f5e68490fe589bc0d9c30038fce44ee01f37226f`) verifies 16/16 from a fresh `git archive` of the commit.
  - `verification-r1.zip` (`488dbc0997f5bf8ac4ea75716875e46f71ec643c9683b2bcfc953d41a6ad51e9`) verifies 89/89 against its
    own `SHA256SUMS` from a fresh extract.
  - Every section of `bundle.md` was checked equal to its source.
- **PRs at staging:**
  - #366 is a draft at `597fb736` (REST `base.sha` `555f0fe1`), updated 2026-11-17T22:27:01Z.
  - #368 is a draft at `1953898b` (REST `base.sha` `55f55371`), updated 2026-11-17T19:40:27Z.
  - The descriptions in the pack are the bodies read then.
- **Pre-dispatch sweep:**
  - First run (2026-11-17): it stopped staging on three unledgered items (U1-U3), all in the maintainer's code. U1/U2 had
    been noted by the phase-1 review but never filed. Seyoon ruled fix now; LE-g50 (`597fb736`) is the fix.
  - Re-run at staging over the LE-g50 delta: nothing new and unledgered (`checks/dup-sweep.txt`). Notes only:
    `depth_neg`/`maxFanin_neg` (equality form) and TreeDAG's private `maxDepth_map`/`maxFaninL_map`.
- **No Lean, no `lake`** was run for this staging. The pack reuses the recorded evidence.

**Ready to dispatch.**
