# Dispatch · Gate 46 round 1 (the GSW 6b gate)

**Do not dispatch yet.** The pre-dispatch duplication sweep has one item, S1, that waits on Seyoon's ruling
(question Q-G46-S1, `dup-sweep.md`). Under option A the pack is re-pinned to #377's new head; under option B the pack's
S1-disposition placeholder is filled in. Separately, the stale [Gen09] disclosure (pack question C3) goes to Seyoon.

**This file postdates the records pin** (lesson G48-02). The records pin is the commit that files this directory. At
the pin, this file holds placeholders for the pin and the exchange commit, and `pack.md` holds one for the pin. The
next records commit fills them in and changes nothing else. `SHA256SUMS` does not cover this file, and the exchange pack
does not contain it.

The Codex pack is staged on the exchange at `<EXCHANGE>`, folder `outbox/gates/46-gsw-6b-gate/`. Seyoon dispatches.

## Prompt for Codex

```text
You are an external Codex auditor for Gate 46 of GSW phase 6 (the 6b gate:
the owner-side PR O2 and the 6b cryptography-layer statements), round 1, in
https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at <EXCHANGE>.
   Read outbox/gates/46-gsw-6b-gate/README.md, pack.md, dup-sweep.md and
   bundle.md. Verify the pack using SHA256SUMS, and verification.zip using
   the SHA256SUMS inside it.
2. Audit two stacked draft PRs, using the pack, with campaign records
   <RECORDS>
   (cryptography/pass-shelat-ch2-4; the pin files the records copy of this
   pack; its Lean equals olean snapshot #10, cf6a2266, with #366 and #368
   merged):
   - PR #376 (O2) at 04ba2446f541c39dd02aefaa97a9eb31dbbda748 (branch
     land/gsw-6b-o2, parent 38123ccbebef878cd25dd2d2761de1b40ba7e421):
     decodeLo, decodeHi and decode_iff_mem_Ico in LWE/BitEncoding.lean
     (P6-Q7), audited as a proof. Insertions only, decls2 5/0/0.
   - PR #377 (statements) at 680be9fa45a9cf5deeb7a59820e8e86aaaa4f068
     (branch land/gsw-6b-statements, base land/gsw-6b-o2 at 04ba2446): the
     6b statements of GSW phase 6 in nine new files: NAND bootstrapping,
     circular security, the leveled scheme with its key hybrid, the ratio
     and the asymptotic statements. 24 admitted targets (23 targets.txt
     rows with G17 split), the proved citations G11 and L1, the reader-only
     G14 and A2 (Q-6B-1 A), every definition and reader, and the landing
     edits LE-6b1..3 (680be9fa; Q-6B-F1 A).
   Check (pack, questions A-I):
   - #376: decode_iff_mem_Ico is true for every q >= 2 and proved;
     decodeLo <= decodeHi <= q;
   - #377: a statement-fidelity audit of all 24 targets against BV14, BV11,
     AP14 (Alperin-Sheriff-Peikert bootstrapping), GSW13, Pei16 and Bar89,
     cited exactly as the issued brief pins them, and against plan section
     r3 (G1-G18, L1-L5, A1-A3) and its Gate 46 checklist: each target
     true, its hypotheses neither vacuous nor contradictory, the edge
     cases, and strong enough for its U12-U19 fill; the noise ledger
     (the selector's 2N*beta, 4^depth, bootNoise, decDepth); the padding
     and the sigma-0 output; the consecutive key chain and the top-down
     hybrid; the per-distinguisher WeakCircularSecure; the A4 hypotheses;
     the definitions and readers;
   - the rulings: W1 (factor 8, pBoot constant 2^70), W2, W3, F1, F2
     (decDepth_le stays admitted), Q-6B-1 and Q-C1;
   - that no frozen file changes beyond the brief's 12 paths (no 6a or
     phase-5 file), and that LE-6b1..3 equal the proposed diff;
   - the 123 citation anchors, the sketches, and the reconstruction
     disclosure against the [Gen09] ingest (question C3);
   - the evidence: recount admissions (216, exactly the 24 targets),
     axioms (sorryAx in exactly the 24 targets), seals (48 probes, 0
     errors), controls and the unfold scan from phase 2's evidence, and
     grade G6B-F10 (LE-6b3's axiom-log effect), G6B-F11 (the delivery's
     stale control payloads) and G6B-F12 (root coe-A not re-run);
   - duplication (an undisclosed or unaccepted restatement or re-derivation
     of a public lemma, including an inline re-derivation of a library
     lemma, is a major): the pre-dispatch sweep's S1 and its disposition,
     the notes N1-N11, and anything the reviews and the sweep missed;
   - whether anything is undisclosed (pack, known slips), and grade the
     review findings G6B-F01 to G6B-F12 and the sweep item S1.
   Out of scope: 6a and #368 (Gates 45 and 50, merged), the 6b fills
   U12-U19, and the [Gen09] citation itself (a docstring-only follow-up).
   The merge order (#376 first) and the snapshot adoption are maintainer
   merge conditions, not audit items.
3. Return gate46-gsw-6b-findings.md as Markdown in this chat, with findings
   numbered G46-01, G46-02, ..., counts by severity per PR, and a verdict
   per PR and overall: CLEAR (zero blockers and zero majors) or HOLD. If
   you need multiple evidence files, return a ZIP containing that Markdown
   and evidence.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```

## State at staging

- **Records pin:** `<RECORDS>`, the commit that files this directory and ledger row DL-61. Its parent is the records tip
  at staging, `dab31951abb5c892dc6279c229e49497ec95de10`, which is `38123ccb` plus 21 records-only commits.
  - **Records copy:** this directory was written on the records checkout and **not committed**. So was ledger row DL-61
    in `briefs/pass-shelat-ch5-8/duplication-ledger.md`. The maintainer commits them with explicit paths.
  - Its `SHA256SUMS` covers the 10 other files. It is regenerated whenever a placeholder in `pack.md` is filled.
- **Exchange:** the local branch `stage/gate46-exchange` in the records checkout's repository, from the sparse worktree
  `$SP/wt-exch-g46`.
  - The staging commit is `4fa8ad888b2ac9be992b42e3971cfe7ae5430a4f`: one SSH-signed commit on the exchange tip
    `5406a958aeda7bc0a887a90e9a0186a7ef2c0222`, adding only `outbox/gates/46-gsw-6b-gate/` (16 files, 9.3 MB). It is
    **not pushed**, and its branch has no upstream.
  - Its `SHA256SUMS` (`e8dddbe3…`) verifies 15/15 from a fresh `git archive`. `bundle.md` has 47 sections, each
    checked equal to its source. `verification.zip` verifies 43/43 against its own `SHA256SUMS` from a fresh extract.
    The 64 entries of `sources.zip` match its README.
  - The commit still carries the records-pin placeholder (in `pack.md`, `README.md`, `RECORDS.txt`, the bundle's pack
    section and the commit message) and the S1-disposition placeholder (in `pack.md`).
  - **Before the push:**
    1. Rule S1, then fill the S1-disposition placeholder (or re-stage under option A).
    2. Commit the records copy, which makes the pin.
    3. Fill the pin in the exchange copy, rebuild `bundle.md` and `SHA256SUMS`, and amend with `-S`. The helper
       `$SP/g46/fill-gate46.sh` does this (steps `s1`, `records`, `exchange`, `dispatch`).
    4. Push: `git push origin stage/gate46-exchange:exchange/pass-shelat-ch5-8`, a fast-forward if the exchange tip has
       not moved; otherwise replay with `git cherry-pick -S`.
  - The exchange pack does not contain `dispatch.md` (convention since Gate 45).
- **PRs at staging:**
  - #376 is a draft at `04ba2446`, REST `base.sha` `1a9a3295`, updated 2026-11-18T06:41:38Z.
  - #377 is a draft at `680be9fa`, base `land/gsw-6b-o2` at `04ba2446`, updated 2026-11-18T06:41:15Z.
  - The descriptions in the pack are the bodies read then.
- **Pre-dispatch sweep:** one item, S1 (`encodeFheView_length`/`encodeLeveledView_length` re-derive the public
  `length_flatten_map_const`, which is in their import closure). It is undisclosed, and the ruling is pending. It is
  recorded today as DL-61 (open), and there are eleven notes. See `dup-sweep.md`.
- **No Lean, no `lake`** was run for this staging. The pack reuses the recorded phase-1 and phase-2 evidence.
