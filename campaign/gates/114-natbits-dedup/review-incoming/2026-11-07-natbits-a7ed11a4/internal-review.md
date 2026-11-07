# Incoming gate 114 NatBits audit: internal review

**External verdict: PASS — 0 blockers, 0 majors, 0 minors, 8 notes.**

**Internal result: accept all eight notes; no code change, new design decision or debt
acknowledgment is required.** The maintainer may close the gate after committing the original
report and dispositions. Merge clearance additionally needs the current clean merge and the
focused catch-up validation described below; this review does not itself clear or merge #222.

## Receipt and scope

Original file: `tcslib-exchange/inbox/natbits-dedup-findings.md` (the shared top-level inbox,
not our campaign inbox). Copied byte-for-byte to `findings-original.md` in this review folder;
the original is untouched. **7,233 bytes**, SHA-256
`a7ed11a46b0d0bb724a62359717ee98e0203f1f712e69232da54e97ee2aad169`. `receipt.json` records the absolute source path and dispatch pins.

Audited Lean: `a02d0531898764d363474fe4d65ccbeff0e7ea5e`. Audited records: `d857c6c8a195b388079a8796e789f9852c047815`.
Bundle SHA-256 `c6705848383a15a6e6033dc4056953e65e237d8a08bbf2a5472432cae69058fd`, **211 sections**. I independently checked the published
exchange Git blob's hash and all 211 serialized section bodies against their corresponding
Lean/records Git objects, including the documented final-newline normalization. The bundle and
report identify exactly the dispatched package.

This is a source/records review. I ran no Lean, build, dependency cache, copy-text screen or Git
mutation; no campaign or exchange file was edited. All writes are confined to this review folder.
The executed Lean/screen claims below are the maintainer's supplied evidence, whose raw records
and input hashes I checked. The auditor's separate finite computations are attributed to the
auditor, not claimed as my own execution.

## Disposition of every note

| Note | Independent review and recommended disposition |
|---|---|
| N1, provenance | **Accept.** The checksum and section count match dispatch. Every one of the 211 section bodies matches its pinned Git object. All 22 head source blobs and 21 existing base source blobs used in my freeze cross-check match the pinned exports/objects. No moving branch was substituted for the audited head. |
| N2, binary lengths | **Accept.** The four literal statements match the report. In the successor-width theorem the hypothesis is indeed `m ≤ 2^e+1`; the maximum examples `e=0,m=2` and `e=1,m=3` give widths 2 and 3. The inequality `m+1 ≤ 2^e+2 < 2^(e+2)` holds because `2^e≥1`. At exponent zero the strict bound `n<1` forces zero, consistent with the empty binary word. These are mathematical/type checks, not additional Lean runs. |
| N3, powers/logarithms | **Accept.** The positive upper bound has the required `1≤L` hypothesis; the unconditional bound is the separate `2n+1` theorem. The logarithmic equality requires `n≠0`. At zero, binary length is 0 while the logarithmic successor is 1 and the power is 1, so the hypotheses and distinction are necessary. The lower bound remains valid at zero. The approved namespace move and references are consistent. |
| N4, word values | **Accept.** The statement is for every Boolean word through `Nat.ofDigits 2 (w.map Bool.toNat)`, not just canonical encodings. Empty word gives 0<1; `[false,true]` gives 2<4, and redundant high zero bits do not invalidate the inequality. The retained LogProg `bitsVal` theorem stays in Bin beside its definition. No new definition or admission is introduced in NatBits. |
| N5, freeze and census | **Accept.** I reproduced source totals 448→449 public, 1918→1911 private, 2366→2360 total; every surviving complete header, visibility and relative order agrees. Six preserved-name moves retain proof bodies verbatim. Exactly seven private declarations are removed and exactly the six listed surviving public bodies change. Independently parsing the unfiltered compiled censuses reproduces every added/removed/moved entry and 2377→2374. NatBits contains 16 compiled constants: 10 source theorems and six moved internal proof auxiliaries; none is omitted or misrepresented as a new source declaration. |
| N6, placement/name resolution/rule 10 | **Accept.** NatBits has exactly three Mathlib imports and no TCSlib imports. I independently reproduced the full 344-module affected closure. All seven Codec calls in Word, Deciders, StepDecider (two), Layout, Layout2 and Parse open LogProg and reach the retained theorem; the deleted Codec theorem is absent. The positive/general power-bound replacement is explicit at `PolyAmp.bigK_le`. The Frag evidence checks the exact changed buffer-cell step with paired controls; neither report nor pack claims a global seal of unrelated legacy proofs. |
| N7, debt and screen | **Accept.** Parsing the complete raw screen outputs gives 926 base pairs, 923 head pairs, 922 persistent, four removed and one added. The new directional pair is the in-file `qy_rnd_tests`/`dz_budget_le` near-match: source inspection shows canonical bound calls, not a fresh proof of those bounds. The source/compiled retirements match the approved BL/NB/LS scope. D9 stays record-only. Current E-PAD source has no `epad_two_pow_bits`, has the two `length_bits_le_self` re-points and cites `LogProg.bitsVal_lt_two_pow`; the historical delivery is not counted as current code. No new debt acknowledgment is needed. |
| N8, executed evidence and limits | **Accept.** Final probe source hashes match their run receipts for module axioms, changed-consumer axioms, sanity, Frag seal and compiled censuses. The complete 16-constant NatBits axiom output lists only subsets of the standard three. The changed-public axiom output and seven-example boundary source agree with the summary. Every one of the 344 replay rows has exit/error count zero and their admission counts total 68, matching the static report. Both blueprint exit codes are zero; policy lint's existing findings are explicitly retained. The auditor disclosed not rerunning Lean, seals or the full screen algorithm; its finite arithmetic enumeration is supplemental evidence, not an elaboration claim. |

## Merge clearance still belongs to the maintainer

At the current remote-tracking campaign observation `7df0d047d501a1d08982d17d20208faf49d39131`, the only actual Lean file
changed since the audited replay baseline is `SpaceComplexity/Padding.lean` from merged #228.
The scoped NatBits sources remain the externally audited ones. The source-side condition that
none of the 22 changed PR modules imports Padding holds, but the old 344-module downstream
replay itself included the former Padding stub. It did not execute the subsequently filled
Padding proof under NatBits' new import environment.

I flagged this as a focused compatibility check, not a gate finding or a request for a code/design
change. The root maintainer confirmed it will merge the current campaign into the PR branch,
verify all 22 audited file blobs are unchanged, and run **Padding plus its facade** as a two-module
catch-up merged-tree replay chained from `oleans-mnb1`. That is one successive snapshot chain,
not a splice of independent PR snapshots. Clear #222 only after that actual check and the clean
current merge check succeed; record the new PR/merge pins and replay receipt.

## Reproduced evidence

`cross-checks.json` records the independent source/census/pair-set checks, moved names, final
probe hashes and all 344 replay-result rows. This review preserves the original report intact;
canonical `findings.md`, `resolutions.md`, statuses and any PR/Git mutations are left to the root
maintainer. No additional Lean check was run by this reviewer.
