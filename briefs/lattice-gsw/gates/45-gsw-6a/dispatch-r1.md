# Dispatch · Gate 45 round 1 (the GSW 6a gate)

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/059331913c8a5380d3ae53e5e9dffa3c7ff6e2b4/outbox/gates/45-gsw-6a-gate)
is pushed to the exchange (replayed by the maintainer onto the moved tip; see State at staging). Seyoon
dispatches.

## Prompt for Codex

```text
You are an external Codex auditor for Gate 45 of GSW phase 6 (the 6a gate:
the owner-side PR O1 and the 6a complexity-layer statements), round 1, in
https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at 059331913c8a5380d3ae53e5e9dffa3c7ff6e2b4.
   Read outbox/gates/45-gsw-6a-gate/README.md, pack-r1.md and bundle.md.
   Verify the pack using SHA256SUMS, and verification-r1.zip using the
   SHA256SUMS inside it.
2. Audit two stacked draft PRs, using the pack, with campaign records
   8c5875fa268a622e4e166da5f7a992715097c2c7:
   - PR #358 (O1) at Lean head a616adcac0760ab56b1b0a2a4869f4763843f9ab
     (branch land/gsw-6a-o1; base cryptography/pass-shelat-ch2-4, merge base
     e1d39836ed4a69a34914c35f4c73c71de853dcc6, whose Lean equals the #346
     merge 3f540c22360c869069a0fba684e23ce6f3cb20db, olean snapshot #5):
     audit it as a proof/refactor. The balanced-tree combinators move from
     TreeNCAC.lean into Complexity/CircuitComplexity/FormulaArith/
     Combinators.lean as the public TreeCircuit.balanced (decls2 7/0/0), with
     the five Rule 10 repairs ruled in 6a Q2 (three named reads plus the
     sumSize_pairUp/maxFaninL_pairUp nil cases) and every TreeNCAC statement
     unchanged. TreeNCAC keeps 2 pre-existing seal failures and 4 explicit
     unfolds (G6A-F05), which are not O1's.
   - PR #359 (statements) at Lean head
     73aedcdaaaffef7e69ab012d9b9195f150bae68d (branch land/gsw-6a-statements;
     base land/gsw-6a-o1 at a616adca): branching programs, Barrington in both
     directions (BWBP = NC1), the NAND form and its layering, and the
     formula-arithmetic layer, with 98 targets admitted, and the landing
     edit LE-ren (TreeCircuit.rename dropped for the public reidx family;
     6a Q1, DL-54).
   Check (pack, questions A-F):
   - #358: the move is exactly the stated changes; the seven statements are
     true and proved for every input; the repairs are semantics-free; Rule 10
     and the controls; G6A-F05 is pre-existing;
   - #359: a fidelity audit of all 98 targets against Bar89, BV14, BV11 and
     plan section r3 (C1-C25, N1-N13, F1-F3, F5-F10): each target true, its
     hypotheses neither vacuous nor contradictory, the edge cases, and strong
     enough for the 6b consumers r3 plans; N12 in the args_lt field form
     (6a Q4); the sigma-0 reading of C16 (G6A-F11); the definitions and the
     proved readers and helpers (no definition contains sorry; sorryAx
     reaches toNANDForm and layerNAND only through N2 and N12-N13: is that
     acceptable?); the 112 citation anchors and the reference lines; the
     sketches; the registrations and registry rows H18-H20; sizes
     (Combinators 629 lines, G6A-F06);
   - duplication (an undisclosed or unaccepted re-proof of a public lemma is
     a major): LE-ren's completeness against reidx, widenCircuit and
     restrictCircuit, and any other restatement of TCSlib or Mathlib;
   - the evidence: the replays on snapshot #5 (R1 9/9, R2 20/20, admissions
     +0/+98 exact, axioms, canonical coe-A on every owner record equal to the
     #4 run, root 14,074 requests 0 errors), and confirm or refute the
     carry-forward argument (equal closure keys plus identical coe-A records
     stand in for re-running the strict/coe-B seals and the controls); exact
     per-variant counts;
   - whether anything is undisclosed (pack, known slips), and grade the
     review findings G6A-F01 to G6A-F15.
   Out of scope: the Q3 owner-side reader PR and any in-house 6a fills (not
   on either PR); 6b (Gate 46), bootstrapping and circular security; the
   [Gen09] citation (a docstring-only follow-up). The merge order (#358
   first) and the snapshot adoption are maintainer merge conditions, not
   audit items.
3. Return gate45-gsw-6a-findings.md as Markdown in this chat, with findings
   numbered G45-01, G45-02, ..., counts by severity per PR, and a verdict per
   PR and overall: CLEAR (zero blockers and zero majors) or HOLD. If you need
   multiple evidence files, return a ZIP containing that Markdown and
   evidence.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```

## State at staging

- **Records pin:** `8c5875fa268a622e4e166da5f7a992715097c2c7`, the tip of `origin/cryptography/pass-shelat-ch2-4` after
  `git fetch` at staging ("Records: GSW 6a re-replay on snapshot #5; draft PRs #358, #359"). It is #358's merge base
  `e1d39836` plus five records-only commits (0 code paths); the pack's own files are filed after the pin.
- **Records copy:** this directory, `briefs/lattice-gsw/gates/45-gsw-6a/`, written on the records checkout and **not
  committed**; the maintainer commits it (explicit paths). `bundle.md` is not committed to the records (`workflow.md` §3).
- **Exchange:** the commit is `059331913c8a5380d3ae53e5e9dffa3c7ff6e2b4`, one SSH-signed commit on the exchange tip
  `5976f1a04ab9e075f0f032e3f28aeade87c4d50d` (the Gate 48 round-2 staging commit). It is the staging commit `b6faf667`, replayed by the maintainer with `git cherry-pick -S` onto the moved tip (equal patch-id; only `outbox/gates/45-gsw-6a-gate/` changes), and is pushed.
  - The local branch is `stage/gate45-exchange` in the records checkout's repository (the sparse worktree
    `$SP/wt-exch-g45` used to build it was removed after the commit). Push it with
    `git push origin stage/gate45-exchange:exchange/pass-shelat-ch5-8`.
  - The commit adds only `outbox/gates/45-gsw-6a-gate/` (14 files).
  - **Pushed** (2026-11-17) after the replay onto `5976f1a0`; the replay has the same patch-id as `b6faf667` and its
    folder verifies 13/13 from a fresh `git archive`.
  - `SHA256SUMS` (`6add94a706aec6e41cbcd1ec49b382fa5f221522c9237b717bcd06074d2ee501`) verifies 13/13 from a fresh
    `git archive` of the commit; `bundle.md` is `bd71212a60df403319f7e3f4159422344c6b9badf1d3ae673dd3786d222ebc00`, 86
    sections, each checked equal to its source; `verification-r1.zip`
    (`6a7f78c3e4e30b465b482be4f5f36b734d05544fa682aab06735bf01e417a731`) has 484 entries and verifies against its own
    `SHA256SUMS` from a fresh extract (483/483; the copied `phase1/`, `phase2/` and `rereplay5/` files also verify against
    their `SHA256SUMS.original`).
  - The folder is 2.2 MB.
- **PR #358:** draft, head `a616adca`, REST `base.sha` `3ef91b40` (records-only descendant of the merge base `e1d39836`),
  updated 2026-11-17T09:46:54Z. **PR #359:** draft, head `73aedcda`, base `land/gsw-6a-o1` at `a616adca`, updated
  2026-11-17T09:47:21Z. The descriptions in the pack are the bodies read then.
- **No Lean, no `lake`** was run for this staging; the pack reuses the phase-1, phase-2 and re-replay evidence as recorded.

**Ready to dispatch** once the exchange commit and the records copy are pushed.
