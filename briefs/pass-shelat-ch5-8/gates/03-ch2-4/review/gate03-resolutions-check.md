# Gate 03 (03a, 03b, 03c, 03e): discrepancies found while drafting the round 1 resolutions

Checked against the code at #201's head `0c348ff94cacf24d96d99078c9dd9e328530c8d2` (worktree
`wt-g03c-fix`, clean), which contains all four repairs: #198 (`c10ed6ac…`), #199 (`b925421e…`,
worker commit `30f90d36…`), 03a (`e8f45ca3…`) and 03c (`bc2aab59…`). Records at
`cryptography/pass-shelat-ch2-4` `f4ca2a55…`. No Lean was run; axiom facts come from
`evidence-repairs/03ac/checks-axioms.log` (the full `Checks` print at #201's head). Lean paths are
under `TCSlib/`.

**14 discrepancies** (D1–D14): 12 review-proposed fixes not found, 2 claims not confirmed or
inaccurate. Section C lists the findings that have no resolution at all. Section D has observations
that are not gaps against a review fix.

## A. Review-proposed fixes not found in the code or records

| # | Pack · finding | Review's fix | Evidence |
|---|---|---|---|
| D1 | 03a #3 (minor) | Fix (A): the additive `NUPPT.exists_compParam` in `Closure.lean`, with `exists_comp` its special case. | Not in the tree: `grep -rn exists_compParam` over the #201 worktree hits only `gate03a-review.md:83` and `gate03a-findings.md:29`. Only the scope is stated (`Complexity/Randomized/Closure.lean:56–57, 195–200`). Neither the ledger, `QUEUE.md`'s clean-up to-do nor the decision log defers it; the decision log row "Gate 03a repairs done" lists #3 among "citations, deviation notes and docstrings". **The only required, unscheduled ch. 2–4 Lean fix of the four reviews that is missing.** |
| D2 | 03a #22 (note) | Pack erratum: list `Asymptotic/EnsemblesLemmas.lean` as context for 03a, audited in 03i. | `03a-pack.md` last changed at `fed6c2fb` (staging); no erratum is written: under `gates/03-ch2-4/` the word occurs only in the 03a and 03l reviews. |
| D3 | 03a #23 (note) | Banners on the inventory rows **and** an erratum to the pack's stale Q1. | Banners done (`inventory-ch2.md:255, 265`; `inventory-ch3.md:38, 195, 204`); pack unchanged (as D2). |
| D4 | 03e #1 (major) | DESIGN §5 item 8 amended to the bounded-message convention (review §1.1, "Docstrings"). | `briefs/pass-shelat/DESIGN.md:1009–1010` still reads "`Efficient` time polynomial in the total input length", with no message bound. The 03e commit `30f90d36…` does not touch `DESIGN.md` (`git log a3c5fa8b..HEAD -- briefs/pass-shelat/DESIGN.md`: only `c10ed6ac`, `e8f45ca3`, `bc2aab59`). |
| D5 | 03e #2 (major), M5 | DESIGN §5 item 11 becomes "`PerfectZK`, `PerfectZKAbort` stated; no source protocol attains them under D8/D10; GI is `StatZK` with negligible δ." | `DESIGN.md:1015–1017` still says "`PerfectZKAbort` stated as the perfect form" (the text the review called misleading). |
| D6 | 03e #2 (major) | Rewrite the Thm-175.1 row of `inventory-ch5-8.md` (with `SequentialZK.lean:41–45, 397–399`). | `briefs/pass-shelat-ch5-8/inventory-ch5-8.md:130` still says the simulators are "truncated with abort (`PerfectZKAbort`)". `SequentialZK.lean` is in gate 06's integration to-do (`gates/06-ch5-8-statements/PLAN.md:55–57`); the inventory row is not. |
| D7 | 03e #5 (c) (minor) | Correct the path in the run-3 summary line; note in 03e's attestation that the 22 core-module sorries are `main`'s. | `audits/pass-shelat/run3-audit-summary.md:17` still says "`TCSlib/Complexity/TuringMachine/Build/*` files of run 3b print 0" (last changed `c1360aa1`, 2026-10-28); neither `evidence-repairs/03e/` nor `03ac/` carries the note. |
| D8 | 03e #6 (a) (minor) | Tag `[Gol01]` in `Defs.lean`, `GraphIsomorphismZK.lean` **and** prong C's `SequentialZK.lean`. | Done in ch. 2–4 (`ZeroKnowledge/Defs.lean:68, 102, 184`; `GraphIsomorphismZK.lean:87, 289`). Prong C's head (`9e6f08bb…`) still cites "O. Goldreich, *Foundations …*" untagged (`Composability/SequentialZK.lean:85`), and gate 06's integration to-do does not name it. |
| D9 | 03e #9 (note) | Add the necessity argument to `Defs.lean` **and** the source issue to DESIGN §7 (beside item 50). | `Defs.lean:42–47` done; `DESIGN.md` §7 (:1145–1253) has no such entry; item 50 (:1243–1246) unchanged. |
| D10 | 03e #15 (note) | Record both D8 limits (Barak–Lindell, `\|x\|` indexing) in the ch. 5–8 bridge notes (S1 note addendum). | No occurrence of "Barak", "strict-PPT", "constant-round" under `briefs/pass-shelat-ch5-8/` outside the 03e findings and review. |
| D11 | 03e #16 (note) | Add Thm-124.1 and Claim-124.d to 03e's inventory list with "(also 03g)", or say 03g owns them. | `03e-pack.md` unchanged since `fed6c2fb`; no hit for `Thm-124.1` in it. |
| D12 | 03e M7 | Correct 03e's scope line (03g is 3-colouring, 03k graph isomorphism) before dispatch. | `03e-pack.md:39` still reads "graph isomorphism, 3-colouring: packs 03g and 03k". |

## B. Claims not confirmed, or records found inaccurate

| # | Claim | Finding |
|---|---|---|
| D13 | 03e commit `30f90d36…` ("names the stubs behind the `sorryAx` prints") and its comments in `audits/pass-shelat/Checks.lean:321–324, 445–447`: the four Thm 124.1 forms and the three new tied forms reach **exactly** `colRep_efficientProverProof` and `col_zk`. | **Not confirmable without Lean** (no build run). Consistent with what can be checked: `LevinReduction.zk` and `.efficientProverProof(Err)` print standard (`checks-axioms.log`); the only other `sorry` in the 3-colouring protocol files, the `decidable` clause of `R3COL_witnessRelation` (`ZeroKnowledge/ThreeColoring/Protocol.lean:844`), is named by no Lean file other than its own (one prose mention in `ThreeColoring/Machines.lean:21`). The review had said "almost certainly". |
| D14 | `duplication-ledger.md`, DL-15: "private copies in `Collections.lean` and `GGMReductionEval.lean`". | The `GGMReductionEval` copy is **public**: `TCSlib.Cryptography.GGMRed.decodeFin_eq_some_iff` (`Cryptography/Asymptotic/GGMReductionEval.lean:163`, in `namespace TCSlib.Cryptography.GGMRed` from :60). That is why the review (03b #12c, M6) warns of the namespace collision when the `Collections.lean` copy is made public. |

Every other claim of the four commit messages was found in the code: the 03e theorems listed as
"re-proved with unchanged statement text" have the same statement text before and after
(comparison of `a3c5fa8b` and `30f90d36`); 03c's 17 moved declarations have the same statements
(`c10ed6ac` vs `bc2aab59`); every new `#print axioms` line is in the head's `Checks.lean` and
prints standard axioms (except the three tied Thm 124.1 forms, as declared); none of the four
diffs adds a `sorry` or a `@[simp]`. The replay and lint claims rest on the evidence logs, which
were not re-run.

## C. Findings with no resolution at all

Nothing was done for: **03a #22** (D2), **03e #15** (D10), **03e #16** (D11), **03e M7** (D12).
**03a #3** (D1) has only its scope docstring, not the review's fix. All four review-level
"Not resolved" rows of the pack errata (D2, D3, D11, D12) can be closed by the closing-round pack
text itself.

## D. Observations (not gaps against a review fix)

1. **#201 is not merged.** 03a's and 03c's "Fixed" rows hold on `cryptography/pass-shelat-ch2-4-g03-ac`
   only; the branch `cryptography/pass-shelat-ch2-4` (`f4ca2a55…`) has no Lean change since
   `af91d53a`. Their closing rounds should pin to #201's merge.
2. **Residual "dyadic" wording.** `Cryptography/Asymptotic/Ensembles.lean:52` and DESIGN register
   item 5 (`DESIGN.md:1002`) still describe `Ensemble` as "dyadic samplable distributions", the
   wording 03a #7 corrected on the structure (`Ensembles.lean:119–125`). The review judged these
   two lines right, so this is not a gap against it, but the closing round may raise it.
3. **03c #7's quoted constant differs from the review's text, correctly.** The review wrote "the
   text's `1/(4mε'²)`"; the raw extract (`blueprint/src/references/pass-shelat-2010-ch3.raw.md`,
   about l. 995–997) reads `(1 − 4ε'²)/(4mε'²) ≤ 1/(mε'²)`, which is what
   `Cryptography/Asymptotic/HardCoreClaims.lean:113–115` now quotes.
4. **Line caps.** `Cryptography/Asymptotic/Collections.lean` is 982 lines and `NextBit.lean` 972
   (the review asked for no `NextBit` split); `Candidates/Rabin.lean` is 994.
5. **Optional review items left undone and tracked nowhere:** 03a #2's `Indist.copies'`
   (backlog); 03b #8's `StrongOneWay` → `ofString` bridge; 03c #4's `PRG.Secure.expand` (the commit
   message says "left for that pack", 03d; no to-do); 03c #1's prong D stretch
   (`Derandomization.lean`, unchanged at prong D's head `6ea900ae`); 03c #10's Claim-107.c; 03e #1's
   `InteractiveProof.mem_IP` (the docstring says the capping argument is not formalized,
   `ZeroKnowledge/InteractiveProofs.lean:44–50`).
6. **Communication items not evidenced.** The 03a review asks that the S1 interface readers be
   told of #1's `Computes` docstring change and #3's addition; no S1 note addendum has changed since
   the ownership transfer (`S1-note-frederick-addendum-2.md`, `444a75d7`).
7. **Scheduled debt.** Every "Scheduled" row depends on work not yet done: clean-up part 1 (in
   progress: DL-11's first half, DL-16, DL-18, DL-19, 03l's minors), part 2 after #195 (DL-9, DL-10,
   DL-12–DL-15, DL-17, the rest of DL-11), the `QUEUE.md:147` to-do (`SimulatorMachine`'s import),
   and gate 06's integration to-do (prong B's `hcanon`/`hspec`; prong C's `ProverBounded`,
   `PerfectZKAbort.seqRep`, the 3-colouring corollary of G3-7 (d)).
