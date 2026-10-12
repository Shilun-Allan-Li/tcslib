# B2b fill gate (`NP ⊆ PSPACE`, `3SAT ∈ PSPACE`): resolutions (CLOSED, round 1)

## Round 1 (2026-10-11): 0 blockers, 0 majors, 1 minor, 4 notes

The findings are verbatim in `audits/b2b-fill-findings.md`; the pack is
`audits/b2b-fill-pack.md`, with its 70-file bundle. The audited head is `cef76e00` (PR #49).
The auditor found no mathematical, statement-freeze, construction-route or unacknowledged
duplication defect. It confirmed:
- **the freeze:** the cumulative patch reproduces the head blob, the four public signatures
  are byte-identical, and the per-delivery stages are as recorded (item 1);
- **route fidelity:** the four sanctioned glue machines only, the one-definition rules, and no
  R8.8, R8.5e or L row (item 2);
- **all five Question 5 obligations**, with a complete-run space calculation that has no factor
  counting trials, and the correctness equivalence (item 3);
- the P4.1 notes 8 and 9 (item 4);
- the combined tree's relevance to the audited head (item 5);
- the screen, rerun over all 14 files: exactly the two disclosed in-file pairs touch
  `Inclusions` (item 6);
- the documentation, including the maintainer's comment-only refresh (item 7), and the size
  (item 8).

| Finding | Disposition |
|---|---|
| 1 (minor): the bundle omits the standards its severity and duplication rules cite (`audits/TEMPLATE.md`, `policy.md`, `workflow.md`) | **Accepted.** The auditor recovered all three at `cef76e00`, so this audit was not affected. **Pack practice:** every future bundle attaches these three standards after the pack. The shipped pack and bundle are kept unchanged under the archival rule. No Lean change |
| 2 (note): the shared-trial restructuring and classical durations stay within route 1 | Confirmed. No action |
| 3 (note): the two in-file pairs (`b2b_callEmb` ← `b2b_bankEmb` 66%, `b2b_trialCfg` ← `b2b_setupCfg` 65%) are permissible assembly similarities | Confirmed; the recorded explanations stand |
| 4 (note): the maintainer refresh `6da48293` and the 2,880-line size are acceptable | Confirmed. No action |
| 5 (note): the private census checks direct `sorryAx` references; the target closure walks are the transitive check. Archive verification, non-execution of environment helpers and fresh-olean creation remain attestations | **Recorded.** Later packs describe the census as a direct-reference check beside the transitive walks |

Item 6 also records that the historical `b2b-screen-base.txt` (665 declarations / 458 pairs) was
a narrower run. The integration records and continuations already use the corrected 14-file
baseline (784 / 626).

**Gate CLOSED.** `Complexity.NP_subset_PSPACE` and `Complexity.SAT3_mem_PSPACE` ([AB09,
Example 4.6]) are filled, admission-free and audited. Cluster B2b is complete.
