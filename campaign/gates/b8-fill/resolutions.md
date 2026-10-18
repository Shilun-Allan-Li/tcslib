# B8 fill gate (`exists_not_timeConstructible`): resolutions (CLOSED, round 1)

## Round 1 (2026-10-12): 0 blockers, 0 majors, 2 minors, 7 notes

The findings are verbatim in `audits/b8-fill-findings.md`; the pack is `audits/b8-fill-pack.md`,
with its 29-file bundle (the first bundled with the audit standards attached). The auditor found
the theorem and the reduction correct. It confirmed:
- the freeze, by reconstruction from the patch, and the 235-line size (note 3);
- the witness's growth and monotonicity, and that only the proved round-trip direction is needed
  (note 4);
- the HALT reduction, including odd-rank carries and empty output (note 5);
- that the digits bridge is a specialization of Mathlib's API, not a third copy of the recursive
  numbering proofs, so no duplication debt arises (note 6);
- the screen, rerun byte for byte over all 12 files (note 7).

It also checked 511 words of length at most 8 against both halting-bit values, as a
supplementary arithmetic check.

| Finding | Disposition |
|---|---|
| 1 (minor): the "Route as filled" appendix attributes stages (i)–(iii) to the primitive-recursive compiler, and says "the one bit where the two candidates differ" | **Fixed, comment-only.** Stages (i)–(ii) are one compiled emitter; stage (iii) runs the constructor that `TimeConstructible T` assumes, composed by `exists_comp_partial`, and `T` is never compiled; stage (iv) reads "a bit guaranteed to differ". **Erratum** for the shipped pack (§3) and `audits/b8-fill-record.md`, which repeat the attribution; both are kept unchanged under the archival rule |
| 2 (minor): the module design and the target's sketch call the enumeration "length-lexicographic", "with a 1 prepended" | **Fixed, comment-only.** Both now describe the little-endian dyadic enumeration: the word read least-significant bit first, behind a high sentinel `1` appended to the list. The private definitions and the frozen statement are unchanged |
| 3–9 (notes) | Confirmed. Note 8: replay, axiom and lint execution remain attestations, as the pack states. Note 9: the route probe's evidence stays distinct from the delivered proof's |

The swept file's comment-stripped code is identical to the audited one, and it elaborates
read-only with 0 errors and 0 warnings (`audits/logs/b8-fill-close.log`).

**Gate CLOSED.** `Complexity.exists_not_timeConstructible` ([AB09, Exercise 3.5]) is filled,
admission-free and audited. Cluster B8 is complete.
