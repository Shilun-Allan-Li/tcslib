# RD-3 statement gate: resolutions (round 1, CLOSED)

**Gate:** `audits/b6-restatement-pack.md`, bundle SHA-256
`a7e8c5049b94951ca58347b97c39760f8f68a359ffb26f8196e3b87129af71df`, 36 sections.
**Findings:** `audits/b6-restatement-findings.md`, preserved verbatim: **PASS, 0 blockers, 0
majors, 4 minors, 8 notes.**

The auditor checked [AB09] Exercise 4.1 (p. 93), the standing convention (p. 79) and Theorem
4.8. The forward statement is faithful, and dropping the failure clause loses nothing the route
uses. The window route is a sound proof plan; the auditor checked:
- the inclusion;
- the clock's four-factor bound with its strict surplus;
- the `Fin 3` output tag;
- the uniform space count;
- the normal-form and all-times bridges;
- the contradiction and the alphabet-reduction packaging.

The freeze reproduces: only `space_universal`'s statement changed.

## Minors

1. **The `+ logSpace` addend is avoidable.** The auditor gave a bounded-prefix input device (a
   unary ruler of the header's length) that would give `C·s`. **Disposition:** the statement
   is kept as gated, and the stronger route is recorded as an implementation choice. Whether to
   strengthen `space_universal` to `C·s` is decided when H5's statements are gated, since the
   stronger form needs a changed H5 contract and sketch, not just a shorter Lean term.
2. **A fourth stale design row** (§12.8a, *Per-consumer rows*). Marked superseded, pointing to the
   window route through H2, H3 and H5 on R8.7's rows.
3. **`counterLoopTMVia` has an optional early exit plus clock exhaustion,** not one exit. Design
   §16b item 3 is corrected: H3 merges halt and window exit into the early escape and tells them
   apart afterwards; its public contract exposes all three outcomes.
4. **Finding B's wording.** The marker tape uses one plus the largest simulated input position
   reached (`Θ(n + 1)` on full scans), so the interpreter cannot guarantee `O(S(n))` uniformly for
   sublinear `S`. Corrected in design §16b item 3 and in `Hierarchy.lean`'s docstrings (on PR
   #82, comment-only).

## Notes

Notes 7–8 and the numbered checks are carried into the host statements now being drafted (H3,
H5, `U₀`, the two bridges). The auditor's suggested sanity obligations go with them:
- a restoring suffix-boundary test, including empty input;
- `U₀`'s startup with empty output and input position 1;
- all-time space preservation under state relabelling;
- an H3 run that halts on its final simulated transition while emitting the deciding bit.
