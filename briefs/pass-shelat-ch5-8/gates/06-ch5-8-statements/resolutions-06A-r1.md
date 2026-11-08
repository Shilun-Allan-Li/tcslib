# Gate 06A round 1 resolutions

**CLOSED: PASS, 0 blockers / 0 majors / 2 minors.** The issued authentication statement gate
satisfies its closing threshold at `3f6db40e1688c4a0bb922c9575dd3bd2157a650b`. Findings were filed verbatim before these
resolutions in `findings/gate06A-r1-findings.md` (46,660 bytes), SHA-256
`03782b01b654595b437ebfd408bd6b7a628dbdf2bb2b47e0280f2fd3e13e8bd5`.
Provenance is a user-supplied local inbox Markdown file by the selected Codex route; no auditor
push is asserted. Issued records/exchange pins remain c81baa7712ab1b43357276ef5df138d02616c9d0 /
5928e06c02b382b63b9b384db89d0458b520f351.

| Finding | Maintainer disposition |
|---|---|
| A-01, minor | Accepted. The truncated exponent sampler is statistically close to uniform, and exponentiation preserves that bound; it does not make an exactly uniform element. The six-file patch replaces the module gloss by “within `2^(-n)` of uniform,” retaining the full-group hypothesis. The reported `p=5,n=3` distribution and distance `3/32` support this distinction. |
| A-02, minor | Accepted. State independence in the coupled honest execution and count the jointly favorable pairs, rather than multiply probabilities after conditioning on non-abort. For a queried fresh forgery their fraction is the number of differing positions divided by `2n`; for a zero-query forgery it is `1/2`. Work at `n≥1` and absorb the zero parameter as a finite exception. A best position carried in `O(log n)` non-uniform advice implements the averaging bound without assuming exact finite-tape uniform sampling of `[n]`. The admitted theorem is not filled. |
| A-03, note | Retain `hdom` as a sufficient full-domain repair, not a logically minimal quantifier. No hypothesis is weakened. |
| A-04, note | Retain the fixed polynomial-message-length adaptation. Neither hash-and-sign nor its existential corollary is relabelled as an unrestricted finite-string result. |

`review-r1-ad/minor-prose-corrections.patch` is the concrete **unapplied** correction proposal.
Its six files have exact noncomment byte equality and a successful patch-application check at
the frozen pin. No public statement or proof body changes. The source branch remains frozen
pending B/C findings; these edits must be applied/rechecked in final integration before landing.

## Scope and evidence limits

The audit inspected the five primary authentication modules/facade, their definitions,
statements, generated readers and short correctness proofs. All required PS10 authentication
comparisons were available. Unavailable Goldreich drafts/publisher identities outside this
prong remain unavailable; no draft/publisher equivalence is inferred. The auditor did not run
Lean/Lake: historical source-matched native/seal/axiom records were inspected, while the finite
Python semantics checks are independent corroboration only.

The four substantive security results remain admitted, and the derived existential theorem
depends on them. Gate closure approves their statements/sketches, not proof completion,
whole-library Rule10 cleanliness, other prongs, or the unreviewed combined S2 target tree.
The shared inherited failures, equation references and exact notation rules remain recorded.
Authentication fills may follow this prong's closure, subject to a separately selected worker,
a concrete issued brief and the actual source/landing prerequisites. No new fill is dispatched
by this resolution.

Internal review: `review-r1-ad/review-a/` independently reproduces the finite bias/counting
arguments and checks the final Authentication hunks, finding no additional issue. The T1
extended-input plus `NUPPT.exists_withAdvice` route makes the advice transport explicit.

**Not yet clear to merge — 06A is closed; #232 still needs 06B/C and final source reconciliation.**
