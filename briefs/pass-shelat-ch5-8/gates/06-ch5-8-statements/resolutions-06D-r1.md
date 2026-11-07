# Gate 06D round 1 resolutions

**CLOSED, 0 blockers / 0 majors / 4 minors.** The issued randomness statement gate meets its
closing threshold at `3f6db40e1688c4a0bb922c9575dd3bd2157a650b`. Findings were filed verbatim before these resolutions in
`findings/gate06D-r1-findings.md` (34,608 bytes), SHA-256
`a13979aa9fafcad2ab77a5b33d59fdd034c5a7969fd346f44e3a70385297bcfc`.
This is user-supplied local Codex Markdown, not an auditor push. Issued records/exchange pins
remain c81baa7712ab1b43357276ef5df138d02616c9d0 /
5928e06c02b382b63b9b384db89d0458b520f351.

| Finding | Maintainer disposition |
|---|---|
| G06D-01, minor | Accepted. An arbitrary positive real exponent does not supply a computable exact seed schedule. The proposed sketch fixes an integer `d≥2` with `1/d < min(ε,1)` and computes the least integer `s` with `n≤s^d`. Its syntactic polynomial output envelope is `a(s^d+1)^k+s+1`, and bad-input advice has length at most `s^d`. The finite-to-one seed map preserves infinitely many bad lengths. A fixed `1/12` threshold gives eventual success at least `7/12`, avoiding a majority-boundary digression. Enumeration and its time proof remain the substantive fill. |
| G06D-02, minor | Accepted. The module summary will state fixed failure probability `δ<γ`; constant edge alone is insufficient. KV94 amplification constructs a different learner and changes sample/time/evaluation costs. That resource bridge remains additional work, not a theorem already provided by part (c). |
| G06D-03, minor | Accepted. Replace the facade's extraction/Occam descriptions with the actual impossibility, PRF prediction-hardness and BPP derandomization contents. |
| G06D-04, minor | Accepted via **docstring clarification**, preserving the theorem. Its conclusion gives advice equality and identical output for every coin tape. The current proof chooses a zero-coin witness, but zero coin schedule is not an exposed conclusion. No new resource clause or strengthened statement is added. |
| N1, scope note | Retain the pointwise `effSources` quantifiers: a sampler may depend on fixed length. This is not one uniform sampler family defeating the extractor at all lengths. Finite hard-coded tables explain why the pointwise statement is weaker; the efficient rejection route remains a valid proof plan. |
| N2, admissions | Retain all three direct security/impossibility admissions and the derived admitted-dependent PAC consequence. Closure does not complete them. |

All four proposed corrections are in `review-r1-ad/minor-prose-corrections.patch`, **unapplied**.
All six A/D files preserve exact noncomment bytes; the patch applies cleanly to the frozen
source. The full stored terms, hypotheses, bounds and algorithms are unchanged. The active
audit branch is not advanced while B/C results are pending. Apply/recheck the comments in
final source reconciliation; the proposed patch is not a fresh native source pass.

## Mathematical assessment and evidence limits

The integer-root schedule uses only a fixed natural constant, integer powers and comparison;
it requires no computable representation of `ε`. Reindexing gives polynomial advice and
computation in the seed parameter. Since `1/d<ε`, seed enumeration times polynomial overhead
fits `O(2^(n^ε))`, and positive time bounds absorb finite exceptions. The confidence-gap and
rejection/fallback calculations support the other two issued statements with their declared
quantifiers. This is statement/sketch assessment, not the missing machine/proof implementation.

All required exact PS10 Chapter8 comparisons were performed by the auditor. The fresh literal
KV94 pages, published-edition AB09 comparison, Goldreich PDFs and draft/publisher equivalences
named unavailable remain unavailable. Contextual prior audits are not recast as fresh source
access. The auditor had no Lean/Lake and did not rerun the historical native artifacts;
independent rational finite checks corroborate semantics without certifying asymptotic Lean
proofs. Root-export elaboration, other prongs and combined S2/Gate06 verification are not claimed.
The common 17 failed source seals and all inherited reads remain failed/debt observations.

This prong's fills may follow its closure under their own worker selection/brief/actual-source
prerequisites; no fill or follow-up audit is dispatched by these resolutions. S2 is separately
merged in the target, and final #232 integration must reconcile that genuine source advance.

Internal review: `review-r1-ad/review-d/` finds no hidden blocker/major, independently checks
the integer-root/confidence/quantifier reasoning and reconstructs the initial comment patch
in memory. The four D sections are unchanged in the final proposal; no fresh native run or
new primary-source access is inferred from that review.

**Not yet clear to merge — 06D is closed; #232 still needs 06B/C and final source reconciliation.**
