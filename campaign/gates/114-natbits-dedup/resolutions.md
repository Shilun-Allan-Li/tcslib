# Gate 114 resolutions

Original external findings are preserved verbatim in `findings.md`: **7,233 bytes**, SHA-256
`a7ed11a46b0d0bb724a62359717ee98e0203f1f712e69232da54e97ee2aad169`. The shared top-level inbox original is untouched.
Independent internal review and source/census/packet cross-checks are retained in
`review-incoming/2026-11-07-natbits-a7ed11a4/`. Reports are data; every note was reviewed.

Verdict: **PASS — 0 blockers, 0 majors, 0 minors, 8 notes.**

| Note | Disposition |
|---|---|
| N1, provenance | Accepted; all 211 sections and source/records pins match the issued package. |
| N2, length bounds | Accepted; exponent-zero and largest admitted successor inputs are covered mathematically; no new Lean run is claimed for the auditor's checks. |
| N3, powers/logs | Accepted; positive 2n and unconditional 2n+1 bounds remain distinct; logarithmic equality keeps its nonzero premise. |
| N4, word values | Accepted; the bound is for every Boolean word, including empty and redundant-zero words, not only canonical binary representations. |
| N5, freeze/counts | Accepted; full headers, visibility/order and six literal proof moves match. Source 2366→2360 and unfiltered CI 2377→2374 include all six moved auxiliaries; new module has 16 compiled constants / 10 source theorems. |
| N6, placement/rule 10 | Accepted; Mathlib-only lower module, approved namespaces, resolved retained names and scoped Frag buffer-cell seal. No global legacy seal is claimed. |
| N7, debt | Accepted; 926→923 pair delta, no new counted member; D9 remains record-only. E-PAD's repairs are current code; no new debt acknowledgment is granted. |
| N8, evidence/limits | Accepted; actual maintainer runs and the auditor's source/finite arithmetic checks are distinguished. The auditor did not run Lean, seals or the screen algorithm. |

**Gate 114 CLOSED.** No code, API, import or debt decision is required.

Audited Lean head remains `a02d0531898764d363474fe4d65ccbeff0e7ea5e` and the issued packet is unchanged.
The current campaign `7df0d047d501a1d08982d17d20208faf49d39131` was merged into the PR, producing
`073d52fc7ecd6ff27f7a3efbe5dc8860b9b0e278`. All **22 audited changed file blobs are identical**; the only actual Lean change
from that earlier passed 344-module snapshot is merged #228's now-proved Padding file.
A fresh **two-module catch-up merged-tree replay** compiled Padding and its facade on a complete
copy of `oleans-mnb1`, yielding **`oleans-mnb2`**, zero failures/static mismatches. This is a
successive replay chain, not a splice of independent snapshots. It directly checks the new
E-PAD proof under NatBits' import environment. Raw logs/receipts disclose the corrected
postprocessing summary-format assertion; both Lean runs themselves passed before that check.

The fresh merge-tree preview at the current campaign is clean and has exactly this passed
snapshot's Lean tree (`current-merge-check.json`). **Clear to merge: #222**; the user merges.
