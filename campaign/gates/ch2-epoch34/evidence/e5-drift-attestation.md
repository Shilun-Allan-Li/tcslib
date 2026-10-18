# E5-closure drift attestation

Baseline: the gate-audited snapshot (commit `154ecb18`, the round-2/3
manifest `final-source-manifest.md`). Current: the post-dedup worktree.
Method per `workflow.md` §6: comment-stripped ordered declaration
sequences compared per module; public declarations enumerated
gained/lost/changed.

| Module | decls before | after | deleted privates | public drift |
|---|---:|---:|---:|---|
| `TCSlib/Complexity/ClassNP/EXP` | 155 | 153 | 2 | none |
| `TCSlib/Complexity/ClassNP/Nondeterminism` | 279 | 206 | 73 | none |
| `TCSlib/Complexity/ClassNP/SAT` | 293 | 282 | 11 | none |
| `TCSlib/Complexity/CookLevin/Hardness` | 623 | 558 | 65 | none |
| `TCSlib/Complexity/ClassNP/Tautology` | 100 | 98 | 2 | none |

All modules not listed are byte-identical to the baseline. Public
surface drift: **none** — the dedup is private-deletion-only, and the retained declaration sequence is an ordered subsequence of the baseline in every changed module.
