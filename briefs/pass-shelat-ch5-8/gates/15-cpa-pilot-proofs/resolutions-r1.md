# Gate 15 · resolutions, round 1

**Status: CLOSED** (0 blockers, 0 majors, 1 minor, fixed). Auditor Codex, 2026-11-11; findings
uploaded by Seyoon and filed verbatim in [findings/](findings/gate15-cpa-pilot-proofs-findings.md)
(SHA-256 `0081197469d48b3e972102a3d10c88476d264979d0fde1666c1b9baed6d5c750`). #290: 0/0/0/0. #291: 0/0/1/0.

| Input | Pin |
|---|---|
| Exchange pack | `c53e2baace2497ceca5814ffc8b1f57e9c04eaf8` |
| Records | `315f781b6d7daf051c9f639fe6fba2e12839d4c2` |
| PR #290 head | `95df0b4fa15e140ffd8f692699c66d0683fc916d` |
| PR #291 audited head | `c286bc6a9b372036f959a033729d841ce10dfa16` |

The auditor verified all hashes and the statement freeze, reviewed both proofs step by step
(endpoints, reductions, exact simulations and signed identity, bounds, edge cases), the rule-10
evidence (re-derived control outcomes; request sets complete against the imported-definition
catalog), the landing edits and the axiom logs, and re-ran the style lint. It did not recompile.

| # | Severity | Resolution |
|---|---|---|
| G15-01 | minor | **Fixed.** `qRun_eq`, `plantTuple_eq`, `plantAns_eq`, `plantOut_eq` now state their equations in words and formulas (commit `7360ffbc`, docstrings only). The affected modules and downstream through `TCSlib` rebuilt at the new head, rc 0, 0 errors, each row bound to the head's source hash (`landing-291-r2/g15-01-rebuild.jsonl`). |

**Clear to merge** — #290 at `95df0b4fa15e140ffd8f692699c66d0683fc916d`, then #291 at
`7360ffbcc2a40a4d00f627b2ea986cbc7c247310` (retarget #291 to `cryptography/pass-shelat-ch2-4` after #290 merges).
