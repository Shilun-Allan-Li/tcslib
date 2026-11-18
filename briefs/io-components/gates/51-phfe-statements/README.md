# Gate 51 · io-phfe statements gate (checkpoint 0)

**Status: staged, not dispatched** (2026-11-18). Static staging; no Lean was run.

The Codex statements gate on the io-phfe job's checkpoint 0: exchange
`1e77173a7032b57aa22260787711c6c7a1b7596e` (`inbox/fills/io-phfe/`), source HEAD
`70b85f9ba83f27393d98fa5bf88505aea3d22a8d`, base `iO/phase-a-base` at
`5ed465f62e4ae0f93ded1a1ba49e807591b589eb`, job records pin
`dbea2807532392781304e004715f3b0190025f5e`. The job's pack is `../../phfe/`.

| File | What |
|---|---|
| `intake-r1.md` | maintainer's static intake of checkpoint 0: integrity, contents, fidelity spot-check against the PDFs, rule 15, duplication, process; findings PHFE-C0-F01..F19 (1 blocker, 1 major, 8 minor, 9 notes); questions Q-G51-1..6 for Seyoon |
| `pack.md` | the gate's task for Codex: pins, local sources, rulings, scope, questions A–H in the binding order, Lean on one slot, severities, findings format |
| `dispatch.md` | "Needs from Seyoon's machine" (rule 16) and the prompt; postdates the records pin (`<RECORDS-G51>`) |
| `dup-sweep.md` | the maintainer's duplication sweep (S1–S11) |
| `source-head.json` | pins, the delivery commit, the 25 source commits, and every audited file with SHA-256, lines, width and `sorry` count |
| `SHA256SUMS` | over `pack.md`, `intake-r1.md`, `dup-sweep.md`, `source-head.json` (not this file or `dispatch.md`) |

No PDF, page image or source excerpt is in this folder (ruling Q12 (A)); the auditor reads the PDFs
from Seyoon's local folder. Findings come back in the chat as `findings-r1.md` and are filed here.
