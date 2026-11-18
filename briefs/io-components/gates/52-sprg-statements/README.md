# Gate 52 · io-sprg statements gate (checkpoint 0)

**Status: staged, not dispatched** (2026-11-18). Static staging; no Lean was run.

The Codex statements gate on the io-sprg job's checkpoint 0: exchange
`15946b52d0615fda8afad9ed3c57cfaf5beaaa8d` (`inbox/fills/io-sprg/`), source HEAD
`d10a560b34d58919bc1a5206ce66a444613f94c7`, base `iO/phase-a-base` at
`5ed465f62e4ae0f93ded1a1ba49e807591b589eb`, job records pin
`dbea2807532392781304e004715f3b0190025f5e`. The job's pack is `../../sprg/`.

| File | What |
|---|---|
| `intake-r1.md` | maintainer's static intake of checkpoint 0: integrity, contents, fidelity spot-check against JLS26, rule 15 (no analogue of Gate 51 F01), duplication, process; findings SPRG-C0-F01..F17 (0 blockers, 1 major, 7 minor, 9 notes); questions Q-G52-1..6 for Seyoon |
| `pack.md` | the gate's task for Codex: pins, local source, rulings, scope, questions A–H in the binding order (Def 3.3 / Thm 4.1 fidelity, then rule 15), Lean on one slot, severities, findings format |
| `dispatch.md` | "Needs from Seyoon's machine" (rule 16) and the prompt; postdates the records pin (`5464995aa000882f6bd41a3bb2f4f0d1a1486d67`) |
| `dup-sweep.md` | the maintainer's duplication sweep (S1–S11) |
| `source-head.json` | pins, the delivery commit, the 15 source commits, the bundle, and every audited file with SHA-256, lines, width and `sorry` count |
| `SHA256SUMS` | over `pack.md`, `intake-r1.md`, `dup-sweep.md`, `source-head.json` (not this file or `dispatch.md`) |

No PDF, page image or source excerpt is in this folder (ruling Q12 (A)); the auditor reads
`jls26.pdf` from Seyoon's local folder. Lean: at most one slot (`lean-slot.sh`, tag `g52-sprg`),
waiting while Gate 51 holds the third. Findings come back in the chat as `findings-r1.md` and are
filed here.
