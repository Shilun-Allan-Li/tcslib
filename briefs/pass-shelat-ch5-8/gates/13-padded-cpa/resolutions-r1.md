# Gate 13 · resolutions, round 1

**Status: CLOSED** (0 blockers, 0 majors, 0 minors, 0 notes). Auditor Codex, 2026-11-11; findings
uploaded by Seyoon and filed verbatim in [findings/](findings/gate13-padded-cpa-findings.md)
(SHA-256 `871c41ba4d5359fb9e4c50c81d2854ce6c68c5fea5bd56c61a0cebb50d821f5f`).

| Input | Pin |
|---|---|
| Exchange pack | `35ea3015a726096b19e1852b58114991ba332be9` |
| PR #288 Lean head | `892a3f3c78abcde8bdf822a3b4168ab3302b4272` |
| Records | `f6b8de11291e56858eeb76990d53469cacc3f852` |
| PR base | `2950c4a74c45b98185a5eaf4601cf8b88a7528c2` (Lean `ed0f7238`) |

The auditor verified all pack, bundle, source and archive hashes, the statement freeze, the proof
(eager coins, first-challenge congruence, the recording handler and T1 coin transport, the exact
signed advantage identity and boundary cases), the seal and control evidence, and the landing
edits, and bound both build logs to the pinned head's source hashes. It did not recompile; the
compiler and axiom results are verified recorded evidence. DL-30 and DL-31 remain recorded
follow-up work.

**Clear to merge** — #288 at `892a3f3c78abcde8bdf822a3b4168ab3302b4272`.
