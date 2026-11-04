# Abstract register machines: step equations and block embedding (PR #182, an API gate): resolutions

**Gate, round 1:** the API gate of PR #182 (`lean/arm-embed` at `8fd6f91a`). Pack `pack.md`.
**Ruled (user, 2026-11-04):** the general `savitch` reuses Hydroxyi's Savitch search unchanged through
a generic block embedding, instead of restating the search for any containing program. The lemmas
sit beside the definitions they read, in his `Machines` and `SavitchARM` files: additive, and FYI
only, the user's to send. The design is
`campaign/items/ch34/savitch-general/SAVITCH-deepening-design.md`. Bundle SHA-256
`e253274fec7dbdc422563b96b501f3208909763e07894ef06c89a85827567819` (90 sections), the Lean at
`8fd6f91a270f497a872146765cfab8422c3faf8e`, the records at `415fe4ee`. **Staged (2026-11-04); dispatched
(user, 2026-11-04).** Findings: pending.

**The replay:** `replay-larm.sh` (`evidence/merged-tree/`), 138 modules from `oleans-leqc3`, pinning
the five blobs; precheck passed. **Running** (user, 2026-11-04).
