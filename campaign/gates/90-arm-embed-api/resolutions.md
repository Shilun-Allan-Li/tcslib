# Abstract register machines: step equations and block embedding (PR #182, an API gate): resolutions

**Gate, round 1:** the API gate of PR #182 (`lean/arm-embed` at `8fd6f91a`). Pack `pack.md`.
**Ruled (user, 2026-11-04):** the general `savitch` reuses Hydroxyi's Savitch search unchanged through
a generic block embedding, instead of restating the search for any containing program. The lemmas
sit beside the definitions they read, in his `Machines` and `SavitchARM` files: additive, and FYI
only, the user's to send. The design is
`campaign/items/ch34/savitch-general/SAVITCH-deepening-design.md`. **Staged (2026-11-04)**; not yet
dispatched. Findings: pending.

**The replay:** `replay-larm.sh` (`evidence/merged-tree/`), 138 modules from `oleans-leqc3`, pinning
the five blobs; precheck passed. Not yet run.
