# Gate 121 round 2 resolutions for #241

Round 1 held `d64dff4fbef865d815c6a561ce8037ea1bae07a2` on one major and one minor
(`findings.md`, SHA-256 `0c69519c40330cee311f245164a322cfe3cfdf7e55427b036a4271686b464404`).
The current PR head is `0f6f07eba0c2d91dbb082287f6479cb0962dc377`. It merges the
campaign after #251 (`4fff1ea826606070b86d0057052c20f3504b19e6`) and adds two
approved proof-only repairs. Seyoon selected Codex for this follow-up.

| Finding | Resolution |
| --- | --- |
| 1 · major · imported-definition reads | Repaired, not retained. The five idle donors (`clCopy_idle`, `clCmp_idle`, `clWipe_idle`, `clFresh_idle`, `clInput_idle`) and their same-kind stationary companions now read the step through `MultiTapeTM.step_of_some` (`46edaeef`, nine bodies); `clFresh_idle` and `clPrepared_idle` also read the right-hand seam state through the gate 131 reader `seamCompTM_tr_inr` (`0f6f07eb`). EXP's exposed `enumCont_absorb` uses `runFrom_zero` and `step_of_some` (`46edaeef`). `clA5Compare_compute` uses only existing published APIs (`5abe015a`) and the approved `CfgFacts` import (`9936345a`). `exists_inputLengthTM` reads its machine through the owner equations #251 published (`e2ccda50`). None of the seven named declarations contains `unfold MultiTapeTM.step` or another explicit foreign definition read at the head, and all 24 changed proofs pass whole-proof seals of every ordinary foreign definition they reach, with paired controls. |
| 2 · minor · component manifests | Fixed. The four original integrity files (`MANIFEST.json` and `SHA256SUMS.txt` of `review/evidence/compact-census/` and `review/evidence/nine-boundary/`) are bundle sections in this round, byte-identical to the frozen records and their `PATH-MAP.json` hashes. The originals are unchanged. |
| 3–9 · notes | Accepted within their stated scopes. The round 2 evidence replaces the source, replay, seal, lint and screen evidence those notes checked. |

Bounded scope. The round 1 census at `d64` (`campaign/items/dedup/fe-live1-repairs/stationary-nine/2026-11-08/census/`)
classifies 91 raw `MultiTapeTM.step` tokens in Hardness and EXP. At the head, 78 remain,
all in declarations this PR does not change (machine-specific transitions, frame and
simulation steps, and halted or live reads inside operational proofs). They keep their
census dispositions. This round neither retires that family nor asks to retain it.

## Round 2 result (2026-11-12)

Codex returned **HOLD (0 blockers, 0 majors, 1 minor, 7 notes)**, recorded verbatim as
`findings-r2.md` (SHA-256 `3eb556933eee0a8ae0ed7b974065e0ec20387fec17ea9d440d0f24335b7229ec`). Round 1's major 1 and minor 2 are resolved (notes 2 and 3).

| Finding | Disposition |
| --- | --- |
| 1 · minor · copy-screen inputs incompletely packaged | **Fixed in records.** `r2-evidence/SCREEN-INPUTS-CARRIER-r2.json` holds all 33 population files at BASE `4fff1ea8` and HEAD `0f6f07eb` (66 captures; 39 unique blobs) and the scorer `scripts/copy-text-screen-v3.py` (SHA-256 `f4feac91d3a1ec036f3bbcaafde83e6855a1bf1a62d31dac31a40a40d878f181`). `SCREEN-INPUTS-BINDING-r2.json` binds each capture to its Git blob, SHA-256 and byte count, and records the invocation; carrier SHA-256 `d97ce1d618ad72ad974aba12dba8e5e636ad99400c3a2f930a57ba53f2cc13af`. Each capture equals the export the screens ran on. The issued round 2 files are unchanged. No Lean change. |
| 2–8 · notes | Accepted within their stated scopes. Note 2's limit stands: the 78 raw step tokens in 52 unchanged declarations are not cleared by this gate. |

With 0 blockers and 0 majors and the minor fixed, **gate 121 is closed.**
