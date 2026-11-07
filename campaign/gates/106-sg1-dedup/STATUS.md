# Gate 106: SG-1 (#215)

The user dispatched the immutable Codex packet pinned by `dispatch.json` / `prompt.md`.
Await the findings attachment; the issued bundle is unchanged.

After #222 merged, the **current-campaign full replay passes: 329 modules, 0 failures,
0 static mismatches**, chained from complete **oleans-mac2** into **oleans-msg3**.
The closure has 67 remaining admitted declarations (68 in the original replay, minus the
now-merged E-PAD proof). No admission change belongs to SG-1. Raw order, precheck, replay,
static check, source pins and receipt are in `evidence/current-after-natbits/`.

All four originally audited file blobs remain byte-identical. The current PR diff has three
Lean files because the identical Frag repair is already common through #222. Earlier source,
screen, seal, axiom and census evidence remains in `evidence/current/`: non-private compiled
census **293 → 293**, no name/kind/module-owner change; all six originally changed public
proof bodies have standard axioms. Earlier replays remain historical evidence.

**Not yet clear to merge: #215**; external gate 106 must close.
