# Current gate 116 context after NatBits

**No regression found.** All refreshed source, screen, metadata, axiom, seal and control checks
passed in this context. This is internal maintainer evidence, not external gate closure or
permission to merge. The existing primary pack and all earlier evidence are preserved.

- Current campaign base: `3555163f40d9c101a2ef4e81407c1bda58fe5ca4`.
- Parent's generated/pushed consumer head: `74494d669ad9f8f926844f9280812449f57263d6`.
- Reviewed Hierarchy source SHA-256: `1d7e0c7d706521991a623dfe6963650f867edfebe34c2dae8316e2078dc8069f`.
- Snapshot context: base **oleans-mac2**, head **oleans-mlin2**.

The parent replay completed **2 modules, 0 failed** before these metadata/seal checks started.
`parent-replay.log` is its copied log; its receipt pins the generation file and content hash.
This reviewer did not run that replay and does not independently claim its static-check result.

## Source pins and scope

Both eleven-file populations are fresh Git archives of the two commits above. Only Hierarchy
differs between these base/head source populations. `source-receipt.json` records both Git blobs
and both SHA-256 values for every file. Complete sources are provided under `base-source/` and
`head-source/`, with `.lean.txt` suffixes. Current Hierarchy source text on each side is identical
to its counterpart in the initial review, so its complete-header/import/visibility/order freeze
and source-level lint conclusions remain applicable by exact text identity. No fresh lint run
is claimed here.

The unchanged source census is **4 public / 43 private declarations**, with only the existing
`SPACE_linear_ne_NP` proof filled and the approved Padding import added. Headers and visibility
are frozen; every other declaration's complete text is identical. Source admissions remain
**2 → 1**, leaving F6's independent `space_universal` admission. That remaining admission is not
an axiom dependency of the newly proved separation.

Relative to the earlier pre-NatBits common base, this population's **Encoding and Constructible**
context files changed through the already-merged NatBits PR. Their fresh source contents, rather
than the earlier exports, are what both current screens and the current snapshots use. Source
identity of the target alone is not substituted for the fresh import-context checks.

## Fresh results

| Check | Current result |
|---|---|
| Non-private compiled census | **4 → 5**, retaining every internal/generated constant |
| Complete compiled census | **137 → 138**, including **133 private constants on each side** |
| Sole addition | Internal theorem `Complexity.SPACE_linear_ne_NP._proof_1_1`; no removed/renamed/moved constant |
| Target axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Auxiliary axioms | `propext`, `Quot.sound` |
| Direct foreign inventory | Exactly **NP, SPACE, padLang, pairEncode**; all four sealed, zero exclusions |
| Current default-simp definition inventory | Action.apply, Cfg.init, MultiTapeTM.initCfg, NDTM.initCfg; all four removed in the strong source seal |
| Strong new-section seal | Exit 0, zero errors; only the unchanged F6 admission warning |
| Positive controls | Four pointwise plus four parameter-abstracted equations close, exit 0 |
| Negative controls | The same eight equations fail sealed, exit 1; exactly one error at each expected line, no extras |
| Copy-text screen | **247 → 248 eligible bodies**, **31 → 31 directional pairs**, **5,917 → 5,917 reproduced characters** |
| Pair delta | **0 new, 0 removed**; candidate measurements also equal the earlier context's pair population |

The two screens ran serially under the shared screen lock and released it. Their eligible-body
counts differ from the initial 249 → 250 because of the two changed common-context sources; this
is not a change to Hierarchy's source declaration census. The newly proved target is the one new
eligible body in the current head and is in no candidate pair.

`Inventory.lean.txt` accurately scopes the target and its sole compiler auxiliary.
`constant-delta.json` and `all-constant-delta.json` reconcile both census views.
`control-check.json` verifies exact diagnostic-line **multiplicities** and expected exits.
`results.json` records the aggregate checks; each raw run has a separate JSON receipt and output.
The new-region seal is not a seal of the unchanged legacy Hierarchy proofs.

No new source-fidelity, interface, reuse or debt issue was found. The semantic classification is
in `classification.md`; it does not grant a new acknowledgment of any legacy debt. No Git
mutation, source edit, primary-pack edit, cache operation, `lake build` or bare Lean command was
performed. Lean runs were one at a time through leanelab. Reassess this evidence against any later
campaign change before publication/merge; these receipts certify only the pinned context above.
