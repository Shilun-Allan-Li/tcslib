# Gate 43 · resolutions, round 1 · CLEAR → CLOSED

Codex's verdict is **CLEAR for both pinned heads**: 0 blockers and 0 majors.
- **Findings:** `findings/gate43-gsw-fills-findings.md`, SHA-256
  `19ac93e02b412e1553e5706da43eac09c62be14537b82a4ed50c57767aab387e`.
- **Audited:** #339 (`gsw-core`) at `839f36cca9b4af0570c014f03f19858d0a03cbfb` (29 targets, 0 minors, 6 notes) and #338
  (`gsw-security`) at `d45d3682089cb6fd04f4d075f48a464fefaa143c` (6 targets, 2 minors, 4 notes); records `4ed91289`,
  exchange `14e681e6`.

Codex checked all 35 proofs on the routes Gate 41 accepted, in particular:
- `Encrypts.mul` with the exact `|x₁|·β₂` term, and `encrypts_chain`;
- `decrypt_of_encrypts` for odd `q` and for `q = 2, 3`, and the dyadic decoder;
- `eval_encrypts` via `runWith_rel`, and the exact leveled condition of `decrypt_keygen_eval`;
- F7's batch bijection, F5's column hybrid, and F6's four hybrids with `2Nε`.

Codex also found:
- every frozen header and its prose byte-identical;
- no undisclosed duplicate beyond the reviewers' findings;
- Rule 10 passing, with GC-05's reader route acceptable independently of the matcher limitation;
- citations consistent with the DW-7 transcriptions;
- the evidence complete, with GS-03 reconstructed.

No Lean change is needed for either PR.

| Finding | Grade | Disposition |
|---|---|---|
| GC-01 | note, disclosed debt | The site is already on DL-47 (records after the pin). Nothing more. |
| GC-02 | note | No existing public lemma has the Boolean integer identities. Nothing. |
| GC-03 | note | The REPORT overstates why `arrowCongr`/`curry`/`piComm` were unsuitable. Recorded; nothing on the branch. |
| GC-04 | note | Editorial only. Nothing. |
| GC-05 | note, Rule 10 passes | The matcher tooling note is filed in `briefs/pass-shelat-ch5-8/maintainer/tooling-followups.md` (records after the pin). |
| GC-06 | note | The evidence nits are confirmed; the provenance is adequate. Nothing. |
| GS-01 | note, **ruling pending** | Seyoon rules on the ledger debt and promotion P-1 (recommended: accept both). The ledger row is written after his ruling. |
| GS-02 | minor | The recorded erratum and the corrected P-1 in the gsw-security review stand. The `distAdv_comp` item is **not** an undisclosed re-proof (Codex §GS-02(c)): those steps prove acceptance-probability equalities through seed bijections. |
| GS-03 | minor, reconstructed | The missing one-line `CacheProbe.lean` reconstructs to the manifested SHA-256 `f8388ee6…`. The review already corrects the delivery-exactness claim. Nothing more. |
| GS-04 | note | Future fill briefs will ask workers to leave generated `.pyc` files out of deliveries. |
| GS-05 | note | The "base" seal label is imprecise; the final seals stand. Nothing. |
| GS-06 | note | A shared `Regev.augmentedEquiv` is added to DW-4 as a follow-up. |

The pre-existing missing registry entry for `[Vad12]` is a source-registration note. It is added to the DW-7 follow-ups.

**Gate 43 is closed.** The remaining merge conditions are maintainer items:
- GS-01's ruling, for #338;
- a combined build of #339 × #338 on the current tip (`201bf57a`, with #327 and #324). It is queued for the next free
  olean tree, together with #331's integration build, and expects admissions 229 → 194.

Once both are met, #339 and #338 are marked ready. They merge in either order.
