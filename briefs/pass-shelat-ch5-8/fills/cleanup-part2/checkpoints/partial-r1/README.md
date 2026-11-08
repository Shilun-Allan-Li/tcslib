# Cleanup final-PARTIAL delivery: immutable intake

Claude pushed `0c4d4f60203021f3a3b93f88eaf7c9085c6ab885` on exchange/pass-shelat-ch5-8,
under the assigned inbox/fills/cleanup-part2/ subtree. The 30-minute watch detected
it at 2026-11-08T10:56:08Z. The commit is named final; its report explicitly says
FINAL DELIVERY — PARTIAL, not final-complete. No completion is inferred.

The archive is the maintainer's Git archive of that immutable subtree, not a
worker-uploaded ZIP. REPORT.md and PAYLOAD-SHA256SUMS are copied verbatim.
files.json binds every Git blob/mode, size and SHA-256; supplied checksums match
after ordinary ./ normalization. All 221 owned source snapshots are present,
without an outside-owned snapshot. Executable-mode files are retained as data.

- 3,936 files; 49,015,725 raw bytes.
- Archive SHA-256: `5e814a991ae91447b6aa18d92e3d65d8c78e8c76cef93769a5f3c37a570393ac`.
- REPORT SHA-256: `dca5f8e5961b83b402a6255ff4afd4273a555e3d04a9f1fb391fa15acdb8b57e`.
- Worker claims source head `03ead73ab38e74621800367c072f6fd3f0f70991`,
  thirteen whole patches, 122 changed source paths, 26 provider-only insertions.
- Worker reports 173/509 keys and 152/764 historical rows still open, plus
  further failing declarations, E-API and E-FREEZE. These counts and all native,
  seal/control/census/disposition claims require independent review.

Independent source/freeze, workflow/evidence and API/frontier reviews are archived in [review-r1](review-r1/README.md),
using the snapshot rather than mutable exchange files. No incoming program has
been executed, no source applied, no new external job dispatched, and no ruling
or merge clearance is granted by intake. The CP1 local API follow-up remains a
separate checked local commit; it is not implicitly in this worker payload.

The later [checked maintainer repairs](checked-repairs-r1/README.md) are separate
from this immutable intake. Their124-module closure and ten selected axiom checks
pass; full cleanup and seal acceptance remain open.

**Not yet clear to merge — partial delivery reviewed and local repairs checked; full acceptance remains open.**
