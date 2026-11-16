# Codex audit · Gate 43 GSW fills (#339 gsw-core and #338 gsw-security, audited together)

Audit draft PR #339 (gsw-core: gadget, noise algebra, public- and secret-key GSW, circuit evaluation; 29 targets) at
839f36cca9b4af0570c014f03f19858d0a03cbfb and draft PR #338 (gsw-security: the column leftover-hash hybrid and IND-CPA of
public-key GSW; 6 targets) at d45d3682089cb6fd04f4d075f48a464fefaa143c, using the scope in pack.md: a **proof audit** of the
35 frozen GSW targets of phase 5 of the lattice campaign, whose statements Gate 41 accepted. Campaign records are
pinned at 4ed91289d6132f71ace06b3d9fd87539956d6a88.

**Gate number.** Gate 42 is reserved for sc-yao (Pass-shelat campaign). The phase-6 plan
(`briefs/lattice-gsw/phase6/plan-section.md`) uses 42 and 43 as provisional numbers for its two statement gates; those
will be renumbered later. This gate, 43, is the phase-5 fill gate.

The bundle contains the pack, policy, the two delivery reviews, the two worker REPORTs (from their final exchange
commits), the two issued briefs, the GSW rulings, Gate 41's resolutions and findings, the duplication ledger, the DW-7
scoped transcriptions of [GSW13], [AP14], [BV14] and [Pei16], and the 7 changed Lean files at their heads.

Also:
- pr-339.diff.txt and pr-338.diff.txt: the full diff of each PR from its merge base with the records tip to its head;
- source-head.json: the heads, bases, hashes, line counts and over-width counts of the 7 changed files;
- sources.zip: for each PR, the import closure at its head of its changed files (25 + 25 files), under the prefixes
  pr-339-gsw-core/ and pr-338-gsw-security/ (the heads differ in the shared closure: at #338's head gsw-core's files
  are still sorried);
- verification.zip: the two review evidence ZIPs with their manifests, byte copies of the entries the pack cites, the
  worker REPORTs, manifests and patches, the cited records, the DW-7 transcriptions, context files for the duplication
  questions, the PR descriptions and the pack's git-object re-checks with their scripts (pack-checks/); its entries
  are exactly its SHA256SUMS plus SHA256SUMS.

The workers' own evidence is on this branch under inbox/fills/gsw-core/ (final commit 9e52a5019258c51d67b1f28d3675c66cf787209b) and
inbox/fills/gsw-security/ (final commit 5857e850e7f7daf264d2860caf27341e3052f8c5).

Check SHA256SUMS before using the pack.

Return gate43-gsw-fills-findings.md as Markdown in the chat, with findings marked by PR. If you have several evidence files,
return a ZIP containing that Markdown and the evidence. The user dispatches and merges.
