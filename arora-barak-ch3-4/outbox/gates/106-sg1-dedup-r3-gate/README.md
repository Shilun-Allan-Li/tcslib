# 106-sg1-dedup-r3-gate

Audit PR#215 gate106 round3 at the exact source and records pins below.
Read pack-r3.md first; distinguish original reports, historical candidate/preparation records
and current final-source evidence. All TCSlib root sections use the final proof pin.
Codex returns sg1-dedup-r3-findings.md as a downloadable Markdown attachment in chat, with its
contents pasted too. No push or code change is requested. All validation is evidence to audit,
not gate closure.

| File | What |
|---|---|
| `106-sg1-dedup-r3-bundle.md` | the bundle to attach: 1614 sections (one per file, in `BUNDLE-FILES.txt` order), 100861434 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `INPUT-INDEX.json` | every actual section’s full Git pin/blob, raw/rendered bytes and SHA-256 |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `104d4805fc8e1b53fdc8aa1e8ac7e611b09034398f46887fdc0be4d4e7aeb5d8`
- **Built by** `mkbundle-mixed.py`: the Lean files from `79e7c63a6bfa5f002663924f5c7d4e72db705026`, everything else from the
  campaign commit `f07808363a5fc839de9cdb1c90e05158826bbf57`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `1614 segments, 0 problems`.
- **Findings:** the auditor delivers `sg1-dedup-r3-findings.md` as an attachment in chat; committed as `campaign/gates/106-sg1-dedup/findings-r3.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).

Independent root verification matches all1614 sections to the exact mixed-pin Git blobs;
all521 JSON sections parse. Rebuild and Git-archive verification report0problems. All
TCSlib root sections use final proof79; historical baseline captures/inventories remain
separate. The complete input index is co-published and checksummed; no folder cap applies.
