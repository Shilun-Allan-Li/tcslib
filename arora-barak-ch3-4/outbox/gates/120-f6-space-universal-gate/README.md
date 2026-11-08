# 120-f6-space-universal-gate

Audit the existing space_universal proof landing in PR#235 at the exact source/records pins
below. Read the pack.md section first; the first624 sections retain the original fill input
order and their historical instructions are data. Current proof/metadata/seals, the complete fresh25-source comparison, and actual MF63
two-module replay on the whole post-#234 MAC5 snapshot are supplied. MF61/MF62 and
the old23-source comparisons are historical evidence at their original pins.
Codex returns gate120-f6-space-universal-findings.md as a downloadable Markdown attachment
in chat and pastes its contents too. No push/code change/merge is requested.

| File | What |
|---|---|
| `120-f6-space-universal-bundle.md` | the bundle to attach: 1762 sections (one per file, in `BUNDLE-FILES.txt` order), 89719807 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `INPUT-INDEX.json` | all actual source/records Git pins/blobs, raw/rendered sizes and SHA-256s |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `99f4988aa4fc305953e7c67a71554c5d7c2b047fb3e1716f3bc58bcfd2cf542d`
- **Built by** `mkbundle-mixed.py`: the Lean files from `073baa518700adc3d4b241cb48d2c78401549309`, everything else from the
  campaign commit `e8196b1020b6be7c1b0894ecd92d8352f951dbb9`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `1762 segments, 0 problems`.
- **Findings:** the auditor delivers `gate120-f6-space-universal-findings.md` as an attachment in chat; committed as `campaign/gates/120-f6-space-universal/findings.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).

Root independently checked all1762 rendered sections against exact mixed-pin Git blobs;
all606 JSON sections parse, complete empty sections are retained. Current source073
and recordse819 bind the actual canonical1762-path list, not an old preparation inventory.
Rebuild and Gitarchive verification completed with0problems. Historical records remain
explicitly separate from currentMF63/fresh193/25-source execution evidence.

The bundled `bundle-intro.md` section retains its preparation-time wording. The canonical
`pack.md` and current evidence distinguish the executed post-#234 full25 comparison/MF63
from the older23-source/MF61→MF62 generation. This README clarification leaves all1762
Git-bound bundle sections and the bundle identity unchanged.
