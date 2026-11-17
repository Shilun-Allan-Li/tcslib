# 157-w5-blueprint-r2-gate

The second Codex audit (light) for draft PR #361 (gate 157): the chapters 3–4 blueprint (W5). Round 1 returned HOLD (one major, two minors). This round checks the repairs: dz_kit_exists and qy_kit_exists now state their calls' bounds exactly as the Lean gives them (g-bounded input calls), exists_queryTM's title no longer says "linear", the Codec label headings match their bodies, and the orphan count is explained correctly against the pinned validator. No Lean change.
Read pack-r2.md (after the standards). Deliver the findings as a downloadable file and paste them in chat.

| File | What |
|---|---|
| `gate157-w5-blueprint-r2-bundle.md` | the bundle to attach: 108 sections (one per file, in `BUNDLE-FILES.txt` order), 3757399 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `b64bf5475056fb1139b0047fa538e63480ed8f174ec032911b1c501a2769929d`
- **Built by** `mkbundle-mixed.py`: the Lean files from `84e43bd7162c06cefd6581fb58a68ff71d96a37e`, everything else from the
  campaign commit `84e43bd7162c06cefd6581fb58a68ff71d96a37e`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `108 segments, 0 problems`.
- **Findings:** the auditor delivers `gate157-w5-blueprint-r2-findings.md` as an attachment in chat; committed as `campaign/gates/157-w5-blueprint/findings-r2.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
