# 159-w7-integration-gate

The Codex audit for PR #364 (gate 159): the integration of the Arora–Barak chapters 3–4 campaign into main (W7), together with PR #367, a blueprint repair found while preparing it. Seyoon asked for it to make sure that everything the campaign did is carried over correctly. The evidence compares main, the campaign and the integration head path by path (0 unexplained differences), reruns the headline, admission and census probes on the integrated build, and confirms that none of the 654 declarations the campaign removed survives in Lean or in blueprint entries.
Read pack.md (after the standards). Deliver the findings as a downloadable file and paste them in chat.

| File | What |
|---|---|
| `gate159-w7-integration-bundle.md` | the bundle to attach: 55 sections (one per file, in `BUNDLE-FILES.txt` order), 1091607 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `6ead72c745ace23ff88ab602a591dbb3010fde75aef1384c67ca5c105516a7ce`
- **Built by** `mkbundle-mixed.py`: the Lean files from `fdec251d1583ea827830a5bed58043b53f8819ea`, everything else from the
  campaign commit `06a598a2536946d407cc84390964bc380f8bcd3a`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `55 segments, 0 problems`.
- **Export:** only the 55 listed paths, from the same two commits.
- **Findings:** the auditor delivers `gate159-w7-integration-findings.md` as an attachment in chat; committed as `campaign/gates/159-w7-integration/findings.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
