# 152-cc7-1-legs-gate

The first Codex audit for draft PR #345 (gate 152): chapters 3–4 closeout, wave R3, family CC7-1 in `TuringMachine/CodeSimulator`. The seven stage-front legs now go through one private leg template (with a guard helper and a head-move helper), and the two twin strict-cut lemmas cite one private `phaseCut_leg`. All private, statements unchanged, net −212 lines.
Read pack.md (after the standards). Deliver the findings as a downloadable file and paste them in chat.

| File | What |
|---|---|
| `gate152-cc7-1-legs-bundle.md` | the bundle to attach: 19 sections (one per file, in `BUNDLE-FILES.txt` order), 2760241 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `3bb2a05e5067b2c68a6da06d1836e3f387321337408067e4be0dbd65e2d517f3`
- **Built by** `mkbundle-mixed.py`: the Lean files from `1dcbbe3171dd685600525d4f7cf71548889ecceb`, everything else from the
  campaign commit `3709738aa20ed40165b54f59c47d4ebc9e107876`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `19 segments, 0 problems`.
- **Findings:** the auditor delivers `gate152-cc7-1-legs-findings.md` as an attachment in chat; committed as `campaign/gates/152-cc7-1-legs/findings.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
