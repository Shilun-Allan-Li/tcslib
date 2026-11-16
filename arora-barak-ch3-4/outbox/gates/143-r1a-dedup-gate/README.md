# 143-r1a-dedup-gate

The first Codex audit for draft PR #329 (gate 143): chapters 3–4 closeout refactor R1a, which retires the BW-1 and CH34-D4 duplication families by citing the existing public lemmas.
Read pack.md (after the standards). Deliver the findings as a downloadable file and paste them in chat.

| File | What |
|---|---|
| `gate143-r1a-dedup-bundle.md` | the bundle to attach: 20 sections (one per file, in `BUNDLE-FILES.txt` order), 2031581 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `5fdb37f19788596c722e977288b3455cd0dd9b553810b094eac28fbc6d579757`
- **Built by** `mkbundle-mixed.py`: the Lean files from `45d0ce546318188d7991ef65429138071b5c152a`, everything else from the
  campaign commit `4d9475bfccdddd640c5895923677d4348898b46d`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `20 segments, 0 problems`.
- **Findings:** the auditor delivers `gate143-r1a-dedup-findings.md` as an attachment in chat; committed as `campaign/gates/143/findings-dedup.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
