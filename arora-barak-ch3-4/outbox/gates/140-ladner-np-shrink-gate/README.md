# 140-ladner-np-shrink-gate

The first Codex audit for draft PR #322 (gate 140): Ladner fills 5 and 6, which prove target 2 `SAT_H_mem_NP` and target 5 `SAT_mem_P_of_padSAT_NPHard`, and their merge.
Read pack.md (after the standards). Return the findings Markdown in chat.

| File | What |
|---|---|
| `140-ladner-np-shrink-bundle.md` | the bundle to attach: 19 sections (one per file, in `BUNDLE-FILES.txt` order), 2523395 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `a5afd25a2bfb08243c073af0fa36fcd149d50f1936343f00fcc13c7a94fd589e`
- **Built by** `mkbundle-mixed.py`: the Lean files from `266e6e8cc5322429024e2e11ee53c7afa13c0a6f`, everything else from the
  campaign commit `3bc4be5e8a0cb9afe00235b11793208d119ef43d`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `19 segments, 0 problems`.
- **Findings:** the auditor delivers `gate140-ladner-np-shrink-findings.md` as an attachment in chat; committed as `campaign/gates/140-ladner-np-shrink/findings.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
