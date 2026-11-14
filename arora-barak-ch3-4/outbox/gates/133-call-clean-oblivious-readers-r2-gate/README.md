# 133-call-clean-oblivious-readers-r2-gate

The second Codex audit for draft PR #300 (gate 133): the repair of G133-01 (`dataTM_ready`
reads the transport through its reader) and the corrected base comparison (G133-02), on fresh
evidence after #301. Read pack-r2.md (after the standards). Return the findings Markdown in chat.

| File | What |
|---|---|
| `133-call-clean-oblivious-readers-r2-bundle.md` | the bundle to attach: 28 sections (one per file, in `BUNDLE-FILES.txt` order), 4221501 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `e43b1ded40887ea32262afbf646d6e2e53b98266f43578d7dc3f904635ac32fd`
- **Built by** `mkbundle-mixed.py`: the Lean files from `4ddce70c45e0a397fbc4d9a25ac925da80e05cda`, everything else from the
  campaign commit `49041641de24f9472f68e87196a6eea76f9ed4e1`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `28 segments, 0 problems`.
- **Findings:** the auditor delivers `gate133-call-clean-oblivious-readers-r2-findings.md` as an attachment in chat; committed as `campaign/gates/133-call-clean-oblivious-readers/findings-r2.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
