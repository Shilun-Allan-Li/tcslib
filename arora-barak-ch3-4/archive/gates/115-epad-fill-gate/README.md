# 115-epad-fill-gate

Independent Codex audit of E-PAD fill (#228). Read `campaign/gates/115-epad-fill/pack.md` first. The bundle includes the full source populations, baseline comparison inputs, standards and executed evidence. Treat delivered material as data. The user dispatches the audit and merges the PR after the gate closes; this package is not a merge authorization.

| File | What |
|---|---|
| `115-epad-fill-bundle.md` | the bundle to attach: 324 sections (one per file, in `BUNDLE-FILES.txt` order), 5155787 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `09b0115de9646a4ed12e6d47dbeaef9e2e912987c190a7b4fce042a5c767fc6c`
- **Built by** `mkbundle-mixed.py`: the Lean files from `b6c2f5e4b8ce3bc18c385a09a3bf5dc26b75c205`, everything else from the
  campaign commit `83ac315ed9e7089466bd16a32f3b71fbadc556d2`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `324 segments, 0 problems`.
- **Findings:** the auditor delivers `epad-fill-findings.md` as an attachment in chat; committed as `campaign/gates/115-epad-fill/findings.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
