# 129-input-readers-r3-gate

Codex audit of gate 129 round 3 for PR #251.
The approved repair addresses the round 2 live-step and eraser findings.
The exact campaign Lean base is `ef98f1685ddfb8da40d8e97890c0fff6d145523b`. The merged-tree replay
passed all 395 modules. Begin with `campaign/gates/129-input-readers/pack-r3.md`.

| File | What |
|---|---|
| `129-input-readers-r3-bundle.md` | the bundle to attach: 26 sections (one per file, in `BUNDLE-FILES.txt` order), 21059989 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `e09465af2b3c1e475eb17d8897dab5f1eb8c0dc690b8ab67f20344d0634e509d`
- **Built by** `mkbundle-mixed.py`: the Lean files from `ead826bc6b1900c4209717aafc14244745106d7d`, everything else from the
  campaign commit `ed548f0aea280845a9aeda5096ecd9f79398d5b7`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `26 segments, 0 problems`.
- **Findings:** the auditor delivers `gate129-input-readers-r3-findings.md` as an attachment in chat; committed as `campaign/gates/129-input-readers/findings-r3.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
