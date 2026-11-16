# 145-r4-1-transducer-gate

The first Codex audit for draft PR #334 (gate 145): chapters 3–4 closeout refactor R4-1. It retires the SAT/Hardness one-way transducer copies (SG1 kind 4, its riders and PL-1's twins) by extending `ClassNP/Transducer` with a final-emission machine.
Read pack.md (after the standards). Deliver the findings as a downloadable file and paste them in chat.

| File | What |
|---|---|
| `gate145-r4-1-transducer-bundle.md` | the bundle to attach: 20 sections (one per file, in `BUNDLE-FILES.txt` order), 3551144 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `f0851a47cb125a502d96c8ab47995fd141089f2b9d0cb531d5177cddc5db7c50`
- **Built by** `mkbundle-mixed.py`: the Lean files from `7bb1f687d87c8faa25c8523fc4bb1e15a5d473c1`, everything else from the
  campaign commit `533f741f03b54d989fe86fdb43a197aac697e198`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `20 segments, 0 problems`.
- **Findings:** the auditor delivers `gate145-r4-1-transducer-findings.md` as an attachment in chat; committed as `campaign/gates/145/findings-transducer.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
