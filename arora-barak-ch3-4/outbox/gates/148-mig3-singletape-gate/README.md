# 148-mig3-singletape-gate

The first Codex audit for draft PR #337 (gate 148): chapters 3–4 closeout, wave R6, item MIG-3. `one_work_tape` is re-proved through the demand-grown witness that `one_work_tape_spaceUsed` already used (one private witness lemma), and the first sweep witness's run layer is deleted (net −444 lines, no statement changes).
Read pack.md (after the standards). Deliver the findings as a downloadable file and paste them in chat.

| File | What |
|---|---|
| `gate148-mig3-singletape-bundle.md` | the bundle to attach: 18 sections (one per file, in `BUNDLE-FILES.txt` order), 6244387 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `d036931e84e20a642c22ff1daaa357e75248e8b7b22faabde1cb81bf70ffa7de`
- **Built by** `mkbundle-mixed.py`: the Lean files from `fed2c719f935ff7f3c4875c7c680e534b4779c78`, everything else from the
  campaign commit `d922f9d52fdd43c6bbfa8760612155ad43cdc21e`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `18 segments, 0 problems`.
- **Findings:** the auditor delivers `gate148-mig3-singletape-findings.md` as an attachment in chat; committed as `campaign/gates/148-mig3-singletape/findings.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
