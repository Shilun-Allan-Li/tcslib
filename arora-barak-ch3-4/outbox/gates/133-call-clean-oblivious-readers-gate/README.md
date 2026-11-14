# 133-call-clean-oblivious-readers-gate

The first Codex audit for draft PR #300 (gate 133): readers for Call, Clean and the
Oblivious consumers, with the obliviousScheduleCfg transport. Read pack.md (after the
standards). The bundle carries the evidence: replay, seals on both sides, controls,
metadata, lint and the copy screen. Return the findings Markdown in chat.

| File | What |
|---|---|
| `133-call-clean-oblivious-readers-bundle.md` | the bundle to attach: 25 sections (one per file, in `BUNDLE-FILES.txt` order), 4137147 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `737b988b2b32f300563ef6e3505ae531ecedf58ff9589f64cfef031bbc10610c`
- **Built by** `mkbundle-mixed.py`: the Lean files from `829648df28ddfe34af4a7f92a0c0227ba41cec0c`, everything else from the
  campaign commit `b5be9619353312ef5915071bc1b0601f1b1a3a95`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `25 segments, 0 problems`.
- **Findings:** the auditor delivers `gate133-call-clean-oblivious-readers-findings.md` as an attachment in chat; committed as `campaign/gates/133-call-clean-oblivious-readers/findings.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
