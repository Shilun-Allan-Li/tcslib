# 167-prog2-statements-gate

The Codex statement audit for (a5) PROG-2 (gate 167) on the RAM work branch: the signatures of Light with string input and output and coins (a mirror of the in-place edit to the vendored Light files), and the compiler deliverable: a Light run compiles to an extended-RAM program that HaltsWithin with the same output. No Lean PR; the mirror elaborates with 0 errors.
Read pack.md (after the standards). Deliver the findings as a downloadable file and paste them in chat.

| File | What |
|---|---|
| `gate167-prog2-statements-bundle.md` | the bundle to attach: 24 sections (one per file, in `BUNDLE-FILES.txt` order), 386490 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `371c55ad51f1a501bfef8a5913fc5bda0de6ae775385a845f249ced78d950ae2`
- **Built by** `mkbundle-mixed.py`: the Lean files from `de464c7f08a3c36a4bc0b908dd83e5660255f790`, everything else from the
  campaign commit `de464c7f08a3c36a4bc0b908dd83e5660255f790`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `24 segments, 0 problems`.
- **Export:** only the 24 listed paths, from the same two commits.
- **Findings:** the auditor delivers `gate167-prog2-statements-findings.md` as an attachment in chat; committed as `campaign/gates/167-prog2-statements/findings.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
