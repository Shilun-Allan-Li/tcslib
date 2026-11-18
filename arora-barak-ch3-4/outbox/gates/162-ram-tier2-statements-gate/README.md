# 162-ram-tier2-statements-gate

The Codex statement audit for draft PR #372 (gate 162) on the RAM work branch: the public statements for tier 2 (the word RAM simulated by a Turing machine), namely word arithmetic rows, a keyed-table host, the input-bit row, and the simulation's internal interfaces (encoding, start-up, one phase per instruction), plus readers for the extended RAM. Five fill jobs will build on these statements in parallel, so the audit checks truth and sufficiency. Replay 88/88, seals and controls pass, no sweep flag, no new copy pairs.
Read pack.md (after the standards). Deliver the findings as a downloadable file and paste them in chat.

| File | What |
|---|---|
| `gate162-ram-tier2-statements-bundle.md` | the bundle to attach: 46 sections (one per file, in `BUNDLE-FILES.txt` order), 3458398 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `a3517e78a3bb1cfacc1b238783991816d3232fad218fc5a1a31df110eba4013a`
- **Built by** `mkbundle-mixed.py`: the Lean files from `e1325c96cf035f0ed6710443d89c3fcb6026a5c4`, everything else from the
  campaign commit `6164f5d1a50a38d0932baa4cef294226dcd37457`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `46 segments, 0 problems`.
- **Export:** only the 46 listed paths, from the same two commits.
- **Findings:** the auditor delivers `gate162-ram-tier2-statements-findings.md` as an attachment in chat; committed as `campaign/gates/162-ram-tier2-statements/findings.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
