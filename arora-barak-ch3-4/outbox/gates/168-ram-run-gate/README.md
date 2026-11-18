# 168-ram-run-gate

The Codex audit for draft PR #383 (gate 168) on the RAM work branch: tier 2 job E, the stage-2 simulation. WordRAM.exists_simulation and exists_ndSimulation are proved from the three Sim interface statements in 17 new Sim/Run* modules (public in the internal namespace WordRAM.Sim), with four pure readers. Replay 286/286, seals pass, no sweep flag, 15 new copy pairs classified (one shared prelude raised for your judgment).
Read pack.md (after the standards). Deliver the findings as a downloadable file and paste them in chat.

| File | What |
|---|---|
| `gate168-ram-run-bundle.md` | the bundle to attach: 47 sections (one per file, in `BUNDLE-FILES.txt` order), 8761785 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `1988867bfa4a92c61b24d60de3120ddf75e3b5f3d1ce5dae0f3706555e30bc6b`
- **Built by** `mkbundle-mixed.py`: the Lean files from `a6199066dcefcc0ab5cbf6d424693bba0cc4cae0`, everything else from the
  campaign commit `fd74fff2d3b4a129f2d07efe821b9698b710a812`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `47 segments, 0 problems`.
- **Export:** only the 47 listed paths, from the same two commits.
- **Findings:** the auditor delivers `gate168-ram-run-findings.md` as an attachment in chat; committed as `campaign/gates/168-ram-run/findings.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
