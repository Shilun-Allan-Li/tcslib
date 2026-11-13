# Post-consolidation folds `dl-folds` (DL-36 and DL-37)

Claude is the worker (Seyoon's standing ruling, 2026-11-11). The job repays duplication-ledger rows DL-36 (the
nm-cca2 fill) and DL-37 (the nm-sim fill), and promotes the generic lemmas that those fills' reviews accepted. It
deletes the copies and re-points every use, with no statement change. The base is
`d3f2290a2c66f614e8807903b89ac595086578b3` on `cryptography/pass-shelat-ch2-4` (the merge of #298, the DL-30–DL-34
consolidation).

Read [the brief](brief.md) and the [environment addendum](fill-environment-addendum.md). Verify the package with
`shasum -a 256 -c SHA256SUMS` from this directory.

- [Build order](order.txt): 421 TCSlib modules. These are the modules downstream of every home or copy file the
  brief names, plus their upstream closure.
- [Mathlib roots](roots.txt): 112.
- [Source hashes](SOURCE-SHA256SUMS) at the issue base.
- [Base admissions](base-sorries.txt): 45 declarations in 24 modules. They must be unchanged.

Claude returns checkpoints and the final payload only at `inbox/fills/dl-folds/` on the exchange. Seyoon
dispatches.

**Ready to dispatch**
