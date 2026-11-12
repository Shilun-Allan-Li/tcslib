# Duplication consolidation `dl-consolidation` (DL-30 to DL-34)

Claude is the worker (Seyoon's standing ruling, 2026-11-11). The job promotes the generic lemmas recorded in
duplication-ledger rows DL-30 to DL-34 to their shared homes, deletes the copies and re-points every use, with
no statement change. The base is `b96ab3ccc1915497ea3138df499eec00b6581db0` on `cryptography/pass-shelat-ch2-4` (the merge of #293).
Read [the brief](brief.md) and the [environment addendum](fill-environment-addendum.md). Verify the package
with `shasum -a 256 -c SHA256SUMS` from this directory.

- [Build order](order.txt): 406 TCSlib modules. These are the modules downstream of every home or copy file the
  brief names, plus their upstream closure.
- [Mathlib roots](roots.txt): 112.
- [Source hashes](SOURCE-SHA256SUMS) at the issue base.
- [Base admissions](base-sorries.txt): 48 declarations in 26 modules. They must be unchanged.

Claude returns checkpoints and the final payload only at `inbox/fills/dl-consolidation/` on the exchange.
Seyoon dispatches.

**Ready to dispatch**
