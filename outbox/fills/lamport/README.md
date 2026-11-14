# Codex fill `lamport` (Theorem 137.2)

Codex is the worker (Seyoon, 2026-11-14). It works in a local checkout and pushes its deliveries to the exchange.
The job proves the admitted `lamport_oneTimeSecure` in `TCSlib/Cryptography/Authentication/Signatures/Lamport.lean` [PS10, Theorem 137.2]. The base is `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9` on
`cryptography/pass-shelat-ch2-4` (the merge of #299).

Read [the brief](brief.md) and the [environment addendum](fill-environment-addendum.md). Verify the package with
`shasum -a 256 -c SHA256SUMS` from this directory.

- [Build order](order.txt): 150 TCSlib modules. These are the upstream closure of the owned module, plus its
  downstream modules.
- [Mathlib roots](roots.txt): 82.
- [Source hashes](SOURCE-SHA256SUMS) at the issue base.
- [Base admissions](base-sorries.txt): 22 declarations in 12 modules. The only change must be the removal of
  the target.

Deliveries go to `inbox/fills/lamport/` on the exchange, with a final ZIP in the chat as a fallback. Seyoon dispatches.

**Ready to dispatch**
