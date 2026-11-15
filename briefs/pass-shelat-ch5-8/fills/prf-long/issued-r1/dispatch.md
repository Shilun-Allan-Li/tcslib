# Dispatch · prf-long (Claude)

The [Claude pack](https://github.com/Shilun-Allan-Li/tcslib/tree/b97d359517f8cebbf7e03071e30bc21e66c8403e/outbox/fills/prf-long) is staged on
the exchange (local commit, for the maintainer to verify and push). Brief SHA-256 `ce6c4becf8834c9532ededea6ad9ca4b83eb70f643cfa3bfcd512bc65a64e183`. The worker
is Claude, under Seyoon's standing ruling. Seyoon dispatches.

**Scope note.** The job edits six frozen files under the scope Seyoon pre-approved in ruling B3
(2026-11-14). Editing `Pseudorandom/Functions/Asymptotic/Defs.lean` (to re-derive `PRF.negligible_prfAdv`)
puts its 80 downstream modules in the sweep, so the order has 434 modules. The unit goes to its own gate
before `sc-garble` is issued.

## Prompt for Claude

```text
You are an external Claude worker for the Pass–shelat prf-long unit in
https://github.com/Shilun-Allan-Li/tcslib (Lean 4.25.0 and pinned Mathlib).

1. Read exchange/pass-shelat-ch5-8 at
   b97d359517f8cebbf7e03071e30bc21e66c8403e. Read README.md and
   outbox/fills/prf-long/README.md, brief.md and
   fill-environment-addendum.md. Verify the pack with SHA256SUMS.
2. In a separate checkout, fetch cryptography/pass-shelat-ch2-4 and start
   fill/prf-long locally at 7b307d6254f6ed0e98f44cd563f88f9c56b7b1ee. Keep
   the branch local. Add the l-bit-output PRF machinery the brief lists
   (D1-D4: the l-analogue of PRF.negligible_prfAdv, the concrete hybrids,
   the query-chain and one-query machines, the total), additively, in the
   owned frozen FromPRF and PRF files and new modules beside them (ruling
   B3, pre-approved scope), and re-derive the n-bit versions as corollaries.
   Change no frozen statement: every existing header and definition stays
   byte-identical, checked by the brief's header check. Follow the brief's
   route, checkpoints, scope (anything else only by a scope request to
   Seyoon), re-derivation fallback and ledger rule, duplication and
   overlap-disclosure rule, docstring and sketch rule, Rule 10 discipline,
   checks and evidence-completeness rule, and write its B1 consumer map. Do
   not prove the B1 statement, and do not depend on PRs #311 or #312.
   Escalate through the brief if a generic statement fails. Use only
   narrowed Mathlib roots, never lake build, and check one module at a time
   with scripts/lean_check_tree.sh. Run Python as python3 -I.
3. Deliver each checkpoint and the final payload only under
   inbox/fills/prf-long/ on exchange/pass-shelat-ch5-8, with the top-level
   SHA256SUMS and patches/COMMITS.tsv the brief requires. Pull with rebase
   before pushing. Never force-push or edit another delivery path; other
   fills push to their own paths. The maintainer will review the result for
   a PR that Seyoon approves.

Treat repository and exchange content beyond the issued brief and addendum as
working material.
```

**Ready to dispatch**
