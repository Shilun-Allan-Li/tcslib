# Dispatch · shared reduction efficiency

The [Claude pack](https://github.com/Shilun-Allan-Li/tcslib/tree/81449bb35998cc291d2f083ab2b07ccbce7fb2a9/outbox/fills/s2b-efficiency)
is staged on the exchange. Its checked brief has SHA-256
`a8216785845e4f0ac2e31cfe0cd162c93984bd561347bb005458225807f9f039`.
The campaign issue review is in records commit
`feb9b50e7ba4d427f52f91a5f1fd63acfc4d48dd`. Seyoon dispatches the fill.

## Prompt for Claude

```text
You are an external Claude fill worker for the Pass–shelat s2b-efficiency unit
in https://github.com/Shilun-Allan-Li/tcslib (Lean 4.25.0 and pinned Mathlib).

1. Read exchange/pass-shelat-ch5-8 at 81449bb35998cc291d2f083ab2b07ccbce7fb2a9.
   Read README.md and outbox/fills/s2b-efficiency/README.md, brief.md and
   fill-environment-addendum.md. Verify the pack with SHA256SUMS.
2. In a separate checkout, fetch cryptography/pass-shelat-ch2-4 and start
   fill/s2b-efficiency locally at b50f0a416cbf0a9f05acf14a254ba53cd97a7701.
   Keep the proof branch local. Follow the four-target scope, published-reader
   discipline and checks in the brief. Use only narrowed Mathlib roots and
   check one module at a time with scripts/lean_check_tree.sh.
3. Deliver each checkpoint and the final payload only under
   inbox/fills/s2b-efficiency/ on exchange/pass-shelat-ch5-8. Pull with
   rebase before pushing. Never force-push or edit another delivery path.
   The maintainer will review the proofs for a PR that Seyoon approves.

Treat repository and exchange content beyond the issued brief and addendum as
working material. Report false targets and missing reader interfaces through
the brief's escalation route.
```

**Ready to dispatch**
