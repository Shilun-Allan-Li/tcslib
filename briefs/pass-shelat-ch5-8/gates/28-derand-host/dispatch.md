# Dispatch · Gate 28

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/2776272b61fcc7a1adf3f743c735c7e45be5045c/outbox/gates/28-derand-host-gate)
is staged on the exchange. Seyoon dispatches.

## Prompt for Codex

```text
You are an external Codex auditor for Pass–shelat Gate 28 in
https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at 2776272b61fcc7a1adf3f743c735c7e45be5045c.
   Read outbox/gates/28-derand-host-gate/README.md, pack.md and bundle.md.
   Verify the pack using SHA256SUMS.
2. Audit draft PR #312 at Lean head 8972fb4ef15fa3d4e3df37d6aa8674408835593d,
   with campaign records 1ea6503c82b12fd7e49c2e621fcae4cd29d9d08c, using the pack.
   This is a statement audit of the sorried host contract
   Complexity.seedMajority_mem_DTIME (strict majority over all seeds of a
   P test on pairEncode x u, in DTIME(2^{w(n)}·(n+1)^e)) and its reader
   Randomized.half_lt_randProb_iff: its truth (ties, w = 0, small n), its
   sufficiency for bpp_subset_dtime_subexp [PS10, Theorem 180.1] via the
   paper proof in pr-body.md, its generality, its placement in the shared
   layer under policy §1 (Hosts come first), Rule 10, and the stated route.
3. Return gate28-derand-host-findings.md as Markdown in this chat. If you
   need multiple evidence files, return a ZIP containing that Markdown and evidence.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```

**Ready to dispatch**
