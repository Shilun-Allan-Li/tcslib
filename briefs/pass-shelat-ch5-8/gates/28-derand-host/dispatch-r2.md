# Dispatch · Gate 28 round 2

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/4bf496ccd5ffa48f70704251cd0310d8aa13a2fe/outbox/gates/28-derand-host-gate-r2)
is staged on the exchange. Seyoon dispatches.

## Prompt for Codex

```text
You are an external Codex auditor for Pass–shelat Gate 28, round 2, in
https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at 4bf496ccd5ffa48f70704251cd0310d8aa13a2fe.
   Read outbox/gates/28-derand-host-gate-r2/README.md, pack-r2.md and bundle.md.
   Verify the pack using SHA256SUMS. The round-1 pack is
   outbox/gates/28-derand-host-gate/ at exchange
   2776272b61fcc7a1adf3f743c735c7e45be5045c.
2. Re-audit draft PR #312 at Lean head 0c04d1eb1e5450372632a23f3e94f3b7bfc37606,
   with campaign records 50416ccc67b9a28fea74177c2cb2ecf562cc6b29, using the pack.
   Round 1 was HOLD (G28-01 major: H17 not registered; G28-02 major: no
   head-envelope clause; G28-03 minor: consumer test wording; N28-01 note:
   proof owner). Check the H17 registry row against the code; the new
   machine-level contract exists_seedMajorityTM (correctness, time and a
   Clean.envelope-form head envelope on one machine, derived from the time
   bound, no admitted space spec: its truth, its sufficiency for Theorem
   180.1 through the corollary, Rule 10); the corollary seedMajority_mem_DTIME,
   now admitted until mem_DTIME_iff; G28-03 and N28-01; and the two round-2
   evidence builds. The base has moved (#311 merged, disjoint); say whether
   anything is new since round 1, and whether each round-1 finding is closed.
3. Return gate28-derand-host-r2-findings.md as Markdown in this chat. If you
   need multiple evidence files, return a ZIP containing that Markdown and evidence.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```

**Ready to dispatch**
