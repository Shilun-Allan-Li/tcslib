# Dispatch · Gate 31

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/37f16e2b7222d0723c17ed1e1666a290f707b0e6/outbox/gates/31-prf-long-gate)
is staged on the exchange (local commit, for the maintainer to verify and push). Seyoon dispatches.

## Prompt for Codex

```text
You are an external Codex auditor for Pass–shelat Gate 31 in
https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at 37f16e2b7222d0723c17ed1e1666a290f707b0e6.
   Read outbox/gates/31-prf-long-gate/README.md, pack.md and bundle.md.
   Verify the pack using SHA256SUMS.
2. Audit draft PR #315 at Lean head fbd37f447596d4207c8d08b7ef7602f57fe95198,
   with campaign records 9cc4db6204a9965da907471603993e9c24d105d2, using the pack.
   This is a machinery audit of prf-long (ruling B3: the PRF machinery of
   PS10 Theorem 99.2 at l(n)-bit outputs, D1-D4; no admitted target):
   frozen-statement integrity with proof-only re-derivations, D1-D4 against
   the drafted signatures, the B1 consumer map against the merged
   SpecialEncryptionMulti and Gate 27's hand-off, undisclosed duplication
   beyond DL-46, the Rule-10 seals and controls (variant A canonical, the
   seal-B attribution), the LE-doc and LE-ws landing edits, and the
   interaction with the merged #314 and the open #313, under the rulings
   and dispositions in the pack. The integration rebuild of #314's
   downstream on the merged tip is a pending merge condition the
   maintainer runs, not an audit item.
3. Return gate31-prf-long-findings.md as Markdown in this chat. If you
   need multiple evidence files, return a ZIP containing that Markdown and evidence.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```

**Ready to dispatch**
