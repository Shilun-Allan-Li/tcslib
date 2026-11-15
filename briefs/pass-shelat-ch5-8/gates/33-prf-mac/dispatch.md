# Dispatch · Gate 33

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/2c666ab85b578479872a07622a60ff2e0ad6cfdf/outbox/gates/33-prf-mac-gate)
is staged on the exchange (local commit, for the maintainer to verify and push). Seyoon dispatches.

## Prompt for Codex

```text
You are an external Codex auditor for Pass–shelat Gate 33 in
https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at 2c666ab85b578479872a07622a60ff2e0ad6cfdf.
   Read outbox/gates/33-prf-mac-gate/README.md, pack.md and bundle.md.
   Verify the pack using SHA256SUMS.
2. Audit draft PR #317 at Lean head 590d1a56a350d9e8e75ee33d31e0501182169f67,
   with campaign records 76ff988bc26c66298a42b06a0abce1cf6cca7e34, using the pack.
   This is a proof audit of prf-mac (Authentication.prfMAC_secure, PS10
   Theorem 135.4): correctness against the frozen statement, including the
   bound Pr[forge] <= prfAdv(F_n, D^{q*1+1}) + 2^-n at every n and its edge
   cases; frozen-statement integrity (38 ADDED, 0 CHANGED, 0 REMOVED, every
   header byte-identical); undisclosed duplication beyond DL-44 (F-01 fixed
   by LE-reuse onto the merged prfAdv_eq_expect, F-02 and F-03 ruled errata
   with ledger debt); the Rule-10 seals and controls (variant A canonical);
   the landing edits LE-doc (docstrings only) and LE-reuse (proof only); and
   the docstring and sketch rules, under the rulings and dispositions in the
   pack. The integration rebuild on the merged tip with #315 and #316,
   whichever merges second, is a pending merge condition the maintainer
   runs, not an audit item.
3. Return gate33-prf-mac-findings.md as Markdown in this chat. If you
   need multiple evidence files, return a ZIP containing that Markdown and evidence.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```

The records (pin `76ff988b`, then this dispatch commit) and the exchange commit `2c666ab8` (on the Gate 32 exchange
commit `22df0b71`) must be pushed first.

**Ready to dispatch**
