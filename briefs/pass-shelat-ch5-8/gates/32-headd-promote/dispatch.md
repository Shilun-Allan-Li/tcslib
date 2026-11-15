# Dispatch · Gate 32

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/22df0b71465fd1148fdd94dc4751a43d41614162/outbox/gates/32-headd-promote-gate)
is staged on the exchange (local commit, for the maintainer to verify and push). Seyoon dispatches.

## Prompt for Codex

```text
You are an external Codex auditor for Pass–shelat Gate 32 in
https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at 22df0b71465fd1148fdd94dc4751a43d41614162.
   Read outbox/gates/32-headd-promote-gate/README.md, pack.md and bundle.md.
   Verify the pack using SHA256SUMS.
2. Audit draft PR #316 at Lean head c18afbe66101381eed1617801d942dcf691506ea,
   with campaign records 3433097294600c7cd1ce30f5a5cc005c4ff0e4a4, using the pack.
   This is a promotion audit under ruling G29-02 (Gate 29): the placement
   of TCSlib.Cryptography.headD_drop_ofFn in Foundations/BitLists, upstream
   of both consumers (no import cycle, no undisclosed import), the
   proof-only re-derivation of LamportFill.headD_drop_ofFn with its header
   byte-identical, further copies of the fact beyond those ruled as DL-47
   debt (headD, List.ofFn, drop and getD readers), the Rule-10 seals and
   controls, the docstring and sketch rules, and the downstream effects
   (the #313 re-point of firstBit_of_pos, #315), under the rulings and
   dispositions in the pack. The integration rebuild of the downstream of
   BitLists and MachineSpec on the merged tip (#314 merged first) is a
   pending merge condition the maintainer runs, not an audit item.
3. Return gate32-headd-promote-findings.md as Markdown in this chat. If you
   need multiple evidence files, return a ZIP containing that Markdown and evidence.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```

The records (pin `34330972`, then this dispatch commit) and the exchange commit `22df0b71` must be pushed first.

**Ready to dispatch**
