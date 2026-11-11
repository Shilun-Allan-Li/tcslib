# Dispatch · Gate 11

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/117c5882ef91b87cc2489992cea90cdca5661833/outbox/gates/11-levin-gate)
is staged on the exchange. Seyoon dispatches.

## Prompt for Codex

```text
You are an external Codex auditor for Pass–shelat Gate 11 in
https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at 117c5882ef91b87cc2489992cea90cdca5661833.
   Read outbox/gates/11-levin-gate/README.md, pack.md and bundle.md.
   Verify the pack using SHA256SUMS.
2. Audit draft PR #286 at Lean head a1293a6970b4039a9cf19fd475b9f8cf304a44b3
   and campaign records deb8885bab195b3cc3bdd14ea37687e99b459bdf using the pack.
   This audits the Levin padding proof (PadQuad.exists_linearTime_gStr), its
   supporting modules and the maintainer's rule-10 repair commit.
3. Return gate11-levin-findings.md as Markdown in this chat. If you need
   multiple evidence files, return a ZIP containing that Markdown and evidence.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```

**Ready to dispatch**
